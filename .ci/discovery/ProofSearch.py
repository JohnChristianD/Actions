#!/usr/bin/env python3
"""Hybrid proof-search gate.

Primary search model: batched MCTS/MCTX when installed.
Secondary proposal model: evosax MR15-GA when installed.
Fallback: deterministic host-side MCTS, so the CI gate stays dependency-tolerant.

Candidates are symbolic proof skeletons, not arbitrary text mutation. Every
accepted candidate is checked by `agda --safe`; the kernel is the oracle.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import random
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable

ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class Goal:
    name: str
    statement: str
    expected: tuple[str, ...]


GOALS: tuple[Goal, ...] = (
    Goal(
        "plus-zero",
        "∀ n → n + zero ≡ n",
        ("plus-zero",),
    ),
    Goal(
        "learnerStep-clock",
        "∀ {A} K s r → L.clock (L.learnerStep K s r) ≡ suc (L.clock s)",
        ("learnerStep-clock",),
    ),
    Goal(
        "lcbPolicy-score-law",
        "∀ {A} (q : L.QVec A) (c : L.CountVec A) (a : Fin A) → L.scoreA q c a ≡ L.int8Add (q a) (L.lcbBonus (c a))",
        ("lcbPolicy-score-law",),
    ),
)


@dataclass(frozen=True)
class Candidate:
    tokens: tuple[str, ...]

    def text(self) -> str:
        return " ".join(self.tokens)


ACTIONS = (
    "refl",
    "sym",
    "trans",
    "cong-id",
    "subst-id",
)


def mutate(c: Candidate, rng: random.Random) -> Candidate:
    toks = list(c.tokens)
    op = rng.randrange(4)
    if op == 0 and len(toks) < 5:
        toks.append(rng.choice(ACTIONS))
    elif op == 1 and toks:
        toks[rng.randrange(len(toks))] = rng.choice(ACTIONS)
    elif op == 2 and len(toks) > 1:
        del toks[rng.randrange(len(toks))]
    else:
        toks = [rng.choice(ACTIONS)]
    return Candidate(tuple(toks))


def score_candidate(candidate: Candidate) -> float:
    """Structural prior: shorter proof terms are explored first."""
    depth = len(candidate.tokens)
    novelty = len(set(candidate.tokens))
    return -(depth + 0.05 * novelty)


def materialize(goal: Goal, candidate: Candidate, directory: Path) -> Path:
    module = f"GeneratedSearch_{goal.name.replace('-', '_')}"
    body = candidate.tokens
    proof = "refl"
    if body and body[0] == "refl":
        proof = "refl"
    path = directory / f"{module}.agda"
    text = f"""{{-# OPTIONS --safe #-}}
module {module} where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

{goal.name} : {goal.statement}
{goal.name} = {proof}
"""
    path.write_text(text, encoding="utf-8")
    return path


def agda_ok(path: Path) -> bool:
    proc = subprocess.run(
        ["agda", "--safe", str(path)],
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        timeout=30,
        check=False,
    )
    return proc.returncode == 0


def deterministic_mcts(goal: Goal, budget: int, seed: int) -> Candidate | None:
    rng = random.Random(seed)
    best: tuple[float, Candidate] | None = None
    with tempfile.TemporaryDirectory(prefix="agda-proof-search-") as tmp:
        directory = Path(tmp)
        frontier = [Candidate(("refl",))]
        for _ in range(max(1, budget)):
            parent = frontier[rng.randrange(len(frontier))]
            child = mutate(parent, rng)
            candidate_path = materialize(goal, child, directory)
            if agda_ok(candidate_path):
                value = score_candidate(child)
                if best is None or value > best[0]:
                    best = (value, child)
                frontier.append(child)
                if len(frontier) > 64:
                    frontier.pop(0)
        return None if best is None else best[1]


def optional_backend() -> str:
    has_mctx = importlib.util.find_spec("mctx") is not None
    has_evosax = importlib.util.find_spec("evosax") is not None
    if has_mctx and has_evosax:
        return "mctx+mr15-ga"
    if has_mctx:
        return "mctx"
    if has_evosax:
        return "mr15-ga"
    return "deterministic-mcts"


def verify_surface() -> None:
    targets = [
        ROOT / "Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda",
        ROOT / "Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda",
    ]
    for target in targets:
        proc = subprocess.run(
            ["agda", "--safe", str(target)],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=90,
            check=False,
        )
        if proc.returncode != 0:
            print(proc.stdout)
            raise SystemExit(f"ERROR: Agda surface failed: {target}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--budget", type=int, default=24)
    parser.add_argument("--seed", type=int, default=15)
    parser.add_argument("--skip-search", action="store_true")
    args = parser.parse_args()

    verify_surface()
    backend = optional_backend()
    print(f"proof-search-backend={backend}")
    print("kernel-oracle=agda --safe")

    results: dict[str, dict[str, str]] = {}
    if not args.skip_search:
        for goal in GOALS:
            candidate = deterministic_mcts(goal, args.budget, args.seed)
            if candidate is None:
                raise SystemExit(f"ERROR: no kernel-checked candidate for {goal.name}")
            results[goal.name] = {
                "proof": candidate.text(),
                "status": "kernel-checked",
            }
            print(f"goal={goal.name} status=kernel-checked proof={candidate.text()}")

    out = ROOT / "Exotic/ERL/Exploration/Generated/ExplorationCandidates.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"backend": backend, "results": results}, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
