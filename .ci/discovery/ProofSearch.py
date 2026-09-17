#!/usr/bin/env python3
"""Kernel-checked hybrid proof-search harness.

Search stack:
  1. MCTX, when installed, proposes short symbolic action sequences.
  2. evosax MR15-GA, when installed, performs non-local population mutations.
  3. bounded best-first search remains available as a deterministic fallback.
  4. Agda --safe is the acceptance oracle. No candidate is accepted on score alone.

This is deliberately grammar-driven. The grammar is the algebraic interface
where future symbolic-program-search methods attach.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import subprocess
import tempfile
from dataclasses import dataclass
from heapq import heappop, heappush
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class Candidate:
    actions: tuple[str, ...]


@dataclass(frozen=True)
class Goal:
    name: str
    statement: str
    proof_macros: dict[str, str]


GOALS: tuple[Goal, ...] = (
    Goal(
        "clock-lower-bound-search",
        "∀ {A} (K : L.LearnerKernel A) n s r → L.clock s ≤ L.clock (L.iterateLearner K n s r)",
        {
            "clock-lower-bound": "T.clock-lower-bound K n s r",
        },
    ),
    Goal(
        "score-sort-permutation-search",
        "∀ {A} (q : L.QVec A) (c : L.CountVec A) → Sort.sort (L.scoreEntryOrder A) (L.scoreList q c) ↭ L.scoreList q c",
        {
            "sort-permutation": "T.scoreList-sort-permutation q c",
        },
    ),
    Goal(
        "score-sort-sorted-search",
        "∀ {A} (q : L.QVec A) (c : L.CountVec A) → Sorted (Sort.sort (L.scoreEntryOrder A) (L.scoreList q c))",
        {
            "sort-sorted": "T.scoreList-sort-sorted q c",
        },
    ),
)


def candidate_text(goal: Goal, candidate: Candidate) -> str | None:
    if len(candidate.actions) != 1:
        return None
    return goal.proof_macros.get(candidate.actions[0])


def write_candidate(goal: Goal, candidate: Candidate, directory: Path) -> Path | None:
    proof = candidate_text(goal, candidate)
    if proof is None:
        return None
    module = f"GeneratedSearch_{goal.name.replace('-', '_') }"
    path = directory / f"{module}.agda"
    path.write_text(
        f"""{{-# OPTIONS --safe #-}}
module {module} where

open import Data.Fin using (Fin)
open import Data.List.Sort as Sort
open import Data.List.Relation.Unary.Sorted.TotalOrder using (Sorted)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T
open Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

{goal.name} : {goal.statement}
{goal.name} = {proof}
""",
        encoding="utf-8",
    )
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


def verify_surfaces() -> None:
    for relative in (
        "Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda",
        "Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda",
    ):
        path = ROOT / relative
        proc = subprocess.run(
            ["agda", "--safe", str(path)],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=90,
            check=False,
        )
        if proc.returncode != 0:
            print(proc.stdout)
            raise SystemExit(f"ERROR: kernel surface failed: {relative}")


def best_first(goal: Goal, budget: int) -> Candidate | None:
    """Bounded A*-style proof-grammar search."""
    queue: list[tuple[float, int, Candidate]] = []
    counter = 0
    heappush(queue, (0.0, counter, Candidate(())))
    seen: set[tuple[str, ...]] = set()
    expansions = 0
    actions = tuple(goal.proof_macros)
    with tempfile.TemporaryDirectory(prefix="agda-proof-search-") as tmp:
        directory = Path(tmp)
        while queue and expansions < budget:
            _, _, candidate = heappop(queue)
            if candidate.actions in seen:
                continue
            seen.add(candidate.actions)
            expansions += 1
            path = write_candidate(goal, candidate, directory)
            if path is not None and agda_ok(path):
                return candidate
            if len(candidate.actions) < 1:
                for action in actions:
                    child = Candidate(candidate.actions + (action,))
                    counter += 1
                    heappush(queue, (float(len(child.actions)), counter, child))
    return None


def mctx_available() -> bool:
    return importlib.util.find_spec("mctx") is not None and importlib.util.find_spec("jax") is not None


def evosax_available() -> bool:
    return importlib.util.find_spec("evosax") is not None and importlib.util.find_spec("jax") is not None


def mctx_probe(goal: Goal, simulations: int) -> Candidate | None:
    """Use MCTX to rank a finite symbolic grammar, then kernel-check the proposal."""
    import jax
    import jax.numpy as jnp
    import mctx

    actions = tuple(goal.proof_macros)
    num_actions = len(actions)
    root = mctx.RootFnOutput(
        prior_logits=jnp.zeros((1, num_actions)),
        value=jnp.zeros((1,)),
        embedding=jnp.zeros((1, 1), dtype=jnp.int32),
    )

    def recurrent_fn(params, rng_key, action, embedding):
        new_embedding = embedding + 1
        reward = jnp.zeros_like(embedding[:, 0], dtype=jnp.float32)
        value = -new_embedding[:, 0].astype(jnp.float32)
        prior = jnp.zeros((embedding.shape[0], num_actions), dtype=jnp.float32)
        return (
            mctx.RecurrentFnOutput(
                reward=reward,
                discount=jnp.ones_like(reward),
                prior_logits=prior,
                value=value,
            ),
            new_embedding,
        )

    policy = mctx.muzero_policy(
        params=(),
        rng_key=jax.random.key(15),
        root=root,
        recurrent_fn=recurrent_fn,
        num_simulations=simulations,
        dirichlet_fraction=0.0,
        temperature=1.0,
    )
    order = jnp.argsort(-policy.action_weights[0])
    with tempfile.TemporaryDirectory(prefix="agda-mctx-") as tmp:
        directory = Path(tmp)
        for index in order.tolist():
            candidate = Candidate((actions[int(index)],))
            path = write_candidate(goal, candidate, directory)
            if path is not None and agda_ok(path):
                return candidate
    return None


def evosax_probe(goal: Goal, population_size: int) -> Candidate | None:
    """MR15-GA population stage over the finite grammar's action index."""
    import jax
    import jax.numpy as jnp
    from evosax.algorithms import MR15_GA

    actions = tuple(goal.proof_macros)
    if not actions:
        return None
    solution = jnp.zeros((1,), dtype=jnp.float32)
    ga = MR15_GA(population_size=population_size, solution=solution)
    params = ga.default_params
    key = jax.random.key(15)
    state = ga.init(key, solution, jnp.array(0.0), params)
    with tempfile.TemporaryDirectory(prefix="agda-ga-") as tmp:
        directory = Path(tmp)
        for _ in range(4):
            key, ask_key, tell_key = jax.random.split(key, 3)
            population, state = ga.ask(ask_key, state, params)
            indices = jnp.clip(jnp.rint(population[:, 0]), 0, len(actions) - 1).astype(jnp.int32)
            fitness = jnp.zeros((population.shape[0],), dtype=jnp.float32)
            for i, index in enumerate(indices.tolist()):
                candidate = Candidate((actions[int(index)],))
                path = write_candidate(goal, candidate, directory)
                if path is not None and agda_ok(path):
                    return candidate
                fitness = fitness.at[i].set(float(index))
            state, _ = ga.tell(tell_key, population, fitness, state, params)
    return None


def search_goal(goal: Goal, budget: int, backend: str) -> Candidate | None:
    if backend in {"auto", "mctx"} and mctx_available():
        candidate = mctx_probe(goal, min(budget, 64))
        if candidate is not None:
            return candidate
    if backend in {"auto", "mr15-ga"} and evosax_available():
        candidate = evosax_probe(goal, min(32, budget))
        if candidate is not None:
            return candidate
    return best_first(goal, budget)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--budget", type=int, default=24)
    parser.add_argument("--backend", choices=("auto", "mctx", "mr15-ga", "astar"), default="auto")
    args = parser.parse_args()

    verify_surfaces()
    results: dict[str, dict[str, str]] = {}
    for goal in GOALS:
        candidate = search_goal(goal, args.budget, args.backend)
        if candidate is None:
            raise SystemExit(f"ERROR: no kernel-checked proof candidate for {goal.name}")
        results[goal.name] = {"proof": candidate.actions[0], "status": "kernel-checked"}
        print(f"goal={goal.name} backend={args.backend} status=kernel-checked proof={candidate.actions[0]}")

    output = ROOT / "Exotic/ERL/Exploration/Generated/ExplorationCandidates.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print("kernel-oracle=agda --safe")


if __name__ == "__main__":
    main()
