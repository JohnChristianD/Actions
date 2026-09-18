from __future__ import annotations

"""Typed finite symbolic discovery.

The program graph is deliberately small and proof-aware.  Operators expose
their finite carrier, sparsemax/Tsallis-2, LCB, finite RoPE, WHT, q=2
Munchausen/Watkins, and predictable-scan properties as explicit tags.

JAxtar is an optional A* controller.  The local exact A* remains the
acceptance baseline, so a search library never substitutes for Agda proof.
"""

import argparse
import heapq
import json
import math
import random
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass(frozen=True)
class Op:
    name: str
    source: str
    target: str
    tags: frozenset[str]
    cost: int = 1
    scan_safe: bool = True


OPS = (
    Op("lcb_score", "critic", "score_pair",
       frozenset({"finite", "lcb", "predictable_scan"})),
    Op("sparsemax2", "score_pair", "sparse_pair",
       frozenset({"finite", "sparsemax", "tsallis2", "predictable_scan"})),
    Op("rope_quarter", "sparse_pair", "sparse_pair_rope",
       frozenset({"finite", "rope", "predictable_scan"})),
    Op("wht4", "sparse_pair_rope", "walsh4",
       frozenset({"finite", "wht", "orthogonal", "predictable_scan"})),
    Op("project_left", "walsh4", "recurrent_signal",
       frozenset({"finite", "predictable_scan"})),
    Op("qlog2_bias", "sparse_pair", "shaped_reward",
       frozenset({"finite", "qlog2", "tsallis2", "predictable_scan"})),
    Op("watkins_q2", "shaped_reward", "watkins_signal",
       frozenset({"finite", "watkins", "qlog2", "predictable_scan"})),
    Op("state_gate", "recurrent_signal", "recurrent_signal",
       frozenset({"finite"}), scan_safe=False),
)

REQUIRED_POLICY = {"finite", "lcb", "sparsemax", "tsallis2", "predictable_scan"}
REQUIRED_ATTENTION = {"finite", "wht", "orthogonal", "predictable_scan"}
REQUIRED_TARGET = {"finite", "qlog2", "watkins", "tsallis2", "predictable_scan"}


@dataclass(frozen=True)
class State:
    channel: str
    tags: frozenset[str]
    path: tuple[str, ...]


@dataclass(frozen=True)
class Candidate:
    policy_path: tuple[str, ...]
    attention_path: tuple[str, ...]
    target_path: tuple[str, ...]
    tags: tuple[str, ...]
    predictable_scan: bool
    state_gate_rejected: bool


def successors(s: State):
    for op in OPS:
        if op.source != s.channel:
            continue
        if op.target == s.channel and op.name in s.path:
            continue
        yield State(op.target, s.tags | op.tags, s.path + (op.name,))


def shortest(start: State, goal_channel: str, required: set[str]) -> State:
    heap = [(0, 0, start)]
    best: dict[tuple[str, frozenset[str]], int] = {
        (start.channel, start.tags): 0
    }
    tick = 0
    while heap:
        cost, _, s = heapq.heappop(heap)
        key = (s.channel, s.tags)
        if cost != best.get(key):
            continue
        if s.channel == goal_channel and required.issubset(s.tags):
            return s
        for n in successors(s):
            nc = cost + 1
            nk = (n.channel, n.tags)
            if nc < best.get(nk, math.inf):
                best[nk] = nc
                tick += 1
                heapq.heappush(heap, (nc, tick, n))
    raise RuntimeError(f"no candidate for {goal_channel}")


def finite_gain(table: list[int]) -> int:
    """Exact unary cyclic gain on the Z/256Z carrier."""
    result = 0
    for x in range(256):
        for y in range(256):
            d = min((x - y) % 256, (y - x) % 256)
            out = min((table[x] - table[y]) % 256, (table[y] - table[x]) % 256)
            if d == 0:
                if out:
                    return 256
            else:
                result = max(result, (out + d - 1) // d)
    return result


def rope_quarter(x: int, y: int) -> tuple[int, int]:
    return ((-y) % 256, x % 256)


def discover_exact(require_rope: bool) -> Candidate:
    policy = shortest(State("critic", frozenset(), ()),
                      "sparse_pair", REQUIRED_POLICY)

    attention = shortest(
        State("sparse_pair", policy.tags, policy.path),
        "recurrent_signal",
        REQUIRED_ATTENTION | ({"rope"} if require_rope else set()),
    )

    target = shortest(
        State("sparse_pair", attention.tags, attention.path),
        "watkins_signal",
        REQUIRED_TARGET,
    )

    tags = tuple(sorted(attention.tags | target.tags))
    rejected = "state_gate" not in attention.path
    return Candidate(
        policy_path=policy.path,
        attention_path=tuple(
            x for x in attention.path[len(policy.path):]
        ),
        target_path=tuple(
            x for x in target.path[len(attention.path):]
        ),
        tags=tags,
        predictable_scan=rejected and "predictable_scan" in tags,
        state_gate_rejected=rejected,
    )


def discover_random(seed: int, require_rope: bool) -> Candidate:
    rng = random.Random(seed)
    candidates = [discover_exact(require_rope)]
    rng.shuffle(candidates)
    return candidates[0]


def discover_jaxtar(require_rope: bool) -> Candidate:
    try:
        from JAxtar.stars.astar import astar_builder
        from heuristic.heuristic_base import Heuristic
        from puxle import Puzzle
        from xtructure import FieldDescriptor, xtructure_dataclass
        import jax.numpy as jnp
    except Exception as exc:
        raise RuntimeError(f"JAxtar unavailable: {exc}") from exc

    if not require_rope:
        # The accepted architecture in this search mode deliberately keeps
        # the finite RoPE branch explicit, so the accelerated controller is
        # only asked to certify that branch.
        raise RuntimeError("JAxtar backend requires --require-rope")

    channels = (
        "sparse_pair",
        "sparse_pair_rope",
        "walsh4",
        "recurrent_signal",
    )
    channel_index = {name: i for i, name in enumerate(channels)}
    branch_ops = tuple(
        op for op in OPS
        if op.name in {"rope_quarter", "wht4", "project_left"}
    )
    goal = channel_index["recurrent_signal"]

    @xtructure_dataclass(bitpack="off")
    class SearchState:
        channel: FieldDescriptor.scalar(dtype=jnp.int32)

    class BranchPuzzle(Puzzle):
        def define_state_class(self):
            return SearchState

        def __init__(self):
            self.action_size = len(branch_ops)
            super().__init__()

        def get_initial_state(self, solve_config, key=None, data=None):
            return SearchState(code=channel_index["sparse_pair"])

        def get_solve_config(self, key=None, data=None):
            return self.SolveConfig(
                InstanceContext=self.InstanceContext(),
                GoalSpec=SearchState(channel=goal),
            )

        def get_actions(self, solve_config, state, action, filled=True):
            current = int(state.channel)
            op = branch_ops[int(action)]
            source_ok = channel_index[op.source] == current
            valid = jnp.logical_and(jnp.asarray(source_ok), filled)
            next_channel = channel_index[op.target] if source_ok else current
            return SearchState(channel=next_channel), jnp.where(
                valid, 1.0, jnp.inf
            )

        def get_string_parser(self):
            return lambda state, **kwargs: channels[int(state.channel)]

        def get_img_parser(self):
            return lambda state, **kwargs: jnp.zeros((1, 1, 1), dtype=jnp.float32)

    class ZeroHeuristic(Heuristic):
        def __init__(self, puzzle):
            super().__init__(puzzle)

        def distance(self, heuristic_parameters, current):
            return jnp.zeros_like(current.channel, dtype=jnp.float32)

    puzzle = BranchPuzzle()
    search = astar_builder(
        puzzle,
        ZeroHeuristic(puzzle),
        batch_size=4,
        max_nodes=16,
    )
    solve_config = puzzle.get_solve_config()
    result = search(
        solve_config,
        puzzle.get_initial_state(solve_config),
    )
    if not bool(result.solved):
        raise RuntimeError("JAxtar did not solve the finite RoPE -> WHT -> GRU branch")

    # The exact typed graph remains the semantic acceptance oracle.
    return discover_exact(require_rope)


def certificate_slots():
    return [
        "sparsemax-support-nonempty",
        "generalPolicy-is-lcb-sparsemax",
        "canonicalRecurrentInput-law",
        "walshHadamardOrthogonality4",
        "canonicalWatkinsTarget-law",
        "learnerNormBudget-step-monotone",
        "fullLearnerState-no-left-inverse",
    ]


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--backend", choices=["auto", "jaxtar", "astar", "random"], default="auto")
    p.add_argument("--require-rope", action="store_true")
    p.add_argument("--seed", type=int, default=17)
    p.add_argument("--output", default=".ci/discovery/last-search.json")
    p.add_argument("--agda-check", action="store_true")
    args = p.parse_args()

    backend = args.backend
    if backend in {"auto", "jaxtar"}:
        try:
            candidate = discover_jaxtar(args.require_rope)
            backend = "jaxtar"
        except Exception as exc:
            if backend == "jaxtar":
                print(f"JAxtar backend failed: {exc}")
                return 2
            print(f"JAxtar auto-backend skipped: {exc}")
            candidate = discover_exact(args.require_rope)
            backend = "astar"
    elif backend == "random":
        candidate = discover_random(args.seed, args.require_rope)
    else:
        candidate = discover_exact(args.require_rope)

    required = REQUIRED_POLICY | REQUIRED_ATTENTION | REQUIRED_TARGET
    accepted = (
        required.issubset(set(candidate.tags))
        and (not args.require_rope or "rope" in candidate.tags)
        and candidate.predictable_scan
    )

    report = {
        "accepted": accepted,
        "backend": backend,
        "policy_path": candidate.policy_path,
        "attention_path": candidate.attention_path,
        "target_path": candidate.target_path,
        "tags": candidate.tags,
        "predictable_scan": candidate.predictable_scan,
        "state_gate_rejected": candidate.state_gate_rejected,
        "certificate_slots": certificate_slots(),
        "finite_carrier": "Z/256Z",
        "parameter_count_bound": "256^p = 2^(8p)",
        "norm_pair_module": "Exotic/ERL/FullCoupled/FiniteCyclicNormPairCertificate.agda",
        "policy_semantics": "LCB + sparsemax, Tsallis-q=2 aligned with q=2 Munchausen",
        "attention_semantics": "data-dependent sparsemax plus fixed WHT; finite quarter-turn RoPE is optional",
    }

    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\\n",
        encoding="utf-8",
    )
    print(json.dumps(report, indent=2, sort_keys=True))

    if not accepted:
        return 3

    if args.agda_check:
        root = Path(__file__).resolve().parents[2]
        for rel in (
            "GeneralFullCoupledLearnerMonolith.agda",
            "GeneralFullCoupledTheoremsMonolith.agda",
            "MonolithCompositeReservoirTheorem.agda",
            "FiniteCyclicNormPairCertificate.agda",
            "FunctionalWalshBridge.agda",
        ):
            subprocess.run(
                ["agda", "--safe", str(root / "Exotic/ERL/FullCoupled" / rel)],
                check=True,
                cwd=root,
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
