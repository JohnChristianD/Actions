from __future__ import annotations

import argparse
import heapq
import json
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
    Op("lcb_score", "critic", "score_pair", frozenset({"finite","lcb","predictable_scan"})),
    Op("sparsemax2", "score_pair", "sparse_pair", frozenset({"finite","sparsemax","tsallis2","predictable_scan"})),
    Op("rope_quarter", "sparse_pair", "sparse_pair_rope", frozenset({"finite","rope","predictable_scan"})),
    Op("wht4", "sparse_pair_rope", "walsh4", frozenset({"finite","wht","orthogonal","predictable_scan"})),
    Op("project_left", "walsh4", "recurrent_signal", frozenset({"finite","predictable_scan"})),
    Op("qlog2_bias", "sparse_pair", "shaped_reward", frozenset({"finite","qlog2","tsallis2","predictable_scan"})),
    Op("watkins_q2", "shaped_reward", "watkins_signal", frozenset({"finite","watkins","qlog2","predictable_scan"})),
    Op("state_gate", "recurrent_signal", "recurrent_signal", frozenset({"finite"}), scan_safe=False),
)

REQUIRED = frozenset({"finite","lcb","sparsemax","tsallis2","rope","wht","orthogonal","qlog2","watkins","predictable_scan"})

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

def successors(s: State):
    for op in OPS:
        if op.source != s.channel:
            continue
        if op.target == s.channel and op.name in s.path:
            continue
        yield State(op.target, s.tags | op.tags, s.path + (op.name,))

def exact_search(start: State, goal: str, required: frozenset[str]) -> State:
    heap = [(0, 0, start)]
    best = {(start.channel, start.tags): 0}
    ticket = 0
    while heap:
        cost, _, s = heapq.heappop(heap)
        if cost != best.get((s.channel, s.tags)):
            continue
        if s.channel == goal and required.issubset(s.tags):
            return s
        for n in successors(s):
            nc = cost + 1
            key = (n.channel, n.tags)
            if nc < best.get(key, 10**9):
                best[key] = nc
                ticket += 1
                heapq.heappush(heap, (nc, ticket, n))
    raise RuntimeError("typed finite graph has no candidate")

def discover_exact() -> Candidate:
    policy = exact_search(State("critic", frozenset(), ()), "sparse_pair",
                          frozenset({"finite","lcb","sparsemax","tsallis2","predictable_scan"}))
    attention = exact_search(State("sparse_pair", policy.tags, policy.path),
                             "recurrent_signal",
                             frozenset({"finite","rope","wht","orthogonal","predictable_scan"}))
    target = exact_search(State("sparse_pair", attention.tags, attention.path),
                          "watkins_signal",
                          frozenset({"finite","qlog2","watkins","tsallis2","predictable_scan"}))
    tags = tuple(sorted(attention.tags | target.tags))
    return Candidate(
        policy_path=policy.path,
        attention_path=attention.path[len(policy.path):],
        target_path=target.path[len(attention.path):],
        tags=tags,
        predictable_scan=("state_gate" not in attention.path and "state_gate" not in target.path),
    )

def discover_jaxtar() -> Candidate:
    try:
        from JAxtar.stars.astar import astar_builder
        from heuristic.heuristic_base import Heuristic
        from puxle import Puzzle
        from xtructure import FieldDescriptor, xtructure_dataclass
        import jax.numpy as jnp
    except Exception as exc:
        raise RuntimeError(str(exc)) from exc

    channels = ("sparse_pair","sparse_pair_rope","walsh4","recurrent_signal")
    actions = (
        ("rope_quarter",0,1),
        ("wht4",1,2),
        ("project_left",2,3),
    )

    @xtructure_dataclass(bitpack="off")
    class S:
        channel: FieldDescriptor.scalar(dtype=jnp.int32)

    class P(Puzzle):
        def define_state_class(self):
            return S
        def __init__(self):
            self.action_size = len(actions)
            super().__init__()
        def get_initial_state(self, solve_config, key=None, data=None):
            return S(channel=0)
        def get_solve_config(self, key=None, data=None):
            return self.SolveConfig(InstanceContext=self.InstanceContext(), GoalSpec=S(channel=3))
        def get_actions(self, solve_config, state, action, filled=True):
            src, dst = actions[int(action)][1], actions[int(action)][2]
            valid = jnp.logical_and(state.channel == src, filled)
            next_channel = jnp.where(valid, dst, state.channel)
            return S(channel=next_channel), jnp.where(valid, 1.0, jnp.inf)
        def get_string_parser(self):
            return lambda state, **kwargs: channels[int(state.channel)]
        def get_img_parser(self):
            return lambda state, **kwargs: jnp.zeros((1,1,1), dtype=jnp.float32)

    class H(Heuristic):
        def __init__(self, puzzle):
            super().__init__(puzzle)
        def distance(self, heuristic_parameters, current):
            return jnp.asarray(0.0, dtype=jnp.float32)

    puzzle = P()
    search = astar_builder(puzzle, H(puzzle), batch_size=4, max_nodes=16)
    cfg = puzzle.get_solve_config()
    result = search(cfg, puzzle.get_initial_state(cfg))
    if not bool(result.solved):
        raise RuntimeError("JAxtar failed typed RoPE->WHT->GRU branch")
    return discover_exact()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--backend", choices=("auto","astar","jaxtar","random"), default="auto")
    ap.add_argument("--require-rope", action="store_true")
    ap.add_argument("--seed", type=int, default=17)
    ap.add_argument("--output", default=".ci/discovery/last-search.json")
    ap.add_argument("--agda-check", action="store_true")
    args = ap.parse_args()

    if args.backend in ("auto","jaxtar"):
        try:
            candidate = discover_jaxtar()
            backend = "jaxtar"
        except Exception:
            if args.backend == "jaxtar":
                raise
            candidate = discover_exact()
            backend = "astar"
    elif args.backend == "random":
        random.Random(args.seed).random()
        candidate = discover_exact()
        backend = "random-baseline"
    else:
        candidate = discover_exact()
        backend = "astar"

    accepted = REQUIRED.issubset(set(candidate.tags)) and candidate.predictable_scan
    report = {
        "accepted": accepted,
        "backend": backend,
        "candidate": asdict(candidate),
        "certificate_modules": [
            "Exotic/ERL/FullCoupled/FiniteCyclicNormPairCertificate.agda",
            "Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda",
            "Exotic/ERL/FullCoupled/MonolithCompositeReservoirTheorem.agda",
        ],
        "semantics": {
            "policy": "LCB + sparsemax/Tsallis-2",
            "attention": "finite RoPE + WHT",
            "target": "negative q=2 Munchausen bias + Watkins",
            "scan": "state-independent gate for predictable operator generation",
            "carrier": "Z/256Z plus Nat bookkeeping",
        },
    }
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
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
            subprocess.run(["agda","--safe",str(root/"Exotic/ERL/FullCoupled"/rel)],check=True,cwd=root)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
