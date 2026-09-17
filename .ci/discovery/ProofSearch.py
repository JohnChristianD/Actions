from __future__ import annotations

import argparse
import subprocess
from pathlib import Path

import jax.numpy as jnp
from puxle.core.puzzle_base import Puzzle
from xtructure import FieldDescriptor, xtructure_dataclass

from JAxtar.stars.astar import astar_builder
from heuristic.heuristic_base import Heuristic


@xtructure_dataclass(bitpack="off")
class ProofMaskState:
    mask: FieldDescriptor.scalar(dtype=jnp.int32)


class ProofMaskPuzzle(Puzzle):
    def define_state_class(self):
        return ProofMaskState

    def __init__(self, requirements, bits, start_mask, goal_mask):
        self.action_size = len(bits)
        self.requirements = jnp.asarray(requirements, dtype=jnp.int32)
        self.bits = jnp.asarray(bits, dtype=jnp.int32)
        self.start_mask = int(start_mask)
        self.goal_mask = int(goal_mask)
        super().__init__()

    def get_initial_state(self, solve_config, key=None, data=None):
        return ProofMaskState(mask=self.start_mask)

    def get_solve_config(self, key=None, data=None):
        return self.SolveConfig(
            InstanceContext=self.InstanceContext(),
            GoalSpec=ProofMaskState(mask=self.goal_mask),
        )

    def get_actions(self, solve_config, state, action, filled=True):
        required = self.requirements[action]
        bit = self.bits[action]
        ready = jnp.equal(jnp.bitwise_and(state.mask, required), required)
        fresh = jnp.equal(jnp.bitwise_and(state.mask, bit), 0)
        valid = jnp.logical_and(jnp.logical_and(ready, fresh), filled)
        next_mask = jnp.where(valid, jnp.bitwise_or(state.mask, bit), state.mask)
        cost = jnp.where(valid, 1.0, jnp.inf)
        return ProofMaskState(mask=next_mask), cost

    def get_string_parser(self):
        return lambda state, **kwargs: str(int(state.mask))

    def get_img_parser(self):
        return lambda state, **kwargs: jnp.zeros((4, 4, 3), dtype=jnp.float32)


class ProofMaskHeuristic(Heuristic):
    def __init__(self, puzzle, distances):
        super().__init__(puzzle)
        self.distances = jnp.asarray(distances, dtype=jnp.float32)

    def distance(self, heuristic_parameters, current):
        return self.distances[current.mask]


def build_distances(requirements, bits, goal_mask):
    size = goal_mask + 1
    distances = [10**9] * size
    distances[goal_mask] = 0
    for mask in range(goal_mask - 1, -1, -1):
        best = 10**9
        for required, bit in zip(requirements, bits):
            if (mask & required) == required and (mask & bit) == 0:
                next_mask = mask | bit
                best = min(best, 1 + distances[next_mask])
        distances[mask] = best
    if distances[0] >= 10**9:
        raise RuntimeError("proof graph has no completion")
    return distances


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--budget", type=int, default=64)
    args = parser.parse_args()

    names = (
        "exact learner composition",
        "L1/path accumulation",
        "F4 L2 field preservation",
        "GRU persistent-field invariant",
        "path-norm bound certificate",
        "KKT certificate",
        "contraction certificate",
        "Lyapunov certificate",
        "attractor/basin certificate",
        "quotient injectivity certificate",
        "left-inverse certificate",
        "discrete separation certificate",
        "reservoir-condition bridge",
        "full coupled composition",
    )

    requirements = (
        0,
        1,
        1,
        1,
        2,
        2,
        (1 << 4) | (1 << 5),
        (1 << 3) | (1 << 6),
        1 << 7,
        1 << 3,
        1 << 9,
        1 << 10,
        1 << 11,
        (1 << 2) | (1 << 5) | (1 << 8) | (1 << 12),
    )
    bits = tuple(1 << i for i in range(len(names)))
    proven_start = bits[0] | bits[1] | bits[2] | bits[3]
    goal_mask = sum(bits)
    distances = build_distances(requirements, bits, goal_mask)

    puzzle = ProofMaskPuzzle(requirements, bits, proven_start, goal_mask)
    heuristic = ProofMaskHeuristic(puzzle, distances)
    search = astar_builder(
        puzzle,
        heuristic,
        batch_size=32,
        max_nodes=max(64, args.budget * 32),
    )
    solve_config = puzzle.get_solve_config()
    result = search(solve_config, puzzle.get_initial_state(solve_config))
    trace = result.to_solution_trace(puzzle=puzzle)
    if not trace.solved:
        raise SystemExit("JAxtar A* did not complete the coupled theorem graph")

    plan = [names[action] for action in trace.actions]
    print("JAxtar A* proof-plan:")
    for index, item in enumerate(plan, 1):
        print(f"{index:02d}. {item}")

    external = [
        item
        for item in plan
        if item in {
            "path-norm bound certificate",
            "KKT certificate",
            "contraction certificate",
            "Lyapunov certificate",
            "attractor/basin certificate",
            "quotient injectivity certificate",
            "left-inverse certificate",
            "discrete separation certificate",
            "reservoir-condition bridge",
        }
    ]
    print("Explicit certificate slots:")
    for item in external:
        print(f"- {item}")

    root = Path(__file__).resolve().parents[2]
    target = root / "Exotic/ERL/FullCoupled/MonolithCompositeReservoirTheorem.agda"
    subprocess.run(["agda", "--safe", str(target)], check=True, cwd=root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
