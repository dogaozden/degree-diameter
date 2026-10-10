"""Parent selection. Deterministic for a given random.Random."""
from __future__ import annotations

import random

from evolve.store import CandidateRecord
from evolve.types import Case


def fitness(case_scores: dict[str, float], cases: list[Case]) -> float:
    total = sum(c.weight for c in cases)
    return sum(c.weight * case_scores.get(c.id, 0.0) for c in cases) / total


def parent_pool(cands: list[CandidateRecord], cases: list[Case], elite_k: int) -> list[str]:
    live = [c for c in cands if c.fitness is not None and c.fitness > 0]
    elites = sorted(live, key=lambda c: (-c.fitness, c.generation, c.id))[:elite_k]
    pool = [c.id for c in elites]
    for case in cases:
        with_value = [c for c in live if c.case_values.get(case.id, 0.0) > 0]
        if not with_value:
            continue
        best = min(with_value, key=lambda c: (-c.case_values[case.id], -c.fitness, c.generation, c.id))
        if best.id not in pool:
            pool.append(best.id)
    return pool


def pick_roles(n: int, weights: dict[str, float], rng: random.Random) -> list[str]:
    keys = sorted(weights)
    return rng.choices(keys, weights=[weights[k] for k in keys], k=n)


def pick_parents(pool: list[str], role: str, rng: random.Random) -> list[str]:
    if role == "crossover" and len(pool) >= 2:
        return rng.sample(pool, 2)
    return [rng.choice(pool)]
