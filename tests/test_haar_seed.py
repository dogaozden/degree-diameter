"""The Haar seed core (seeds/haar/core.py): group tables, cost, batch costs, and agreement with the real checker."""
import importlib.util
import sys
import time
from pathlib import Path

import numpy as np
import pytest

from problems.bipartite_dd import checker, lib

sys.modules.setdefault("lib", lib)     # seed programs do `import lib`
_spec = importlib.util.spec_from_file_location("haar_core", Path(__file__).parents[1] / "seeds" / "haar" / "core.py")
core = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(core)


@pytest.mark.parametrize("make", [lambda: core.group_meta(31, 3, 5), lambda: core.group_heis(3),
                                  lambda: core.group_sl2(3), lambda: core.group_agl(8),
                                  lambda: core.group_times_cyclic(core.group_agl(5), 3)])
def test_group_axioms(make):
    MT, inv = make()
    N = len(MT)
    rng = np.random.default_rng(0)
    a, b, c = rng.integers(0, N, (3, 500))
    assert (MT[MT[a, b], c] == MT[a, MT[b, c]]).all()
    assert (MT[0] == np.arange(N)).all() and (MT[np.arange(N), inv] == 0).all()
    assert all(sorted(row) == list(range(N)) for row in MT[:20])


def test_batch_costs_match_cost_and_cost_zero_means_valid():
    MT, inv = core.group_meta(31, 3, 5)
    N = len(MT)
    rng = np.random.default_rng(1)
    S = np.concatenate([[0], rng.choice(np.arange(1, N), 4, replace=False)]).astype(np.int32)
    X = np.array([x for x in rng.integers(0, N, 12) if x not in S[1:]], dtype=np.int32)
    bc = core.batch_costs(MT, inv, S, 2, X)
    for x, c in zip(X, bc):
        S2 = S.copy()
        S2[2] = x
        assert core.cost(MT, inv, S2) == c
    S, c = core.search(MT, inv, 5, None, time.monotonic() + 20, np.random.default_rng(2))
    assert c == 0
    g = core.checked(MT, S, 5, 5)
    assert g is not None and checker.check(g, 5, 5).valid
    bad = np.array([0, 1, 2, 3, 4], dtype=np.int32)
    assert core.cost(MT, inv, bad) > 0
    n, e = core.haar_edges(MT, bad)
    assert not checker.check((n, e), 5, 5).valid
