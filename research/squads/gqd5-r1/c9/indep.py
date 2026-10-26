"""max independent set of a graph (bool adjacency) via SAT with cardinality; returns list"""
import numpy as np
from pysat.formula import CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

def indep_sat(adj, k, forced_in=(), forced_out=(), seed_clauses=()):
    n = adj.shape[0]
    cnf = []
    iu, ju = np.nonzero(np.triu(adj, 1))
    for i, j in zip(iu, ju): cnf.append([-(int(i) + 1), -(int(j) + 1)])
    for i in forced_in: cnf.append([int(i) + 1])
    for i in forced_out: cnf.append([-(int(i) + 1)])
    card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=k, top_id=n, encoding=EncType.seqcounter)
    cnf += card.clauses
    with Cadical153(bootstrap_with=cnf) as s:
        if s.solve():
            m = s.get_model(); return [i for i in range(n) if m[i] > 0]
    return None

def max_indep(adj, lo, hi, **kw):
    """largest k in [lo,hi] with an independent set, linear from lo upward"""
    best = None
    k = lo
    while k <= hi:
        S = indep_sat(adj, k, **kw)
        if S is None: break
        best = S; k = len(S) + 1
    return best
