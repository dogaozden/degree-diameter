"""Smallest sets of lines of Q(4,q) covering all points (= smallest blocking sets of W(q)), q = 3, 5, by SAT with a
cardinality constraint; and the structure of covers of size q^2+q.  Used for Proposition 5.4."""
import sys, itertools
from pysat.formula import CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
from gqlib import W

def min_blocking(G, k, extra=None):
    """point set of size <= k meeting every line of G"""
    cnf = CNF(); n = G.np
    for l in G.lines: cnf.append([p + 1 for p in l])
    card = CardEnc.atmost(lits=list(range(1, n + 1)), bound=k, top_id=n, encoding=EncType.seqcounter)
    cnf.extend(card.clauses)
    if extra: cnf.extend(extra)
    with Cadical153(bootstrap_with=cnf.clauses) as s:
        if s.solve():
            m = s.get_model(); return [i for i in range(n) if m[i] > 0]
    return None

for q in (3, 5):
    G = W(q)            # blocking sets of W(q) = line covers of Q(4,q)
    k = q * q + 1
    while True:
        B = min_blocking(G, k)
        print('W(%d): blocking set of size <= %d: %s' % (q, k, 'yes (%d)' % len(B) if B else 'no')); sys.stdout.flush()
        if B: break
        k += 1
