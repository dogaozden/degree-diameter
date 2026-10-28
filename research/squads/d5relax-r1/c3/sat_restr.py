"""Decide whether the spread-restricted model of W(q) has a set of size >= K (pysat, cadical).
usage: python3 sat_restr.py q K timeout_s"""
import sys, os, time, threading
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wstruct import load
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
q = int(sys.argv[1]); K = int(sys.argv[2]); tmo = float(sys.argv[3])
adj, L, sp = load(q); n = len(adj); S = q * q + 1
spl = [[p for p in range(n) if sp[p] == s] for s in range(S)]
spset = set(frozenset(x) for x in spl)
nonsp = [l for l in L if frozenset(l) not in spset]
cls = []; top = n
for l in nonsp:
    e = CardEnc.atmost(lits=[v + 1 for v in l], bound=1, top_id=top, encoding=EncType.seqcounter); top = max(top, e.nv); cls += e.clauses
for s in spl:
    e = CardEnc.atmost(lits=[v + 1 for v in s], bound=2, top_id=top, encoding=EncType.seqcounter); top = max(top, e.nv); cls += e.clauses
e = CardEnc.atleast(lits=[v + 1 for v in range(n)], bound=K, top_id=top, encoding=EncType.seqcounter); top = max(top, e.nv); cls += e.clauses
t0 = time.time()
with Solver(name='cadical195', bootstrap_with=cls) as s:
    timer = threading.Timer(tmo, lambda: s.interrupt()); timer.start()
    res = s.solve_limited(expect_interrupt=True); timer.cancel()
    if res:
        m = s.get_model(); T = [v for v in range(n) if m[v] > 0]
        print('q=%d K=%d SAT size %d time %.1f' % (q, K, len(T), time.time() - t0))
        open('sat_q%d_K%d.txt' % (q, K), 'w').write('%d\n' % len(T) + ''.join('%d\n' % v for v in T))
    elif res is False:
        print('q=%d K=%d UNSAT time %.1f' % (q, K, time.time() - t0))
    else:
        print('q=%d K=%d UNKNOWN (timeout) time %.1f' % (q, K, time.time() - t0))
