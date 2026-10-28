"""Decision SAT: is there a line set R of size >= k with mode 'spread' (pairwise non-concurrent) or 'pencil'
(concurrent pairs meet off the ovoid and no third R-line meets a pair; at most CAP pairs)?
usage: decide.py mode k [cap]"""
import sys, time, json
from setup_common import *
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
NL = G.nl; oset = set(OV)
meet = {}
for z in range(N):
    ls = [l for l in range(NL) if G.I[z, l]]
    for i in range(len(ls)):
        for j in range(i+1, len(ls)):
            meet[(ls[i], ls[j])] = z


def build(mode, k, cap=None):
    cl = []; top = NL
    for (l, m), z in meet.items():
        if mode == 'spread' or z in oset:
            cl.append([-(l+1), -(m+1)])
        else:
            for n in set(np.nonzero(G.con[l] | G.con[m])[0]) - {l, m}:
                cl.append([-(l+1), -(m+1), -(int(n)+1)])
    if cap is not None and mode == 'pencil':
        pv = []
        for (l, m), z in meet.items():
            if z not in oset:
                top += 1; p = top
                cl += [[-p, l+1], [-p, m+1], [p, -(l+1), -(m+1)]]; pv.append(p)
        enc = CardEnc.atmost(lits=pv, bound=cap, top_id=top, encoding=EncType.seqcounter)
        cl += enc.clauses; top = max(top, enc.nv)
    enc = CardEnc.atleast(lits=list(range(1, NL+1)), bound=k, top_id=top, encoding=EncType.seqcounter)
    cl += enc.clauses
    return cl


if __name__ == '__main__':
    mode, k = sys.argv[1], int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else None
    cl = build(mode, k, cap)
    t = time.time()
    with Solver(name='cd19', bootstrap_with=cl) as s:
        ok = s.solve()
        if ok:
            mdl = s.get_model()
            S = [l for l in range(NL) if mdl[l] > 0]
            Ss = set(S)
            pairs = [(l, m, z) for (l, m), z in meet.items() if l in Ss and m in Ss]
            if mode == 'spread':
                assert is_partial_spread(G, S)
            print(mode, 'k', k, 'cap', cap, 'SAT size', len(S), 'pairs', len(pairs), 'time %.1f' % (time.time()-t), flush=True)
            json.dump(dict(lines=S, pairs=[[int(a), int(b), int(c)] for a, b, c in pairs]),
                      open('set_%s_%d_%s.json' % (mode, len(S), cap), 'w'))
        else:
            print(mode, 'k', k, 'cap', cap, 'UNSAT', 'time %.1f' % (time.time()-t), flush=True)
