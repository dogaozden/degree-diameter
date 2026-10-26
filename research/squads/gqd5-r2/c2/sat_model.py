"""SAT model for relaxed sets T on W(11):
   x_p (p in T). (a) at most one point of T per S-line (any two points on an S-line are a forbidden pair).
   (b) for each p: x_p -> at most one collinear neighbour in T (neighbours are all on non-S lines through p).
   Cardinality |T| >= k via an incremental totalizer on the negated literals."""
import json, sys, time
from pysat.card import CardEnc, EncType, ITotalizer
from pysat.formula import CNF
from pysat.solvers import Solver
S_ = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r2/c2/struct.json'))
plines, lines, S, sline = S_['plines'], S_['lines'], set(S_['S']), S_['sline']
n = len(plines)
X = lambda p: p + 1
def build():
    cnf = CNF(); top = [n]
    def newv():
        top[0] += 1; return top[0]
    # (a) one point per S-line
    byS = {}
    for p in range(n): byS.setdefault(sline[p], []).append(p)
    for l, pts in byS.items():
        cc = CardEnc.atmost([X(p) for p in pts], 1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], cc.nv)
        for c in cc.clauses: cnf.append(c)
    # (b) conditional AMO over non-S neighbours
    for p in range(n):
        nb = [q for l in plines[p] if l not in S for q in lines[l] if q != p]
        cc = CardEnc.atmost([X(q) for q in nb], 1, top_id=top[0], encoding=EncType.ladder)
        top[0] = max(top[0], cc.nv)
        for c in cc.clauses:
            cnf.append(c + [-X(p)])
    return cnf, top[0]
if __name__ == '__main__':
    t0 = time.time()
    cnf, top = build()
    print('clauses', len(cnf.clauses), 'vars', top, 'build', round(time.time()-t0,1), flush=True)

def solve_atleast(k, hint=None, solver='cd15', tlimit=None):
    from pysat.solvers import Solver
    cnf, top = build()
    card = CardEnc.atleast([X(p) for p in range(n)], k, top_id=top, encoding=EncType.seqcounter)
    for c in card.clauses: cnf.append(c)
    with Solver(name=solver, bootstrap_with=cnf.clauses) as s:
        if hint:
            s.set_phases([X(p) if p in hint else -X(p) for p in range(n)])
        ok = s.solve()
        if ok:
            m = s.get_model()
            T = [p for p in range(n) if m[X(p)-1] > 0]
            return T
        return None
