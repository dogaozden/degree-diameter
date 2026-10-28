"""c12: SAT search for an ovoid of Q(4,q) (every line meets it in exactly one point) avoiding a given point set."""
import sys, json, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from hdlib import setup
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def ovoid_avoiding(q, avoid, seed=0, timeout=600):
    Wq, G, _ = setup(q)
    pool = IDPool(start_from=G.np + 1)
    cls = []
    for p in avoid:
        cls.append([-(p + 1)])
    for l, pts in enumerate(G.lines):
        lits = [p + 1 for p in pts]
        enc = CardEnc.equals(lits=lits, bound=1, vpool=pool, encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
    rng = random.Random(seed)
    s = Cadical153(bootstrap_with=cls)
    ok = s.solve()
    if not ok:
        return None
    model = s.get_model()
    O = [p for p in range(G.np) if model[p] > 0]
    s.delete()
    return O

if __name__ == '__main__':
    q = int(sys.argv[1]); base = json.loads(sys.argv[2]) if len(sys.argv) > 2 else []
    O = ovoid_avoiding(q, base)
    print(len(O) if O else None, O)
