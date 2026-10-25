"""c4 direction A: reflection subgroups of W(E7) mod 13 (and of W(E6) = roots orthogonal to the E6 centre).
usage: run_A.py MODE(E7|E6) TL NAME [NAME...]"""
import sys, time, numpy as np
from hx import *
SUBS = {
 'A7': ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6)], 7),
 'D6A1': ([(0,1),(1,2),(2,3),(3,4),(3,5)], 7),
 'D6': ([(0,1),(1,2),(2,3),(3,4),(3,5)], 6),
 'A6': ([(0,1),(1,2),(2,3),(3,4),(4,5)], 6),
 'A6A1': ([(0,1),(1,2),(2,3),(3,4),(4,5)], 7),
 'D5A1': ([(0,1),(1,2),(2,3),(2,4)], 6),
 'D5A1x': ([(0,1),(1,2),(2,3),(2,4)], 7),
 'A5A2': ([(0,1),(1,2),(2,3),(3,4),(5,6)], 7),
 'A5A1': ([(0,1),(1,2),(2,3),(3,4)], 6),
 'A5A1A1': ([(0,1),(1,2),(2,3),(3,4)], 7),
 'D4A1^3': ([(0,1),(0,2),(0,3)], 7),
 'A3A3A1': ([(0,1),(1,2),(3,4),(4,5)], 7),
 'A2^3': ([(0,1),(2,3),(4,5)], 6),
 'A2^3A1': ([(0,1),(2,3),(4,5)], 7),
 'E6': ([(0,1),(1,2),(2,3),(3,4),(2,5)], 6),
 'E6A1': ([(0,1),(1,2),(2,3),(3,4),(2,5)], 7),
 'A4A2A1': ([(0,1),(1,2),(2,3),(4,5)], 7),
 'A1^6': ([], 6),
 'A1^7': ([], 7),
 'D4': ([(0,1),(0,2),(0,3)], 4),
 'A4A1': ([(0,1),(1,2),(2,3)], 6),
 'A4A2': ([(0,1),(1,2),(2,3),(4,5)], 6),
 'D4A2': ([(0,1),(0,2),(0,3),(4,5)], 6),
 'D5': ([(0,1),(1,2),(2,3),(2,4)], 5),
 'A5': ([(0,1),(1,2),(2,3),(3,4)], 5),
 'A3A1A1': ([(0,1),(1,2)], 4),
}
def e6_roots(R, Bsimple6):
    # z spans the orthogonal complement of the E6 span (1-dim); E6 roots = roots orthogonal to z
    from lib import A7 as A
    from q6lib import nullspace_mod
    Mr = np.array([(A @ b) % Q for b in Bsimple6]) % Q
    ns = nullspace_mod(Mr, Q)
    assert len(ns) == 1, len(ns)
    z = ns[0]
    keep = (R @ A @ z) % Q == 0
    return R[keep]

if __name__ == '__main__':
    mode = sys.argv[1]; TL = float(sys.argv[2]); names = sys.argv[3:]
    R = np.load('roots13.npy')
    if mode == 'E6':
        ed6, _ = SUBS['E6']
        B6 = subsystem(R, Q, ed6, 6, seed=1, tries=300)
        R = e6_roots(R, B6)
        print('E6 roots', len(R), flush=True)
    best_overall = 0
    for name in names:
        ed, n = SUBS[name]
        t0 = time.time()
        B = subsystem(R, Q, ed, n, seed=1, tries=300)
        if B is None:
            print(mode, name, 'no subsystem', flush=True); continue
        perms = refl_perms(B)
        w, pts, info = solve_orbits(mode + ':' + name, perms, tl_exact=TL, tl_ils=TL, seed=1, verbose=False)
        ok = score(write_set('tmp_%s_%s.txt' % (mode, name.replace('^','p')), pts)) if pts else 'none'
        print(mode, name, info, 'SCORE', ok, '[%.0fs]' % (time.time()-t0), flush=True)
        if pts and w > 0 and w >= 700:
            write_set('A_%s_%s_%d.txt' % (mode, name.replace('^','p'), w), pts)
        best_overall = max(best_overall, w)
    print('best', best_overall, flush=True)
