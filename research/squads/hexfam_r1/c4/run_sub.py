"""c4 idea 1: reflection subgroups W(R) of W(E7) mod q; orbit unions via exact max-weight clique.
usage: run_sub.py q [names...]"""
import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r1/c4')
from lib import *
from e7roots import e7_roots, subsystem
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
 'A1^7': ([], 7),
 'A1^4': ([], 4),
 'D4': ([(0,1),(0,2),(0,3)], 4),
 'A4A1': ([(0,1),(1,2),(2,3)], 6),
}
if __name__ == '__main__':
    q = int(sys.argv[1]); names = sys.argv[2:] or list(SUBS)
    cap = q ** 3 + 1
    G = Geo(q)
    simple, R = e7_roots(q)
    print('q', q, 'roots', len(R), flush=True)
    for name in names:
        ed, n = SUBS[name]
        t0 = time.time()
        B = subsystem(R, q, ed, n, seed=1, tries=300)
        if B is None:
            print(name, 'no subsystem', flush=True); continue
        perms = [G.perm(reflection_matrix(b, q)) for b in B]
        wgt, pts, info = evaluate(G, perms, cap, tl=float(__import__("os").environ.get("TL", "15")), label=name)
        ok, ext = check_set(G, pts) if pts else (True, 0)
        print(name, 'orbits', info['orbits'], 'selfcompat', info['selfcompat'], 'best', wgt, 'exact' if info['exact'] else 'TIMELIMIT',
              'sizes', info['sizes'][:12], 'valid', ok, '[%.0fs]' % (time.time() - t0), flush=True)
        if wgt > 0:
            open('/home/user/degree-diameter/research/squads/hexfam_r1/c4/sub_q%d_%s_%d.txt' % (q, name.replace('^', 'p'), wgt), 'w').write('\n'.join(map(str, pts)) + '\n')
