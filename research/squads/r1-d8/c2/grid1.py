import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c2')
import holo
from holo import Q, SCR
import gh

H = gh.load(5)
k = int(sys.argv[1])
rules = {
    'sqclass': [0, 1, 2, 2, 1, 3],          # {t,-t} classes: 0 | {1,4} | {2,3} | infinity
    'quad_sq': [0, 1, 4, 4, 1, 0],          # lam^2
    'lin':     [0, 1, 2, 3, 4, 0],          # lam
    'cubic':   [0, 1, 3, 2, 4, 0],          # lam^3 (= lam^3 mod 5: 0,1,3,2,4)
}
refs = sys.argv[2].split(',') if len(sys.argv) > 2 else ['first', 'proj']
seeds = [0]
for ref in refs:
    fr = holo.frames(H, ref)
    lam = holo.lam_table(H, fr)
    for name, Fv in rules.items():
        for hl in ['zero', 'rand']:
            res = []
            t0 = time.time()
            for s in seeds:
                path = f'{SCR}/c2_k{k}_{ref}_{name}_{hl}_s{s}.txt'
                u, out = holo.build_and_score(H, lam, Fv, k, s, hl, path)
                res.append(u)
            print(f'k={k} M={5*k} ref={ref} F={name} hops={hl} unreached={res} ({time.time()-t0:.1f}s)', flush=True)
