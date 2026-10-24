"""Scan group voltage lifts of H(5) + 2 hops (exact, all fibre-0 sources) over small groups.
usage: scan.py model holo seed step  -> one line per group in results.log (c8 folder)"""
import sys
import time

sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c8')
import gperm_lifts as GL  # noqa: E402

GROUPS = [(20, 1, 1), (5, 4, 2), (21, 1, 1), (7, 3, 2), (24, 1, 1), (3, 8, 2), (27, 1, 1), (9, 3, 4),
          (25, 1, 1), (5, 5, 1), (28, 1, 1), (14, 2, 13), (7, 4, 6), (30, 1, 1), (15, 2, 14), (5, 6, 4)]
model = sys.argv[1]; holo = sys.argv[2] == '1'; seed = int(sys.argv[3]); step = int(sys.argv[4])
only = None if len(sys.argv) <= 5 else [tuple(map(int, g.split(','))) for g in sys.argv[5].split(';')]
for (m, n, r) in (only or GROUPS):
    G = GL.Group(m, n, r)
    NB, M, edges = GL.build_base(5, G, seed, model, holo)
    path = f'{GL.SCR}/scan_{m}x{n}r{r}_{model}_h{int(holo)}_s{seed}.txt'
    GL.write_perm_base(path, NB, M, edges)
    t0 = time.time()
    unr, out = GL.run_gperm(path, 8, 1, step)
    line = (f'q=5 G=Z{m}x|Z{n}(r={r}) order={M} abelian={int(G.abelian())} model={model} holo={int(holo)} '
            f'seed={seed} step={step} unreached={unr} [{time.time()-t0:.1f}s]')
    print(line, flush=True)
    with open('results.log', 'a') as fh:
        fh.write(line + '\n')
