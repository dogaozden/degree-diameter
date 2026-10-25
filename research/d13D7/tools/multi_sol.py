#!/usr/bin/env python3
"""Solution files for the (2r+1)-copy hexagon graphs of multi.c (job cell-13-7).
  export: multi_sol.py export EDGES HEXFILE r OUT.sol   -> writes "multi q N r m H HP n", "freed ...", "hubedges k ...",
          then sigma[0..N-1] (point -> line, hexgen indexing), extracted from the edge list
  build:  multi_sol.py build SOL HEXFILE OUT.edges      -> rebuilds the edge list with multi.c (DUALFILE = sigma,
          RFILE, NSFILE, HP; no randomness involved), i.e. the identical graph
Vertex numbering of multi.c: (x, i) -> i*2N + x (points), i*2N + N + l (lines); line-side hubs L*2N + t (t < H),
point-side hubs L*2N + H + t (t < HP); line-side hub t is joined to the point freed[t mod m]."""
import sys, os, subprocess, tempfile, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); import hexlib
cmd = sys.argv[1]
if cmd == 'export':
    edges, hexfile, r, out = sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
    q, lines, coord = hexlib.load(hexfile); N = len(coord); L = 2 * r + 1
    with open(edges) as f:
        n = int(f.readline()); E = np.loadtxt(f, dtype=np.int64)
    base = L * 2 * N
    sig = -np.ones(N, np.int64)
    up = E[(E[:, 0] < N) & (E[:, 1] >= 2 * N + N) & (E[:, 1] < 4 * N)]          # level-0 point -> level-1 line
    sig[up[:, 0]] = up[:, 1] - 3 * N
    hubL = E[(E[:, 0] >= base) & (E[:, 1] < N)]                                  # line-side hub ~ level-0 point
    Hn = int(hubL[:, 0].max() - base + 1)
    freed_of = {int(a - base): int(b) for a, b in hubL}
    hubP = E[(E[:, 0] >= base + Hn) & (E[:, 1] >= N) & (E[:, 1] < 2 * N)]          # point-side hub ~ level-0 line
    HP = int(hubP[:, 0].max() - base - Hn + 1) if len(hubP) else 0
    # freed points in multi.c order: hub t = a*m + j, so the first m line-side hubs give R in order
    R = []
    for t in range(Hn):
        if t > 0 and freed_of[t] == freed_of[0] and len(R) > 0: break
        R.append(freed_of[t])
    m = len(R)
    pts_lines = {int(a - base - Hn): int(b - N) for a, b in hubP}
    for j in range(m):                                                           # sigma on R from the point-side hubs
        if j in pts_lines: sig[R[j]] = pts_lines[j]
    assert (sig >= 0).all() and len(set(sig.tolist())) == N, 'sigma not recovered as a bijection'
    hg = E[(E[:, 0] >= base) & (E[:, 0] < base + Hn) & (E[:, 1] >= base + Hn)]
    with open(out, 'w') as f:
        f.write(f'multi {q} {N} {r} {m} {Hn} {HP} {n}\nfreed ' + ' '.join(map(str, R)) + '\n')
        f.write(f'hubedges {len(hg)} ' + ' '.join(f'{a - base} {b - base - Hn}' for a, b in hg) + '\n')
        for i in range(0, N, 20): f.write(' '.join(map(str, sig[i:i + 20].tolist())) + '\n')
    print(f'wrote {out}: q={q} r={r} m={m} H={Hn} HP={HP} n={n} hubedges={len(hg)}')
elif cmd == 'build':
    sol, hexfile, out = sys.argv[2], sys.argv[3], sys.argv[4]
    tok = open(sol).read().split()
    assert tok[0] == 'multi'
    q, N, r, m, Hn, HP, n = map(int, tok[1:8]); pos = 8
    assert tok[pos] == 'freed'; R = tok[pos + 1: pos + 1 + m]; pos += 1 + m
    assert tok[pos] == 'hubedges'; k = int(tok[pos + 1]); hg = tok[pos + 2: pos + 2 + 2 * k]; pos += 2 + 2 * k
    sig = tok[pos: pos + N]; assert len(sig) == N
    d = tempfile.mkdtemp()
    open(f'{d}/R', 'w').write('\n'.join(R) + '\n'); open(f'{d}/sig', 'w').write('\n'.join(sig) + '\n')
    open(f'{d}/hub', 'w').write('\n'.join(f'{hg[2 * i]} {hg[2 * i + 1]}' for i in range(k)) + '\n')
    env = dict(os.environ, DUALFILE=f'{d}/sig', RFILE=f'{d}/R', NSFILE=f'{d}/hub', HP=str(HP), NOCHECK='1')
    multi = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'multi')
    subprocess.run([multi, hexfile, str(r), '1', out], env=env, check=True)
