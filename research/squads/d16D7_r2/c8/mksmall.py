import numpy as np, sys
fn = sys.argv[1]; out = sys.argv[2]; which = sys.argv[3]
b = open(fn, 'rb').read()
q, N, L = [int(x) for x in np.frombuffer(b[:12], dtype=np.int32)]
LP = np.frombuffer(b[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1).astype(np.int64)
PL = [[] for _ in range(N)]
for l in range(L):
    for p in LP[l]: PL[p].append(l)
if which == 'spread':   # rows = lines, columns = points
    rows = [(l, LP[l].tolist()) for l in range(L)]; ncol = N
else:                   # rows = points, columns = lines
    rows = [(p, PL[p]) for p in range(N)]; ncol = L
with open(out, 'w') as f:
    f.write(f'{len(rows)} {ncol}\n')
    for i, cs in rows:
        f.write(f'{i} ' + ' '.join(map(str, cs)) + '\n')
print(fn, which, 'q', q, 'N', N, 'L', L, 'rowlen', set(len(c) for _, c in rows))
