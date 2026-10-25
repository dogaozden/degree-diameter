import numpy as np, sys
fn = sys.argv[1]; out = sys.argv[2]; which = sys.argv[3]
b = open(fn, 'rb').read()
q, N, L = [int(x) for x in np.frombuffer(b[:12], dtype=np.int32)]
LP = np.frombuffer(b[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1).astype(np.int64)
PL = [[] for _ in range(N)]
for l in range(L):
    for p in LP[l]: PL[p].append(l)
if which == 'pts':
    nbr = [set() for _ in range(N)]
    for l in range(L):
        for p in LP[l]:
            for r in LP[l]:
                if r != p: nbr[p].add(int(r))
    M = N
else:
    nbr = [set() for _ in range(L)]
    for p in range(N):
        for l in PL[p]:
            for m in PL[p]:
                if m != l: nbr[l].add(m)
    M = L
E = sum(len(s) for s in nbr) // 2
with open(out, 'w') as f:
    f.write(f'{M} {E}\n')
    for i in range(M):
        s = sorted(nbr[i])
        f.write(f'{i} {i} {len(s)} ' + ' '.join(map(str, s)) + '\n')
print('graph', which, 'M', M, 'E', E)
