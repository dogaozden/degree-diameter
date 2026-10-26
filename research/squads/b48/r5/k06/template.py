# writes TEMPLATE: for every class rep c of G (as voltage on the first free edge) and every orbit rep g2 of the
# centraliser of c acting on G by conjugation, one line of m volts (tree 0, free[0]=c, free[1]=g2, free[2]=free[3]=0).
# usage: template.py BASE m k r > TEMPLATE ; prints free indices and the number of template lines to stderr.
import sys
import numpy as np
base_path, m_, k_, r_ = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
N = m_ * k_
rp = [pow(r_, j, m_) for j in range(k_)]
M = np.zeros((N, N), dtype=np.int64)
for j in range(k_):
    for a in range(m_):
        for l in range(k_):
            for b in range(m_):
                M[a + m_ * j, b + m_ * l] = (a + rp[j] * b) % m_ + m_ * ((j + l) % k_)
assert M[0].tolist() == list(range(N))
INV = np.array([int(np.where(M[g] == 0)[0][0]) for g in range(N)])
seen = set(); reps = []
for g in range(N):
    if g in seen: continue
    reps.append(g)
    for h in range(N): seen.add(int(M[M[h, g], INV[h]]))
lines = open(base_path).read().split("\n")
b, m = map(int, lines[0].split())
E = [tuple(map(int, lines[1 + i].split()[:2])) for i in range(m)]
dart = {u: [] for u in range(b)}
for i, (u, v) in enumerate(E):
    dart[u].append((v, i)); dart[v].append((u, i))
seen_v = {0}; q = [0]; intree = set(); h = 0
while h < len(q):
    u = q[h]; h += 1
    for v, e in dart[u]:
        if v not in seen_v:
            seen_v.add(v); intree.add(e); q.append(v)
free = [i for i in range(m) if i not in intree]
assert len(free) == 4
cnt = 0
for c in reps:
    C = [h for h in range(N) if M[h, c] == M[c, h]]
    done = set(); orbs = []
    for g in range(N):
        if g in done: continue
        orbs.append(g)
        for h in C: done.add(int(M[M[h, g], INV[h]]))
    for g2 in orbs:
        v = [0] * m; v[free[0]] = c; v[free[1]] = g2
        print(" ".join(map(str, v))); cnt += 1
sys.stderr.write(f"N={N} free={free} classes={len(reps)} template_lines={cnt} expected_evals={cnt*N*N}\n")
