import sys
import numpy as np
m_, k_, r_ = map(int, sys.argv[1:4]); N = m_*k_
rp = [pow(r_, j, m_) for j in range(k_)]
M = np.zeros((N, N), dtype=np.int64)
for j in range(k_):
    for a in range(m_):
        for l in range(k_):
            for b in range(m_):
                M[a + m_*j, b + m_*l] = (a + rp[j]*b) % m_ + m_*((j+l) % k_)
INV = np.array([int(np.where(M[g] == 0)[0][0]) for g in range(N)])
seen = set(); reps = []
for g in range(N):
    if g in seen: continue
    reps.append(g)
    for h in range(N): seen.add(int(M[M[h, g], INV[h]]))
tot = 0
for c in reps:
    C = [h for h in range(N) if M[h, c] == M[c, h]]
    os_ = set(); orbs = 0
    for g in range(N):
        if g in os_: continue
        orbs += 1
        for h in C: os_.add(int(M[M[h, g], INV[h]]))
    tot += orbs
print(f"N={N} classes={len(reps)} sum_orbits={tot} evals~{tot*N*N}")
