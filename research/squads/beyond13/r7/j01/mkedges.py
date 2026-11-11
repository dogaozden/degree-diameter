# mkedges.py SOL OUT.edges : own edge-list builder for a metacyclic Haar solution (haar_gen3 format).
# Group (a,j)(b,l) = (a + r^j b mod m, j + l mod k); index a*k + j; (g,A)=g, (g,B)=N+g; edges (g,A) ~ (s g, B), s in S.
import sys
hdr = open(sys.argv[1]).readline().split()
m, k, r, N = int(hdr[3]), int(hdr[4]), int(hdr[5]), int(hdr[-1])
assert N == m * k and pow(r, k, m) == 1
S = []
for line in open(sys.argv[1]).readlines()[1:]:
    t = line.split()
    if not t: continue
    a, j = t[1][t[1].index('(') + 1:t[1].index(')')].split(',')
    S.append((int(a.split('=')[1]), int(j.split('=')[1])))
assert len(S) == 5 and len(set(S)) == 5
rp = [pow(r, j, m) for j in range(k)]
with open(sys.argv[2], 'w') as f:
    f.write(f"{2 * N}\n")
    for a in range(m):
        for j in range(k):
            g = a * k + j
            for sa, sj in S:
                ha = (sa + rp[sj] * a) % m; hj = (sj + j) % k
                f.write(f"{g} {N + ha * k + hj}\n")
print("edges", 2 * N, len(S) * N, "S =", S)
