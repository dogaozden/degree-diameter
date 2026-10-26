"""c8 (d): random 9-regular bipartite bases with n points, n lines (no GQ structure).
mode cay: point i ~ line j iff j - i in D (random 9-set of Z_n); mode perm: union of 9 random permutations (retry until simple).
usage: python3 mkrand.py cay|perm n seed out.in"""
import sys, random
mode, n, seed, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
if mode == "cay":
    D = rng.sample(range(n), 9)
    lines = [sorted((j + d) % n for d in D) for j in range(n)]   # line j contains points j+D
else:
    while True:
        perms = [rng.sample(range(n), n) for _ in range(9)]
        lines = [[perms[k][l] for k in range(9)] for l in range(n)]
        if all(len(set(s)) == 9 for s in lines): break
sigma = list(range(n)); rng.shuffle(sigma)     # random point -> line bijection
with open(out, "w") as f:
    f.write(f"{n} 9\n")
    for s in lines: f.write(" ".join(map(str, s)) + "\n")
    for v in sigma: f.write(f"{v}\n")
