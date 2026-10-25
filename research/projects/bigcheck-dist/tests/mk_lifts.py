import random, sys
def lift_to_edges(NB, M, E, path):
    with open(path, "w") as f:
        f.write(f"{NB*M}\n")
        for (u, v, a) in E:
            for g in range(M):
                f.write(f"{u*M+g} {v*M+(g+a)%M}\n")
def write_spec(NB, M, E, auts, path):
    with open(path, "w") as f:
        f.write(f"bcd-lift 1\ngroup cyclic {M}\nvertices {NB}\nedges {len(E)}\n")
        for e in E: f.write("%d %d %d\n" % e)
        for (u, p, c) in auts:
            f.write(f"aut {u}\n" + " ".join(map(str, p)) + "\n" + " ".join(map(str, c)) + "\n")
        f.write("end\n")
rng = random.Random(int(sys.argv[1]))
# test A: cyclic Haar graph Z_M, S of size d
M, d = 300, 4
S = rng.sample(range(M), d)
E = [(0, 1, s) for s in S]
write_spec(2, M, E, [], "haar.spec"); lift_to_edges(2, M, E, "haar.edges")
# test B: base = Z_k lift of random bipartite multigraph on b vertices (b even: 0..b/2-1 left), lifted again over Z_M
b, k, M2 = 6, 5, 37
E0 = []
for v in range(b // 2):
    for _ in range(3):
        w = rng.randrange(b // 2, b); E0.append((v, w, rng.randrange(k), rng.randrange(M2)))
NB = b * k; E = []
for (v, w, t, f) in E0:
    for i in range(k):
        E.append((v * k + i, w * k + (i + t) % k, f))
p = [ (x // k) * k + (x % k + 1) % k for x in range(NB)]
write_spec(NB, M2, E, [(1, p, [0]*NB)], "rot.spec"); lift_to_edges(NB, M2, E, "rot.edges")
# bad: perturb one voltage
E[0] = (E[0][0], E[0][1], (E[0][2] + 1) % M2)
write_spec(NB, M2, E, [(1, p, [0]*NB)], "bad.spec")
# auts as explicit perms for rot: (x, g) -> (p x, g)
with open("rot.aut", "w") as f:
    f.write("perm " + " ".join(str(p[x // M2] * M2 + x % M2) for x in range(NB * M2)) + "\n")
    f.write("perm " + " ".join(str((x // M2) * M2 + (x % M2 + 1) % M2) for x in range(NB * M2)) + "\n")
