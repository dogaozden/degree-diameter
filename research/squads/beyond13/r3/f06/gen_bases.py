import random, itertools, sys
out = "/home/user/degree-diameter/research/squads/beyond13/r3/f06/bases"
def write(name, b, edges):
    with open(f"{out}/{name}.txt", "w") as f:
        f.write(f"{b}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
# K5,5 : A=[0,5), B=[5,10)
write("k55", 10, [(i, 5 + j) for i in range(5) for j in range(5)])
# biplane 2-(11,5,2): blocks i+QR, QR mod 11 = {1,3,4,5,9}; points A=[0,11) blocks as B side; here b=22
QR = {1, 3, 4, 5, 9}
write("biplane11", 22, [(p, 11 + i) for i in range(11) for p in range(11) if (p - i) % 11 in QR])
# random 5-regular bipartite, girth >= 6 (no 4-cycles) by random matchings with rejection
def rand_reg(h, d, seed):
    rnd = random.Random(seed)
    for attempt in range(3000):
        adj = [set() for _ in range(h)]  # A-vertex -> B-vertices
        ok = True
        for _ in range(d):
            ok2 = False
            for t in range(60):
                perm = list(range(h)); rnd.shuffle(perm)
                if all(perm[i] not in adj[i] for i in range(h)):
                    # no 4-cycles: pairs of A vertices share at most one B neighbour
                    newadj = [set(adj[i]) | {perm[i]} for i in range(h)]
                    good = True
                    for i, j in itertools.combinations(range(h), 2):
                        if len(newadj[i] & newadj[j]) > 1: good = False; break
                    if good:
                        adj = newadj; ok2 = True; break
            if not ok2: ok = False; break
        if ok: return [(i, h + j) for i in range(h) for j in sorted(adj[i])]
    raise SystemExit("fail")
for h, s in [(25, 4), (30, 5), (40, 6)]:
    write(f"rnd5g6_{2*h}_{s}", 2 * h, rand_reg(h, 5, s))
print("ok")
