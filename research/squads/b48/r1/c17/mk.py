import sys, numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups as G
exec(open("/home/user/degree-diameter/research/squads/b48/r1/c17/build.py").read().split("ORDER_OK")[0])
out = "/home/user/degree-diameter/research/squads/b48/r1/c17/tab/"
want = sys.argv[1:]
def build(name):
    if name == "Z3wrZ4xZ4":
        n = 12; g = []
        for b in range(4):
            o = 3 * b
            p = list(range(n)); p[o], p[o + 1], p[o + 2] = o + 1, o + 2, o; g.append(p)
        p = list(range(n))
        for b in range(4):
            for i in range(3): p[3 * b + i] = 3 * ((b + 1) % 4) + i
        g.append(p)
        T = G.t_perm(n, g)
        return G.t_prod(T, G.t_cyc(4))
    if " x cyc " in name:
        base, k = name.split(" x cyc ")
        n, g = specs[base]
        return G.t_prod(G.t_perm(n, g), G.t_cyc(int(k)))
    n, g = specs[name]
    return G.t_perm(n, g)
for name in want:
    T = build(name)
    N = len(T)
    G.check(T)
    G.write_bin(T, out + name.replace(" ", "_") + ".bin")
    print(name, N, "abelian" if np.array_equal(T, T.T) else "nonabelian", flush=True)
