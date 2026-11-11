"""Edge list of a liftx solution.  Usage: python3 liftedges.py BASE GROUPS id v1 v2 ... > out.edges
Writes "n" then one "x y" line per edge, with vertex (u,g) = u*N + g and edge (u,g) ~ (v, g*a) for base edge (u,v)
with voltage a (same convention as liftx.c)."""
import sys

def read_group(path, gid):
    with open(path) as f:
        tok = f.read().split()
    i = 0
    while i < len(tok):
        assert tok[i] == "G"
        N, g = int(tok[i + 1]), int(tok[i + 2])
        i += 4
        if g == gid:
            return N, [list(map(int, tok[i + r * N:i + (r + 1) * N])) for r in range(N)]
        i += N * N
    raise SystemExit("group not found")

def main():
    base, gfile, gid = sys.argv[1], sys.argv[2], int(sys.argv[3])
    volt = list(map(int, sys.argv[4:]))
    b = open(base).read().split()
    k, E = int(b[0]), int(b[1])
    edges = [(int(b[2 + 2 * e]), int(b[3 + 2 * e])) for e in range(E)]
    assert len(volt) == E
    N, mul = read_group(gfile, gid)
    out = [str(k * N)]
    for (u, v), a in zip(edges, volt):
        for g in range(N):
            out.append(f"{u * N + g} {v * N + mul[g][a]}")
    print("\n".join(out))

main()
