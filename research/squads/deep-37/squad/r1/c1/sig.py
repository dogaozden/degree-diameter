"""signature of a G-set file: sorted multiset of (colour, orbit size) over the vertex orbits of the group in the file."""
import sys, collections
def sig(fn):
    t = open(fn).read().split()
    n, order = int(t[0]), int(t[1]); p = 2
    perms = []
    for _ in range(order):
        perms.append([int(x) for x in t[p:p+n]]); p += n
    col = [int(x) for x in t[p:p+n]]
    par = list(range(n))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for g in perms:
        for i in range(n):
            a, b = f(i), f(g[i])
            if a != b: par[a] = b
    orb = collections.defaultdict(list)
    for i in range(n): orb[f(i)].append(i)
    return tuple(sorted((col[v[0]], len(v)) for v in orb.values()))
if __name__ == "__main__":
    for fn in sys.argv[1:]:
        print(fn, sig(fn))
