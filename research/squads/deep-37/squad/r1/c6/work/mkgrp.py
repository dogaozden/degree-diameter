import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/deep-37/src')
import gutil
fn, out = sys.argv[1], sys.argv[2]
n, E, adj = gutil.load(fn)
perms, go, raw = gutil.aut_gens(adj)
print("grpsize", go, "gens", len(perms))
if go and float(go) > 1000: raise SystemExit("too big")
G = gutil.group_closure(perms, n) if perms else [tuple(range(n))]
ident = tuple(range(n))
G = [ident] + [g for g in G if g != ident]
with open(out, 'w') as f:
    f.write(f"{n} {len(G)}\n")
    for g in G: f.write(" ".join(map(str, g)) + "\n")
side = gutil.sides(adj)
print("order", len(G), "sides", sum(1 for s in side if s == 0), sum(1 for s in side if s == 1))
