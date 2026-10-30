import sys, random
sys.argv = ['x']
import bic
B = bic.Bic('ht/g1815_1.ht')
rng = random.Random(5)
H, K = B.subs[0], B.subs[0]; print("nsub3", len(B.subs))
B.setup(H, K)
for trial in range(3):
    ch = rng.sample(B.small, 7)
    c, adj = B.cost(ch)
    deg = set(len(a) for a in adj)
    sym = all(u in adj[v] for u in range(len(adj)) for v in adj[u])
    print("cost", c, "degrees", deg, "symmetric", sym, "bip", all((u < B.m) != (v < B.m) for u in range(len(adj)) for v in adj[u]))
