# usage: mkedges.py TABLE.ht "s0 s1 ... s6" OUT.edges  (Haar graph H(G,S): (g,A) ~ (s g,B); A = g, B = n + g)
import sys
tab, sset, out = sys.argv[1], [int(x) for x in sys.argv[2].split()], sys.argv[3]
with open(tab) as f:
    toks = f.read().split()
n = int(toks[0]); pos = 2
mul = [int(x) for x in toks[pos:pos + n * n]]
with open(out, "w") as o:
    o.write(f"{2 * n}\n")
    for g in range(n):
        for s in sset:
            o.write(f"{g} {n + mul[s * n + g]}\n")
print("n", n, "S", sset, "edges", n * len(sset))
