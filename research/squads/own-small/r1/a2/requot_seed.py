"""Requot the n=816 seed (meta:17:8:4, flift convention) over index-r subgroup H; output flift base + flift voltages + .bin.
Usage: python3 -I requot_seed.py GENS OUTPREFIX   (GENS = element indices generating H inside meta17_8_4 table)"""
import sys, subprocess, struct, numpy as np
A = "/home/user/degree-diameter/research/squads/own-small/r1/a2"
gens = [int(x) for x in sys.argv[1].split()]; pre = sys.argv[2]
seed = [l.split() for l in open("/home/user/degree-diameter/research/squads/own-small/seeds/nm816_meta17_8_4.out") if l.startswith("e ")]
volt_flift = [int(x[3]) for x in seed]
M = [list(map(int, l.split())) for l in open(A + "/groups/meta17_8_4.grp").read().split("\n")[1:137] if l.strip()]
N = 136
inv = [next(h for h in range(N) if M[g][h] == 0) for g in range(N)]
volt_right = [inv[v] for v in volt_flift]          # flift (u,x)~(v,g x) <-> requot (u,y)~(v,y a) with a = g^-1
base = open("/home/user/degree-diameter/research/squads/own-small/seeds/base33_0.txt").read()
open(pre + ".sub.grp", "w").write("")
# write group table in requot format
with open(pre + ".grp0", "w") as f:
    f.write(f"G {N} 1 0\n" + "\n".join(" ".join(map(str, row)) for row in M) + "\n")
r = subprocess.run(["python3", "-I", "/home/user/degree-diameter/research/squads/own-small/tools/requot.py", "/home/user/degree-diameter/research/squads/own-small/seeds/base33_0.txt",
                    pre + ".grp0", "1", " ".join(map(str, volt_right)), " ".join(map(str, gens)), pre], capture_output=True, text=True)
print(r.stdout, r.stderr)
# convert: requot .sol (right convention, H-indices) -> flift base + voltages (left = inverse)
L = open(pre + ".sol").read().split("\n")
h, _, pp = map(int, L[0].split())
H = [list(map(int, l.split())) for l in open(pre + ".grp").read().split("\n")[1:h + 1] if l.strip()]
hinv = [next(j for j in range(h) if H[g][j] == 0) for g in range(h)]
edges = [tuple(map(int, l.split())) for l in L[1:] if l.strip()]
with open(pre + ".base", "w") as f:
    f.write(f"{2*pp} {len(edges)}\n" + "".join(f"{u} {v}\n" for u, v, a in edges))
with open(pre + ".fvolt", "w") as f:
    f.write(" ".join(str(hinv[a]) for u, v, a in edges) + "\n")
np.array([h], dtype=np.int32).tofile(pre + ".bin")
np.array(H, dtype=np.uint16).tofile(open(pre + ".bin", "ab"))
print("H order", h, "base vertices", 2*pp, "edges", len(edges))
