#!/usr/bin/env python3
"""r2-c3 explicit rule (no annealing). Builds a lift3 solution file for the cyclic lift Z_c of GH(q) + 2 matchings.

Base graph: hex/hex_q{q}.bin (hexgen2 output): points 0..N-1 (sorted normal-form codes), lines 0..N-1 (hexgen2 line
table; line l lists its q+1 points pl[l*(q+1)+k] in ascending point index).
Rule ("product", best found: c = 16 at q = 4):
  matching 1: sigma1(p) = p (line with index p), constant voltage 1 on the edge (p, sigma1(p));
  matching 2: sigma2(p) = (p + N // 3) mod N, constant voltage b on the edge (p, sigma2(p));
  hexagon flag (p, l), p = pl[l*(q+1)+k] (direction point -> line): voltage (s * p * l) mod c.
Usage: build_rule.py q c s b [out.sol]   (verified: q=4, c=16, s=6, b=6; also q=2, 3)
Then:  cd research/d10D8/hex && IN=<out.sol> GROUP="cyc c" J=2 D=8 ITERS=0 ./lift3 q   (DIAMETER_OK when fullcost 0)
"""
import struct, sys
HEXBIN = "/home/user/degree-diameter/research/d10D8/hex/hex/hex_q%d.bin"
q = int(sys.argv[1]) if len(sys.argv) > 1 else 4
c = int(sys.argv[2]) if len(sys.argv) > 2 else 16
s = int(sys.argv[3]) if len(sys.argv) > 3 else 6
b = int(sys.argv[4]) if len(sys.argv) > 4 else 6
out = sys.argv[5] if len(sys.argv) > 5 else "/home/user/degree-diameter/research/squads/d10D8-r2/c3/sols/rule_q%d_c%d_s%d_b%d.sol" % (q, c, s, b)
data = open(HEXBIN % q, "rb").read()
qq, N, L = struct.unpack_from("<3i", data, 0)
Q1 = q + 1
pl = struct.unpack_from("<%di" % (N * Q1), data, 12)
sig1 = list(range(N))
sig2 = [(p + N // 3) % N for p in range(N)]
mv1 = [1] * N
mv2 = [b] * N
hv = [(s * pl[l * Q1 + k] * l) % c for l in range(N) for k in range(Q1)]
with open(out, "w") as f:
    f.write("%d %d %d %d %d\ncyc %d\n" % (q, 2, c, 8, 0, c))
    f.write(" ".join(map(str, sig1)) + "\n" + " ".join(map(str, sig2)) + "\n")
    f.write(" ".join(map(str, mv1)) + "\n" + " ".join(map(str, mv2)) + "\n")
    f.write(" ".join(map(str, hv)) + "\n")
print(out)
