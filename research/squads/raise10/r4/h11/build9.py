import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
exec(open("/home/user/degree-diameter/research/squads/raise10/r4/h11/build7.py").read().split("# G1:")[0])  # V helpers: tr, trans, W, blk, I2, L1, L2
def hmul(g, h):
    return ((g[0] + h[0]) % 3, (g[1] + h[1]) % 3, (g[2] + h[2] + g[0] * h[1]) % 3)
els = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]
ix = {e: 9 * e[0] + 3 * e[1] + e[2] for e in els}
def left(g):
    return [16 + ix[hmul(g, h)] for h in els]
n = 43
gens = [trans(k) + [16 + i for i in range(27)] for k in range(4)]
gens.append(L1 + [16 + i for i in range(27)])  # placeholder, fixed below
gens = gens[:4]
gens.append(tr(L1) + left((1, 0, 0)))
gens.append(tr(L2) + left((0, 1, 0)))
gens.append(list(range(16)) + left((0, 0, 1)))
spec = "perm %d " % n + " ; ".join(",".join(str(x) for x in g) for g in gens)
T = groups.table(spec)
N = len(T)
print("V2^4 x| Heis3 N=", N, "expected 432", "OK" if N == 432 else "MISMATCH", flush=True)
if N == 432:
    groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/V4xHeis3.bin")
