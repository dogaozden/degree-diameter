"""c5: rebuild and write the explicit geometric rules found by fam_m.py (q=3), then check them twice.
rule: points ranked by lex order of normalized coordinates, lines ranked by lex order of their two smallest points;
sigma_1(p) = line of the same rank, sigma_2(p) = line of rank + sh (mod N); matching voltages constant ma (sigma_1), mb (sigma_2);
hexagon flag (p, l) voltage iota[t], t = position of p on l in the frame (lex-smallest two points of l) in {0,1,2,inf}."""
import sys, subprocess, os
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
from geo import *
q = 3; G = geometry(q); N = G["N"]; Q1 = G["Q1"]
def build(m, sh, iota, ma, mb):
    rp, lr = G["rank_p"], G["line_of_rank"]
    s1 = [lr[rp[p]] for p in range(N)]
    s2 = [lr[(rp[p] + sh) % N] for p in range(N)]
    hv = [iota[G["tlab"][(l, k)]] for l in range(N) for k in range(Q1)]
    return [s1, s2], [[ma] * N, [mb] * N], hv
if __name__ == "__main__":
    cases = [(16, 52, [0, 12, 6, 13], 1, 14), (18, 121, [0, 5, 3, 6], 13, 9)]
    for m, sh, iota, ma, mb in cases:
        sigs, mvs, hv = build(m, sh, iota, ma, mb)
        sol = os.path.join(HERE, "sols", "explicit_q3_m%d.sol" % m)
        write_sol(sol, q, m, sigs, mvs, hv)
        r = subprocess.run(["timeout", "120", "nice", "-n", "19", "./verify", "hex/hex_q3.bin", sol, "8"],
                           cwd=HERE, capture_output=True, text=True)
        print("verify.c (independent BFS):", r.stdout.strip() or r.stderr.strip())
        print("lift3:", evaluate(q, m, sigs, mvs, hv, tag="explicit"), "m", m, "sh", sh, "iota", iota, "ma", ma, "mb", mb)
