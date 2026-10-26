#!/usr/bin/env python3
"""Verified values for the new cells (job new-cells-beyond).  One entry per cell: the best checked graph.
Fields: value (vertices), how (construction), check (checker + log path), files (graph / builder / solution).
Run `python3 results.py` to print BEYOND_TABLE.md's table rows."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plan import moore, upper, formulas, CELLS, OURS, n_at_mu

R = {}
def add(d, D, value, how, check, files, note=""):
    R[(d, D)] = dict(value=value, how=how, check=check, files=files, note=note)

# D = 3
add(17, 3, 546, "PG(2,16) incidence graph (Moore graph)", "apsp: checks/d17D3_n546_pg2_16.apsp.txt", "graphs/d17D3_n546_pg2_16.edges.gz; builder research/squads/beyond/r1/c01/build.py")
add(18, 3, 614, "PG(2,17) incidence graph (Moore graph)", "apsp: checks/d18D3_n614_pg2_17.apsp.txt", "graphs/d18D3_n614_pg2_17.edges.gz")
add(19, 3, 624, "fourth hat R(17;2,3), POLISHED.md Thm 2.2 (19-regular)", "apsp: checks/d19D3_n624_fourthhat_q17.apsp.txt", "graphs/d19D3_n624_fourthhat_q17.edges.gz; builder c01/build.py hat 17 2 3")
add(20, 3, 762, "PG(2,19) incidence graph (Moore graph)", "apsp: checks/d20D3_n762_pg2_19.apsp.txt", "graphs/d20D3_n762_pg2_19.edges.gz")
# D = 4
add(17, 4, 8738, "W(16) incidence graph (Moore graph)", "apsp: checks/d17D4_n8738_W16.apsp.txt", "graphs/d17D4_n8738_W16.edges.gz; builder c02/gq2edges.py")
add(18, 4, 10440, "W(17) incidence graph (Moore graph)", "apsp: checks/d18D4_n10440_W17.apsp.txt", "graphs/d18D4_n10440_W17.edges.gz")
add(19, 4, 10982, "AS(17) + clones of two elliptic quadrics, POLISHED.md Cor. A1 (19-regular)", "apsp: checks/d19D4_n10982_AS17_clones.apsp.txt", "graphs/d19D4_n10982_AS17_clones.edges.gz; builder c02/build_as_clones.py")
add(20, 4, 14480, "W(19) incidence graph (Moore graph)", "apsp: checks/d20D4_n14480_W19.apsp.txt", "graphs/d20D4_n14480_W19.edges.gz")
# D = 5
add(17, 5, 33792, "the (16,5) route-chart lift (max degree 16 <= 17); nothing larger found", "apsp (research/theorems/graphs/d16D5_n33792_check.txt)", "research/theorems/graphs/build_d16D5_n33792.py")
add(18, 5, 47600, "multi-doubled-matching lift of W(13): 2 doubled matchings, Z2 x Z5 (18-regular)", "apsp: checks/d18D5_n47600_W13_2dm_Z10.apsp.txt", "graphs/d18D5_n47600_W13_2dm_Z10.edges.gz; builder mdm/build_mdm.py + mdm/nu_q13_s2.txt")
add(20, 5, 75000, "route-chart lift over F5 (4 letters x 5 scalars, fibre F5^4): K3,3 + doubled matching over Z20 (m = 60), chart with 22 singular patterns (squad r1 c04); also 66,640 by the multi-doubled-matching lift of W(13), Z2 x Z7 (MDM.md)", "apsp: checks/d20D5_n75000_routechart_F5_Z20.apsp.txt; checks/d20D5_n66640_W13_3dm_Z14.apsp.txt", "graphs/d20D5_n75000_routechart_F5_Z20.edges.gz (code research/squads/beyond/r1/c04/); graphs/d20D5_n66640_W13_3dm_Z14.edges.gz")
add(19, 5, 52428, "doubled-matching lift of W(16) over Z6 (DM_D5.md; = MDM with k = 1); nu, sigma annealed by squad r1/c05 (dmfast, routes allowed)", "apsp: checks/d19D5_n52428_W16_dm_Z6.apsp.txt", "graphs/d19D5_n52428_W16_dm_Z6.edges.gz; mdm/dm_q16_s11_c05.sol.gz + mdm/build_mdm.py (k = 1)")
# D = 6
add(17, 6, 2236962, "H(16) incidence graph (split Cayley hexagon; Moore graph)", "classical (Tits); built with research/d10D7/hexgen2.c, BFS from 94 vertices: ecc 6 and Moore level sizes (checks/d17D6_n2236962_H16.sampled.txt)", "builder: research/squads/beyond/r1/c08/hexgen2.c + hexbfs.c")
add(18, 6, 3017196, "H(17) incidence graph (Moore graph)", "classical; BFS from 96 vertices: ecc 6, Moore levels (checks/d18D6_n3017196_H17.sampled.txt)", "builder: c08/hexgen2.c")
add(19, 6, 3203968, "Theorem D of POLISHED.md, q = 17, m = 2 (doubling of H(17) with levels and exact whiskers; max degree 19)", "theorem (paper + Lean for all odd q); builder checked all-pairs at q = 5, 7 (checks/thmD_builder_q5_q7.apsp.txt); q = 17 instance: BFS from 96 vertices, ecc 6 (checks/d19D6_n3203968_thmD_q17.sampled.txt)", "builder: research/squads/beyond/r1/c08/thmd.c")
# D = 8
add(17, 8, 41373072, "Haar graph SL(2,53) x Z139, S = {e} + 1 fixed + 5 orbits of size 3", "haarcheck_sl (c15) and hcheck5 (director): VALID", "research/frontier/sols/d17D8_sl_53_139_orb3_c15.txt")
add(19, 8, 86317296, "Haar graph PSL(2,103) x Z79, S = {e} + 6 orbits of size 3", "hcheckpsl VALID (runs/check_hcheckpsl_d19D8_psl_103_79_orb3_s1.txt)", "research/frontier/sols/d19D8_psl_103_79_orb3_s1.txt")
add(20, 8, 122739120, "Haar graph PSL(2,71) x Z343, S = {e} + 1 fixed + 6 orbits of size 3", "hcheckpsl VALID (runs/check_hcheckpsl_d20D8_psl_71_343_orb3_s1.txt)", "research/frontier/sols/d20D8_psl_71_343_orb3_s1.txt")
add(17, 9, 501707400, "Haar graph PSL(2,101) x Z487, S = {e} + 1 fixed + 5 orbits of size 3", "hcheckpsl VALID (runs/check_hcheckpsl_d17D9_psl_101_487_orb3_s2.txt)", "research/frontier/sols/d17D9_psl_101_487_orb3_s2.txt")
add(18, 8, 57637680, "Haar graph SL(2,61) x Z127, S = {e} + 2 fixed + 5 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d18D8_sl_61_127_orb3_s2.txt)", "research/frontier/sols/d18D8_sl_61_127_orb3_s2.txt")
add(18, 9, 790626816, "Haar graph SL(2,127) x Z193, S = {e} + 2 fixed + 5 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d18D9_sl_127_193_orb3_s2.txt)", "research/frontier/sols/d18D9_sl_127_193_orb3_s2.txt")
add(19, 9, 1218394320, "Haar graph SL(2,131) x Z271, S = {e} + 6 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d19D9_sl_131_271_orb3_s2.txt)", "research/frontier/sols/d19D9_sl_131_271_orb3_s2.txt")
add(20, 9, 1823175864, "Haar graph PSL(2,163) x Z421, S = {e} + 1 fixed + 6 orbits of size 3", "hcheckpsl VALID (runs/check_hcheckpsl_d20D9_psl_163_421_orb3_s2.txt)", "research/frontier/sols/d20D9_psl_163_421_orb3_s2.txt")
# D = 11, 12
add(3, 11, 1008, "Haar graph of PSL(2,7) x Z3, S = {e, x, y}", "apsp: research/squads/beyond/r1/c11/check_n1008.txt; director re-run VALID", "graphs/d3D11_n1008_psl2_7xZ3.edges.gz")
add(9, 11, 145258344, "Haar graph PSL(2,197) x Z19, S = {e} + 2 fixed + 2 orbits of size 3", "hcheckpsl VALID (runs/check_hcheckpsl_d9D11_psl_197_19_orb3_s4.txt)", "research/frontier/sols/d9D11_psl_197_19_orb3_s4.txt")
add(10, 11, 445709568, "Haar graph SL(2,193) x Z31, S = {e} + 3 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d10D11_sl_193_31_orb3_s1.txt)", "research/frontier/sols/d10D11_sl_193_31_orb3_s1.txt")
add(3, 12, 1320, "Haar graph of PSL(2,11), S = {e, a, b}", "apsp: c12/checks/apsp_3_12_n1320_psl2_11.txt; director re-run VALID", "graphs/d3D12_n1320_psl2_11.edges.gz")
add(4, 11, 18480, "Haar graph SL(2,11) x Z7, S = {e} + 1 orbit of size 3 (haar_sym, squad r2/d09); earlier 17,600 metacyclic (r1/c13)", "apsp (d09 and director: checks/d4D11_n18480_sl11xZ7.apsp.txt), build_haar2.py, haarcheck_sl", "graphs/d4D11_n18480_sl11xZ7.edges.gz; research/frontier/sols/d4D11_sl_11_7_orb3_d09.txt")
add(4, 12, 50160, "Haar graph SL(2,11) x Z19, S = {e} + 1 orbit of size 3 (haar_sym, squad r2/d09); earlier 48,000 metacyclic (r1/c13)", "apsp (d09 and director: checks/d4D12_n50160_sl11xZ19.apsp.txt), build_haar2.py, haarcheck_sl", "graphs/d4D12_n50160_sl11xZ19.edges.gz; research/frontier/sols/d4D12_sl_11_19_orb3_d09.txt")
add(5, 11, 253080, "Haar graph PSL(2,19) x Z37, random S (haar_sym, director); earlier 158,928 (r1/c14)", "hcheckpsl and build_haar2.py VALID (checks/d5D11_psl_19_37_s1.check.txt)", "research/frontier/sols/d5D11_psl_19_37_s1.txt")
add(5, 12, 912576, "Haar graph PSL(2,97), random S (haar_sym, director); earlier 229,824 (r1/c14)", "hcheckpsl and build_haar2.py VALID (checks/d5D12_psl_97_1_s1.check.txt)", "research/frontier/sols/d5D12_psl_97_1_s1.txt")
add(6, 11, 1971744, "Haar graph PSL(2,47) x Z19, S = 2 free orbits of size 3 (haar_sym ORBIT 3 2 0, director); earlier 659,568 (r1/c14)", "hcheckpsl and build_haar2.py VALID (checks/d6D11_psl_47_19_orb3f0_s1.check.txt)", "research/frontier/sols/d6D11_psl_47_19_orb3f0_s1.txt")
add(7, 11, 10648176, "Haar graph SL(2,43) x Z67, S = {e} + 2 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d7D11_sl_43_67_orb3_s1.txt)", "research/frontier/sols/d7D11_sl_43_67_orb3_s1.txt")
add(6, 12, 9303840, "Haar graph SL(2,71) x Z13, S = 2 free orbits of size 3 (haar_sym ORBIT 3 2 0); earlier 8,924,736 (SL(2,47) x Z43)", "hcheck5 VALID (checks/d6D12_sl_71_13_orb3f0_s2.check.txt)", "research/frontier/sols/d6D12_sl_71_13_orb3f0_s2.txt")
add(7, 12, 56297592, "Haar graph PSL(2,163) x Z13, S = {e} + 2 orbits of size 3", "hcheckpsl VALID (runs/check_hcheckpsl_d7D12_psl_163_13_orb3_s1.txt)", "research/frontier/sols/d7D12_psl_163_13_orb3_s1.txt")
add(8, 11, 43702560, "Haar graph SL(2,89) x Z31, S = {e} + 1 fixed + 2 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d8D11_sl_89_31_orb3_s1.txt)", "research/frontier/sols/d8D11_sl_89_31_orb3_s1.txt")
add(10, 12, 3500976768, "Haar graph PSL(2,193) x Z487, S = {e} + 3 orbits of size 3", "hcheckpsl VALID (runs/check_hcheckpsl_d10D12_psl_193_487_orb3_s1.txt)", "research/frontier/sols/d10D12_psl_193_487_orb3_s1.txt")
add(9, 12, 1055973600, "Haar graph SL(2,199) x Z67, S = {e} + 2 fixed + 2 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d9D12_sl_199_67_orb3_s1.txt)", "research/frontier/sols/d9D12_sl_199_67_orb3_s1.txt")
add(8, 12, 268496208, "Haar graph SL(2,163) x Z31, S = {e} + 1 fixed + 2 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d8D12_sl_163_31_orb3_s1.txt)", "research/frontier/sols/d8D12_sl_163_31_orb3_s1.txt")

def fmt(x): return f"{x:,}"

if __name__ == "__main__":
    print("| (Δ,D) | value | % of M_b | upper bound | construction | check | best formula family (for comparison) |")
    print("|---|---:|---:|---:|---|---|---|")
    for d, D in CELLS:
        r = R.get((d, D))
        allf = formulas(d, D)
        f = [x for x in allf if not x[1].startswith("PATTERN")]
        pat = [x for x in allf if x[1].startswith("PATTERN")]
        fam = f"{fmt(f[0][0])} ({f[0][1]})" if f else "—"
        if pat: fam += f"; 2013-table D=8 pattern (no construction known): {fmt(pat[0][0])} ({pat[0][1][8:]})"
        if D >= 8 or (d <= 10 and D >= 11):
            fam += f"; Haar size law at mu = 5: 2N = {2 * n_at_mu(d, D, 5):.3g}"
        fam = fam.replace("—; ", "")
        if not r:
            print(f"| ({d},{D}) | open | | {fmt(upper(d, D))} | | | {fam} |"); continue
        pct = 100.0 * r['value'] / moore(d, D)
        print(f"| ({d},{D}) | **{fmt(r['value'])}** | {pct:.2f} | {fmt(upper(d, D))} | {r['how']} | {r['check']} | {fam} |")
