#!/usr/bin/env python3
"""Verified values for the new cells (job new-cells-beyond).  One entry per cell: the best checked graph.
Fields: value (vertices), how (construction), check (checker + log path), files (graph / builder / solution).
Run `python3 results.py` to print BEYOND_TABLE.md's table rows."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plan import moore, upper, formulas, CELLS, OURS

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
# D = 8
add(17, 8, 41373072, "Haar graph SL(2,53) x Z139, S = {e} + 1 fixed + 5 orbits of size 3", "haarcheck_sl (c15) and hcheck5 (director): VALID", "research/frontier/sols/d17D8_sl_53_139_orb3_c15.txt")
# D = 11, 12
add(3, 11, 1008, "Haar graph of PSL(2,7) x Z3, S = {e, x, y}", "apsp: research/squads/beyond/r1/c11/check_n1008.txt; director re-run VALID", "graphs/d3D11_n1008_psl2_7xZ3.edges.gz")
add(3, 12, 1320, "Haar graph of PSL(2,11), S = {e, a, b}", "apsp: c12/checks/apsp_3_12_n1320_psl2_11.txt; director re-run VALID", "graphs/d3D12_n1320_psl2_11.edges.gz")
add(4, 11, 17600, "metacyclic Haar graph Z440 x| Z20 (r = 107)", "apsp (c13 and director)", "graphs/d4D11_n17600_meta440_20.edges.gz; builder c13/build_meta.py")
add(4, 12, 48000, "metacyclic Haar graph Z1200 x| Z20 (r = 413)", "apsp (c13 and director)", "graphs/d4D12_n48000_meta1200_20.edges.gz")
add(5, 11, 158928, "Haar graph SL(2,43), S = {e} + 2 orbits of size 2", "build_haar2.py (c14 and director)", "research/frontier/sols/d5D11_sl_43_1_c14.txt")
add(5, 12, 229824, "Haar graph PSL(2,3) x PSL(2,7) x Z57", "build_haar2.py (c14 and director)", "research/frontier/sols/d5D12_prod_psl_3_psl_7_57_c14.txt")
add(6, 11, 659568, "Haar graph SL(2,13) x Z151, S = 2 free orbits of size 3", "build_haar2.py (c14 and director)", "research/frontier/sols/d6D11_sl_13_151_c14.txt")
add(7, 11, 10648176, "Haar graph SL(2,43) x Z67, S = {e} + 2 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d7D11_sl_43_67_orb3_s1.txt)", "research/frontier/sols/d7D11_sl_43_67_orb3_s1.txt")
add(7, 12, 56297592, "Haar graph PSL(2,163) x Z13, S = {e} + 2 orbits of size 3", "hcheckpsl VALID (runs/check_hcheckpsl_d7D12_psl_163_13_orb3_s1.txt)", "research/frontier/sols/d7D12_psl_163_13_orb3_s1.txt")
add(8, 11, 43702560, "Haar graph SL(2,89) x Z31, S = {e} + 1 fixed + 2 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d8D11_sl_89_31_orb3_s1.txt)", "research/frontier/sols/d8D11_sl_89_31_orb3_s1.txt")
add(9, 12, 1055973600, "Haar graph SL(2,199) x Z67, S = {e} + 2 fixed + 2 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d9D12_sl_199_67_orb3_s1.txt)", "research/frontier/sols/d9D12_sl_199_67_orb3_s1.txt")
add(8, 12, 268496208, "Haar graph SL(2,163) x Z31, S = {e} + 1 fixed + 2 orbits of size 3", "hcheck5 VALID (runs/check_hcheck5_d8D12_sl_163_31_orb3_s1.txt)", "research/frontier/sols/d8D12_sl_163_31_orb3_s1.txt")

def fmt(x): return f"{x:,}"

if __name__ == "__main__":
    print("| (Δ,D) | value | % of M_b | upper bound | construction | check | best formula family (for comparison) |")
    print("|---|---:|---:|---:|---|---|---|")
    for d, D in CELLS:
        r = R.get((d, D))
        f = formulas(d, D)
        fam = f"{fmt(f[0][0])} ({f[0][1]})" if f else "—"
        if not r:
            print(f"| ({d},{D}) | open | | {fmt(upper(d, D))} | | | {fam} |"); continue
        pct = 100.0 * r['value'] / moore(d, D)
        print(f"| ({d},{D}) | **{fmt(r['value'])}** | {pct:.2f} | {fmt(upper(d, D))} | {r['how']} | {r['check']} | {fam} |")
