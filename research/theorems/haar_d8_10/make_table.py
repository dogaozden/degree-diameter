"""Build the records table of HAAR_D8_10.md §5 from the record list below and the re-check logs in recheck/.

Usage: python3 make_table.py            (prints Markdown)

The "this session" column lists a checker only if its log in recheck/ has a VALID line for that exact solution file;
"earlier" is the evidence already in the repo before this session (see the notes in HAAR_D8_10.md §5.2).
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
R = os.path.join(HERE, "recheck")

# cell, 2013 table, ours, group, orbit structure of S (verified by orbit_check*.py), solution file stem, Lean, earlier checks
ROWS = [
    ((3, 8), 256, 288, "lift of a 4-vertex base over Z_3² ⋊ Z_8 (note 1)", "–", "c1r_d3D8_n288_b2_3_0_aff302108_s1", "✓", "A"),
    ((5, 8), 9234, 9760, "Z_61 ⋊_8 Z_80", "–", "d5D8_n9760_haar_meta61_80_8_s1", "(9,576)", "B"),
    ((6, 8), 29790, 31680, "PSL(2,11) × Z_24", "k = 2, f = 0: 2+2+2", "d6D8_psl_11_24_orb2f0_s1", "(30,576)", "B"),
    ((7, 8), 80940, 95760, "PSL(2,19) × Z_14", "k = 3: 1+3+3", "d7D8_psl_19_14_orb3_s1", "✓", "B ×2"),
    ((8, 8), 201480, 239904, "PSL(2,17) × Z_49", "k = 3: 1+1+3+3", "d8D8_psl_17_49_orb3_s1", "✓", "B ×2"),
    ((9, 8), 449480, 540360, "PSL(2,19) × Z_79", "k = 3, f = 0: 3+3+3", "d9D8_psl_19_79_orb3_s1", "✓", "B ×2"),
    ((11, 8), 2246940, 2258520, "PSL(2,59) × Z_11", "k = 5: 1+5+5", "d11D8_psl_59_11_orb5_ORBW5_s3", "–", "B, I, P, G"),
    ((13, 8), 5314680, 6999552, "SL(2,7)² × Z_31", "k = 6 (swap): 1+6+6", "d13D8_prod_sl_7_sl_7_31_orb6swc_s2", "–", "B, G (+3 on a branch)"),
    ((15, 8), 14172480, 18128880, "SL(2,109) × Z_7", "k = 3, f = 0: 3+3+3+3+3", "d15D8_sl_109_7_orb3f0_s1", "–", "B, C, G"),
    ((5, 9), 27936, 29540, "Z_422 ⋊_5 Z_35", "–", "d5D9_meta_422_35_5_s204_n29540", "(28,560)", "B"),
    ((6, 9), 117360, 127296, "SL(2,17) × Z_13", "k = 3, f = 0: 3+3", "d6D9_sl_17_13_orb3f0_s2", "✓", "B ×2"),
    ((7, 9), 400160, 462840, "PSL(2,29) × Z_19", "k = 3: 1+3+3", "d7D9_psl_29_19_orb3_s1", "✓", "B ×3"),
    ((8, 9), 1091232, 1341600, "SL(2,25) × Z_43", "k = 3: 1+1+3+3", "d8D9_sl_25_43_orb3_s1", "–", "B"),
    ((9, 9), 2961536, 3499776, "PSL(2,7) × SL(2,7) × Z_31", "k = 3, f = 0: 3+3+3", "d9D9_prod_psl_7_sl_7_31_orb3f0_s1", "–", "B ×2, G"),
    ((10, 9), 7057400, 8003856, "SL(2,83) × Z_7", "k = 3: 1+3+3+3", "d10D9_sl_83_7_orb3_s1", "–", "B, I, C, C2, G"),
    ((11, 9), 15200448, 16792080, "SL(2,61) × Z_37", "k = 3: 1+1+3+3+3", "d11D9_sl_61_37_orb3_s1", "–", "B, I, C, C2, G"),
    ((12, 9), 30001152, 34026720, "SL(2,41) × Z_247", "k = 3, f = 0: 3+3+3+3", "d12D9_sl_41_247_orb3f0_s1", "–", "C, C2, G"),
    ((13, 9), 50990610, 67742688, "SL(2,103) × Z_31", "k = 3: 1+3+3+3+3", "d13D9_sl_103_31_orb3_s1", "–", "C, G"),
    ((14, 9), 95087738, 116068656, "SL(2,67) × Z_193", "k = 3: 1+1+3+3+3+3", "d14D9_sl_67_193_orb3_s1", "–", "C, C2, G"),
    ((15, 9), 168016334, 208029120, "SL(2,79) × Z_211", "k = 3, f = 0: 3+3+3+3+3", "d15D9_sl_79_211_orb3f0_s1", "–", "C, C2, G"),
    ((16, 9), 288939118, 337394400, "SL(2,151) × Z_49", "k = 3: 1+3+3+3+3+3", "d16D9_sl_151_49_orb3_s1", "–", "C, C2, G (note 3)"),
    ((4, 10), 11748, 12416, "Z_97 ⋊_19 Z_64", "–", "d4D10_n12416_haar_meta97_64_19", "✓", "A"),
    ((5, 10), 90068, 95472, "Z_1989 ⋊_461 Z_24", "–", "d5D10_n95472_haar_meta1989_24_461", "✓", "A"),
    ((6, 10), 452032, 524160, "SL(2,5) × PSL(2,7) × Z_13", "k = 3, f = 0: 3+3", "d6D10_prod_sl_5_psl_7_13_orb3f0_s1", "✓", "B ×2"),
    ((7, 10), 1987380, 2237760, "PSL(2,5) × SL(2,8) × Z_37", "k = 3: 1+3+3", "d7D10_prod_psl_5_sl_8_37_orb3_s15", "–", "B, G"),
    ((8, 10), 6927210, 7818096, "SL(2,67) × Z_13", "k = 3: 1+1+3+3", "d8D10_sl_67_13_orb3_s12", "–", "C, G"),
    ((9, 10), 20017260, 23975280, "PSL(2,71) × Z_67", "k = 3, f = 0: 3+3+3", "d9D10_psl_71_67_orb3f0_s1", "–", "P ×2, G"),
    ((10, 10), 50331156, 60141120, "SL(2,79) × Z_61", "k = 3: 1+3+3+3", "d10D10_sl_79_61_orb3_s1", "–", "C, C2, G"),
    ((11, 10), 130592354, 148729680, "PSL(2,89) × Z_211", "k = 5: 1+5+5", "d11D10_psl_89_211_orb5_ORBW5_s11", "–", "P, G"),
    ((12, 10), 300383050, 325832976, "SL(2,107) × Z_133", "k = 3, f = 0: 3+3+3+3", "d12D10_sl_107_133_orb3f0_s1", "–", "C, C2, G"),
    ((13, 10), 617330936, 677714400, "SL(2,199) × Z_43", "k = 3: 1+3+3+3+3", "d13D10_sl_199_43_orb3_s1", "–", "C, C2, G"),
    ((14, 10), 1213477190, 1326627120, "SL(2,139) × Z_247", "k = 3: 1+1+3+3+3+3", "d14D10_sl_139_247_orb3_FAST1_s1", "–", "C, C2, G"),
    ((15, 10), 2300326510, 2467618800, "SL(2,149) × Z_373", "k = 3, f = 0: 3+3+3+3+3", "d15D10_sl_149_373_orb3f0_s1", "–", "C, G"),
    ((16, 10), 4119507330, 4220872800, "SL(2,151) × Z_613", "k = 3: 1+3+3+3+3+3", "d16D10_sl_151_613_orb3_s1", "–", "C, G"),
]

# re-check logs; each has blocks "=== <header>" followed by result lines. The checker of a block is read from its
# header (program name), else it is the log's default.
LOGS = [("build_haar2.log", "B"), ("second.log", "I"), ("haarcheck_sl_psl.log", "C/P"), ("haarcheck2.log", "C2"),
        ("apsp.log", "A"), ("hc_factor.log", "F")]
ALIAS = {"(3,8) lift": "c1r_d3D8_n288_b2_3_0_aff302108_s1", "(4,10) meta": "d4D10_n12416_haar_meta97_64_19",
         "(5,10) meta": "d5D10_n95472_haar_meta1989_24_461", "meta 61 80 8": "d5D8_n9760_haar_meta61_80_8_s1",
         "meta 422 35 5": "d5D9_meta_422_35_5_s204_n29540"}


def checker(header, default, stem):
    if "apsp" in header:
        return "A"
    if "haarcheck2" in header:
        return "C2"
    if "hc_factor" in header:
        return "F"
    if "check_haar_indep" in header:
        return "I"
    if default == "C/P":
        return "P" if "psl" in stem else "C"
    return default


def session_checks():
    got = {}
    for name, default in LOGS:
        path = os.path.join(R, name)
        if not os.path.exists(path):
            continue
        stem, ok, lab = None, False, None
        for ln in open(path).read().split("\n") + ["=== end"]:
            if ln.startswith("==="):
                if stem and ok:
                    got.setdefault(stem, set()).add(lab)
                stem, ok = None, False
                m = re.search(r"(d\d+D\d+_[A-Za-z0-9_]+|c1r_[A-Za-z0-9_]+)", ln)
                if m:
                    stem = m.group(1)
                for k, v in ALIAS.items():
                    if k in ln:
                        stem = v
                if stem:
                    lab = checker(ln, default, stem)
                continue
            if stem is None:
                continue
            if "with D-1" in ln:          # what follows is the expected failure at diameter D - 1
                if not ok:
                    stem = None
                continue
            if not ok and re.search(r"\bINVALID\b", ln):
                stem = None
            elif re.search(r"(^|\s)VALID\b", ln):
                ok = True
    return got


def W(d, D):
    return sum((d - 1) ** j for j in range(D))


def main():
    got = session_checks()
    print("| cell | 2013 table | ours | gain | of Moore bound | group G | orbit structure of S (verified) | Lean | checks before today | this session |")
    print("|---|---:|---:|---:|---:|---|---|:---:|---|---|")
    for (d, D), t, o, g, st, stem, lean, earlier in ROWS:
        now = ", ".join(sorted(got.get(stem, set()), key=["B", "I", "C", "P", "C2", "F", "A"].index)) or "–"
        print(f"| ({d},{D}) | {t:,} | **{o:,}** | +{100 * (o / t - 1):.1f} % | {100 * o / (2 * W(d, D)):.1f} % | {g} | {st} | "
              f"{lean} | {earlier} | {now} |")


if __name__ == "__main__":
    main()
