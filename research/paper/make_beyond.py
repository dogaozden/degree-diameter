"""Table rows for BEYOND.md, and the PDF.

    python3 research/paper/make_beyond.py          # rewrite the table between the TABLE markers in BEYOND.md
    python3 research/paper/make_beyond.py --pdf    # also BEYOND.tex (pandoc) and BEYOND.pdf (tectonic)

Set TECTONIC=/path/to/tectonic if tectonic is not on the PATH. Every value below was copied from the files named in
BEYOND.md, section 2; the vertex counts are re-derived from the group orders and formulas by --verify.
"""
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Check abbreviations (legend in BEYOND.md): gen, sl, psl, h2, ind, bh2, mc, apsp, auto, samp; † = run by this job.
M = "master"
ROWS = [
    # Δ, D, value, construction, group or base graph, check, where
    (17, 5, 35728, "route-chart lift + 1,936 hubs (88 Z₂₂-orbits)", "(16,5) graph: K₃,₃ + doubled matching, Z₂₂, fibre F₄⁴", "apsp, bfs_all; apsp†", "branch ᵃ"),
    (18, 5, 47600, "multi-doubled-matching lift", "W(13); 2 doubled matchings; Z₂ × Z₅", "apsp; coord. apsp", M),
    (19, 5, 52428, "doubled-matching lift", "W(16); Z₆", "apsp; coord. apsp", M),
    (20, 5, 75000, "route-chart lift over F₅", "K₃,₃ + doubled matching, Z₂₀, fibre F₅⁴", "apsp; coord. apsp", M),
    (17, 6, 2236962, "Moore graph", "H(16)", "classical; auto", "branch"),
    (18, 6, 3017196, "Moore graph", "H(17)", "classical; auto", "branch"),
    (19, 6, 3203968, "Theorem D, q = 17, m = 2", "H(17) doubled with levels and whiskers", "theorem (Lean); auto", "branch"),
    (20, 6, 5227320, "Moore graph", "H(19)", "classical; auto", "branch"),
    (17, 7, 5693959, "typed whisker cover + hubs", "H(13); 32,356 + 30,327 hubs", "coord. apsp; apsp (8 ranges)", M),
    (18, 7, 7240212, "level graph", "9 copies of H(13), 4 matchings, Z₉", "theorem; samp", "branch ᵇ"),
    (19, 7, 11184810, "level graph", "5 copies of H(16), 2 matchings, Z₅", "theorem; samp", "branch ᵇ"),
    (20, 7, 15658734, "level graph", "7 copies of H(16), 3 matchings, Z₇", "theorem; samp", "branch ᵇ"),
    (17, 8, 41373072, "Haar, orbit S", "SL(2,53) × Z₁₃₉", "sl + h2", M),
    (18, 8, 57637680, "Haar, orbit S", "SL(2,61) × Z₁₂₇", "sl + h2", M),
    (19, 8, 86317296, "Haar, orbit S", "PSL(2,103) × Z₇₉", "psl + ind", M),
    (20, 8, 122739120, "Haar, orbit S", "PSL(2,71) × Z₃₄₃", "psl + ind", M),
    (17, 9, 501707400, "Haar, orbit S", "PSL(2,101) × Z₄₈₇", "psl + ind", M),
    (18, 9, 790626816, "Haar, orbit S", "SL(2,127) × Z₁₉₃", "sl + h2", M),
    (19, 9, 1218394320, "Haar, orbit S", "SL(2,131) × Z₂₇₁", "sl + h2", M),
    (20, 9, 1823175864, "Haar, orbit S", "PSL(2,163) × Z₄₂₁", "psl + gen", M),
    (17, 10, 7022052336, "Haar, orbit S", "PSL(2,313) × Z₂₂₉", "psl + gen", M),
    (18, 10, 11787972672, "Haar, orbit S", "PSL(2,223) × Z₁₀₆₃", "psl + gen", M),
    (19, 10, 19233722496, "Haar, orbit S", "SL(2,607) × Z₄₃", "sl + gen", M),
    (20, 10, 30518778360, "Haar, orbit S", "PSL(2,421) × Z₄₀₉", "psl (2 halves) + gen", M),
    (3, 11, 1474, "Haar, all pairs {x, y} searched", "Z₆₇ ⋊₉ Z₁₁", "apsp; apsp†", "branch ᶜ"),
    (4, 11, 30334, "Haar, random S", "Z₅₂₃ ⋊₉ Z₂₉ (Frobenius)", "bh2 + apsp", M),
    (5, 11, 311426, "Haar, random S", "Z₅₀₂₃ ⋊₂₈₈₆ Z₃₁ (Frobenius)", "bh2 + apsp", M),
    (6, 11, 2122518, "Haar, random S", "Z₂₀₈₀₉ ⋊₁₂₉₇₂ Z₅₁ (Frobenius)", "bh2; mc†", M),
    (7, 11, 11012976, "Haar, orbit S", "SL(2,53) × Z₃₇", "gen + sl", M),
    (8, 11, 45329808, "Haar, orbit S", "SL(2,283)", "gen + sl", M),
    (9, 11, 155250816, "Haar, orbit S", "SL(2,223) × Z₇", "gen + sl", M),
    (10, 11, 460691568, "Haar, orbit S", "SL(2,613)", "gen + sl", M),
    (11, 11, 1241299248, "Haar, orbit S", "SL(2,853)", "gen + sl", M),
    (12, 11, 2976066240, "Haar, orbit S", "SL(2,239) × Z₁₀₉", "gen + sl", M),
    (13, 11, 6781213392, "Haar, orbit S", "SL(2,563) × Z₁₉", "gen + sl", M),
    (14, 11, 14381398080, "Haar, orbit S", "SL(2,1009) × Z₇", "gen + sl", M),
    (15, 11, 28655908512, "Haar, orbit S", "SL(2,617) × Z₆₁", "gen + sl (2 halves)", M),
    (16, 11, 29961590400, "Haar, orbit S (size cap)", "PSL(2,449) × Z₃₃₁", "gen only", "branch ᵈ"),
    (3, 12, 2368, "voltage lift", "cubic 4 + 4-vertex base; Z₃₇ ⋊ Z₈ = SmallGroup(296,3)", "coord. rebuild + apsp", M),
    (4, 12, 74066, "Haar, random S", "Z₁₂₇₇ ⋊₉₆₄ Z₂₉", "apsp + mc; coord. apsp", M),
    (5, 12, 1058342, "Haar, random S", "Z₈₉₆₉ ⋊₂₀₅ Z₅₉ (Frobenius)", "bh2; mc†", M),
    (6, 12, 9366240, "Haar, orbit S", "PSL(2,79) × Z₁₉", "gen + psl", M),
    (7, 12, 59838504, "Haar, orbit S", "PSL(2,67) × Z₁₉₉", "gen + psl", M),
    (8, 12, 284095056, "Haar, orbit S", "PSL(2,167) × Z₆₁", "gen + psl", M),
    (9, 12, 1105785120, "Haar, orbit S", "PSL(2,241) × Z₇₉", "gen + psl", M),
    (10, 12, 3712424352, "Haar, orbit S", "PSL(2,337) × Z₉₇", "gen + psl", M),
    (11, 12, 11189148096, "Haar, orbit S", "PSL(2,223) × Z₁₀₀₉", "gen + psl", M),
    (12, 12, 29996171040, "Haar, orbit S", "PSL(2,241) × Z₂₁₄₃", "gen + psl (2 halves)", M),
    (13, 12, 29997644040, "Haar, orbit S (size cap)", "PSL(2,181) × Z₅₀₅₉", "gen + psl (2 halves)", M),
    (14, 12, 29996171040, "Haar, orbit S (size cap)", "PSL(2,241) × Z₂₁₄₃", "gen + psl (2 halves)", M),
    (3, 13, 3400, "cyclic voltage lift", "Desargues graph GP(10,3); Z₁₇₀", "apsp; coord. apsp", M),
    (4, 13, 192382, "Haar, random S", "Z₂₂₃₇ ⋊₁₉₈₄ Z₄₃ (Frobenius)", "apsp + mc; coord. apsp", M),
    (5, 13, 3594910, "Haar, random S", "(Z₁₁ ⋊₄ Z₅) × (Z₂₉₇₁ ⋊₁₇₆₄ Z₁₁)", "mc; bh2†", "branch"),
    (6, 13, 41734392, "Haar, orbit S", "PSL(2,83) × Z₇₃", "gen; psl†", "branch"),
    (7, 13, 312227760, "Haar, orbit S", "SL(2,229) × Z₁₃", "gen; sl†", "branch"),
    (8, 13, 1739514000, "Haar, orbit S", "SL(2,499) × Z₇", "gen; sl†", "branch"),
    (9, 13, 7924036032, "Haar, orbit S", "SL(2,593) × Z₁₉", "gen; sl†", "branch"),
    (10, 13, 19980294768, "Haar, orbit S (size cap)", "PSL(2,503) × Z₁₅₇", "gen only", "branch ᵈ"),
    (3, 14, 5706, "cyclic voltage lift", "Pappus graph; Z₃₁₇", "apsp; coord. apsp", M),
    (4, 14, 497042, "Haar, random S", "Z₂₇₃₁ ⋊₂₄₀₀ Z₉₁", "apsp + mc; coord. apsp", M),
    (5, 14, 12795166, "Haar, random S", "Z₁₄₈₇₈₁ ⋊₈₅₁₇₅ Z₄₃", "mc; bh2†", "branch"),
    (6, 14, 187990656, "Haar, orbit S", "SL(2,97) × Z₁₀₃", "gen; sl†", "branch"),
    (7, 14, 1674490944, "Haar, orbit S", "PSL(2,223) × Z₁₅₁", "gen; psl†", "branch"),
    (8, 14, 11325238056, "Haar, orbit S", "PSL(2,397) × Z₁₈₁", "gen; psl†", "branch"),
]

SUB = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")


def moore(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))


def hexagon(q):
    return 2 * (q + 1) * (q ** 4 + q ** 2 + 1)


def verify():
    """Re-derive each vertex count from its group order or formula."""
    bad = 0
    for d, D, v, con, grp, chk, wh in ROWS:
        g = grp.translate(SUB)
        want = None
        m = re.fullmatch(r"(P?SL)\(2,(\d+)\)(?: × Z(\d+))?", g)
        if m:
            p, n = int(m.group(2)), int(m.group(3) or 1)
            want = 2 * p * (p * p - 1) * n // (2 if m.group(1) == "PSL" else 1)
        elif "⋊" in g and "base" not in g:
            want = 2
            for a, b in re.findall(r"Z(\d+) ⋊\d* Z(\d+)", g):
                want *= int(a) * int(b)
        elif con == "Moore graph":
            want = hexagon(int(re.search(r"H\((\d+)\)", g).group(1)))
        elif con == "level graph":
            c, q = re.search(r"(\d+) copies of H\((\d+)\)", g).groups()
            want = int(c) * hexagon(int(q))
        elif con.startswith("typed whisker cover"):
            want = 7 * hexagon(13) + 32356 + 30327
        elif con.startswith("Theorem D"):
            q = 17
            want = hexagon(q) + 2 * q ** 4 + 4 * q ** 3 + 4 * q + 10
        elif "doubled-matching" in con:
            q = int(re.search(r"W\((\d+)\)", g).group(1))
            k = 2 if "2 doubled" in g else 1
            want = 4 * (2 * k + 1) * (q + 1) * (q * q + 1)
        elif con == "route-chart lift over F₅":
            want = 2 * 60 * 5 ** 4
        elif con.startswith("route-chart lift +"):
            want = 2 * 66 * 4 ** 4 + 88 * 22
        elif "voltage lift" in con:
            base = {"Desargues": 20, "Pappus": 18}
            for k, nb in base.items():
                if k in g:
                    want = nb * int(re.search(r"Z(\d+)$", g).group(1))
            if "SmallGroup(296,3)" in g:
                want = 8 * 296
        ok = want is None or want == v
        bad += not ok
        print(f"({d},{D}) {v:,} {'' if want is None else ('ok' if ok else f'MISMATCH {want:,}')} "
              f"{100 * v / moore(d, D):.2f}% of the Moore bound")
    return bad


def md_table():
    out = ["| (Δ, D) | value | construction | group or base graph | check | where |",
           "|:-------|--------------:|:---------------------------|:-----------------------------------|"
           ":-----------------------|:-----------|"]
    for d, D, v, con, grp, chk, wh in ROWS:
        out.append(f"| ({d}, {D}) | {v:,} | {con} | {grp} | {chk} | {wh} |")
    return "\n".join(out)


def splice():
    p = HERE / "BEYOND.md"
    s = p.read_text()
    new = re.sub(r"(<!-- TABLE -->\n).*?(\n<!-- /TABLE -->)", lambda m: m.group(1) + md_table() + m.group(2), s,
                 flags=re.S)
    p.write_text(new)


HEADER = r"""
\usepackage{fontspec}
\setmainfont{DejaVu Serif}[Scale=0.92]
\setsansfont{DejaVu Sans}[Scale=0.92]
\setmonofont{DejaVu Sans Mono}[Scale=0.84]
\usepackage{etoolbox}
\AtBeginEnvironment{longtable}{\scriptsize\setlength{\tabcolsep}{3pt}}
\usepackage{microtype}
\usepackage{newunicodechar}
\newunicodechar{⋊}{\ensuremath{\rtimes}}
\newunicodechar{∎}{\ensuremath{\square}}
\setlength{\emergencystretch}{3em}
\renewcommand{\arraystretch}{1.12}
"""


def pdf():
    tex = HERE / "BEYOND.tex"
    hdr = HERE / ".beyond_header.tex"
    hdr.write_text(HEADER)
    subprocess.run(["pandoc", str(HERE / "BEYOND.md"), "-s", "-o", str(tex), "--columns=118",
                    "-V", "geometry:margin=0.8in", "-V", "fontsize=10pt", "-V", "colorlinks=true",
                    "-H", str(hdr)], check=True)
    hdr.unlink()
    s = tex.read_text()
    s = s.replace("\\usepackage{lmodern}\n", "")
    tex.write_text(s)
    subprocess.run([os.environ.get("TECTONIC", "tectonic"), str(tex)], cwd=HERE, check=True)


if __name__ == "__main__":
    if verify():
        sys.exit("vertex count mismatch")
    splice()
    if "--pdf" in sys.argv:
        pdf()
