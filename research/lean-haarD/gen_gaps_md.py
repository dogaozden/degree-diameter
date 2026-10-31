#!/usr/bin/env python3
"""Write research/lean-haarD/GAPS.md: every recorded (Delta, D) cell of the README table and research/RESULTS.md, with
its current record (the largest value either file gives), its construction, and whether master and this branch have a
Lean theorem for exactly that graph (same Delta, D and vertex count).

Lean theorems are read from the git trees (`git show REF:path`), so the master column is what master has.
usage: python3 research/lean-haarD/gen_gaps_md.py"""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
OUT = ROOT / "research/lean-haarD/GAPS.md"
BRANCH = "HEAD"


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout


def readme_records(text):
    out = {}
    for line in text.splitlines():
        if not re.match(r"^\| \(\d+, \d+\)", line):
            continue
        parts = line.split("|")
        cell = re.search(r"\((\d+), (\d+)\)", parts[1])
        d, D = int(cell.group(1)), int(cell.group(2))
        ours = int(parts[3].strip().strip("*").replace(",", ""))
        out[(d, D)] = (ours, parts[5].strip(), parts[6].strip())
    return out


def ledger_records(text):
    out = {}
    for line in text.splitlines():
        if not line.startswith("- Oct") or "PT" not in line:
            continue
        for m in re.finditer(r"\((\d+), ?(\d+)\) ([\d,]+)", line):
            key = (int(m.group(1)), int(m.group(2)))
            val = int(m.group(3).replace(",", ""))
            if key not in out or val > out[key][0]:
                note = line.split("):", 1)[-1].strip() if "):" in line else line
                out[key] = (val, note[:160])
    return out


NEW_CONSTRUCTION = {
    (3, 11): "voltage lift of a 4+4 cubic base over Z7 ⋊ Z24 = SmallGroup(168,1)",
    (3, 12): "voltage lift of a 4+4 cubic base over Z37 ⋊ Z8 = SmallGroup(296,3)",
    (4, 11): "orbit search (ledger: sl 8, poly x^3+x+1)",
    (4, 12): "orbit search (ledger: sl 11)",
    (5, 11): "orbit search (ledger: psl 19)",
    (5, 12): "orbit search (ledger: psl 97)",
    (6, 11): "orbit search (ledger: psl 47)",
    (6, 12): "orbit search (ledger: sl 71)",
    (7, 11): "orbit search (ledger: sl 43)",
    (7, 12): "orbit search (ledger: psl 163)",
    (8, 11): "orbit search (ledger: sl 89)",
    (8, 12): "orbit search (ledger: sl 163)",
    (18, 5): "file d18D5_n47600_W13_2dm_Z10 (doubled matching over Z10)",
    (19, 3): "file d19D3_n624_fourthhat_q17 (fourth hat)",
    (19, 4): "file d19D4_n10982_AS17_clones (clones of AS(17))",
    (19, 5): "file d19D5_n52428_W16_dm_Z6 (doubled matching over Z6)",
    (20, 5): "file d20D5_n75000_routechart_F5_Z20 (route-chart lift)",
    (17, 7): "hexagon constructions (typed whisker cover of H(13) with hubs)",
}


def lean_theorems(ref):
    """(Delta, D, vertices) of every record theorem `nb_*` under lean/ at `ref`."""
    found = []
    files = git("ls-tree", "-r", "--name-only", ref, "--", "lean").split()
    for f in files:
        if not f.endswith(".lean"):
            continue
        try:
            text = git("show", f"{ref}:{f}")
        except subprocess.CalledProcessError:
            continue
        for m in re.finditer(r"theorem (nb_\w+)\s*:(.*?):=", text, re.S):
            name, stmt = m.group(1), m.group(2)
            deg = re.search(r"IsBipartiteDegDiam\s+\w+\s+(\d+)\s+(\d+)", stmt)
            fin = re.search(r"Fin\s+(\d+)", stmt)
            if deg is None:
                continue
            n = int(fin.group(1)) if fin else None
            if n is None:
                suf = re.search(r"_(\d{3,})$", name)
                n = int(suf.group(1)) if suf else None
            found.append((int(deg.group(1)), int(deg.group(2)), n, name, f))
    return found


def edges_on_master(n):
    paths = git("ls-tree", "-r", "--name-only", "master").split()
    pat = re.compile(rf"(?<!\d){n}(?!\d)")
    hits = [p for p in paths if pat.search(p) and re.search(r"\.(edges|edges\.gz|txt|sol)$", p)]
    return hits


def main():
    readme = readme_records((ROOT / "README.md").read_text())
    ledger = ledger_records((ROOT / "research/RESULTS.md").read_text())
    cells = set(readme) | set(ledger)
    master_thms = lean_theorems("master")
    branch_thms = lean_theorems(BRANCH)

    def proofs(thms, d, D, n):
        return [name for (dd, DD, nn, name, _f) in thms if (dd, DD) == (d, D) and nn == n]

    rows = []
    for (d, D) in sorted(cells):
        rv = readme.get((d, D))
        lv = ledger.get((d, D))
        if rv and (not lv or rv[0] >= lv[0]):
            n, construction = rv[0], rv[1]
            source = "README"
        else:
            n = lv[0]
            construction = NEW_CONSTRUCTION.get((d, D), lv[1])
            source = "RESULTS"
        m_names = proofs(master_thms, d, D, n)
        b_names = proofs(branch_thms, d, D, n)
        rows.append((d, D, n, construction, source, m_names, b_names))

    lines = [
        "# Lean gaps: recorded graphs on master without a Lean proof",
        "",
        "Generated by research/lean-haarD/gen_gaps_md.py from the README table and research/RESULTS.md (the largest",
        "value either file gives for each (Δ, D) cell). \"Lean on master\" is what master's `lean/` tree proves for exactly",
        "that graph (same Δ, D and vertex count); \"Lean on this branch\" adds the proofs of this job (branch",
        "`claude/lean-gaps-proofs-3qf4j2`). The README's Lean column is stale in places (e.g. (9,5) shows a bracketed 2,758",
        "and (3,10) has no mark); the table below is computed from the Lean sources.",
        "",
        "| Cell (Δ, D) | Vertices | Construction | Source | Lean on master | Lean on this branch |",
        "|---|---:|---|---|---|---|",
    ]
    for d, D, n, construction, source, m_names, b_names in rows:
        m = ", ".join(f"yes (`{x}`)" for x in m_names) if m_names else "no"
        b = ", ".join(f"yes (`{x}`)" for x in b_names) if b_names else "no"
        if m_names and b_names and set(m_names) == set(b_names):
            b = "same"
        lines.append(f"| ({d}, {D}) | {n:,} | {construction} | {source} | {m} | {b} |")
    no_master = [r for r in rows if not r[5]]
    lines += ["", f"Cells with a record and no Lean proof on master: {len(no_master)} of {len(rows)}.", ""]

    lines += [
        "## Candidates for this job (vertices ≤ 12,000, Haar or regular voltage lift, edge list on master)",
        "",
        "| Cell | Vertices | Construction | Edge list on master | Status |",
        "|---|---:|---|---|---|",
    ]
    R = "research/"
    CANDIDATES = {
        (3, 10): (R + "squads/own-small/records/d3D10_n810_c3xheis27.edges", "regular voltage lift over C3 × He3",
                  "proved on this branch: `nb_3_10_810`"),
        (4, 7): (R + "theorems/smallfam/graphs/d4D7_n864_heis9xC16.edges.gz", "Haar graph of Heis(F₉) ⋊ C₁₆ (order 432)",
                 "proved on this branch: `nb_4_7_864`"),
        (3, 11): (R + "squads/own-small/records/d3D11_n1344_meta7_24.edges", "regular voltage lift over Z7 ⋊ Z24",
                  "proved on this branch: `nb_3_11_1344`"),
        (3, 12): (R + "squads/own-small/records/d3D12_n2368_meta37_8.edges", "regular voltage lift over Z37 ⋊ Z8",
                  "proved on this branch (staged): `nb_3_12_2368`"),
        (10, 5): (R + "d10D7/graphs/d10D5_n4800_gqdm_q7.edges.gz", "regular Z6 lift of the GQ(7) doubled-matching base",
                  "proved on this branch (staged): `nb_10_5_n4800`"),
        (11, 5): (R + "d10D7/graphs/d11D5_n7020_gqdm_q8.edges.gz", "regular Z6 lift of the GQ(8) doubled-matching base",
                  "proved on this branch (staged): `nb_11_5_n7020`"),
        (9, 5): (R + "selfdual-d5/records/d9D5_n3036_haar_c69c22.edges", "Haar graph of C69 : C22",
                 "proved on an earlier commit of this branch (`nb_9_5_n3036`), not on master"),
        (12, 5): (R + "d10D7/graphs/d12D5_n9840_gqdm_q9.edges.gz", "regular Z6 lift of the GQ(9) doubled-matching base",
                  "next candidate, not done in this job"),
        (13, 5): (R + "frontier/beyond/graphs/d13D5_n11700_W8_2dm_Z10.edges.gz",
                  "regular Z10 lift of the GQ(8) doubled-matching base", "next candidate, not done in this job"),
        (5, 8): ("none on master (sol file only: " + R + "frontier/sols/d5D8_n9760_haar_meta61_80_8_s1.txt)",
                 "Haar graph of the metacyclic group Z61 ⋊ Z80 (order 4880)", "not done: no edge list on master"),
        (8, 5): (R + "theorems/chartlift/graphs/d8D5_n2048.edges.gz",
                 "route-chart lift with affine fibre maps", "not done: not a plain regular voltage lift as built"),
    }
    small_gap = [r for r in rows if r[2] <= 12000 and not r[5]]
    rest = sorted((r[2], (r[0], r[1])) for r in rows if r[2] > 12000 and not r[5])
    min_rest = (f"({rest[0][1][0]}, {rest[0][1][1]})", rest[0][0])
    for d, D, n, construction, source, m_names, b_names in small_gap:
        if (d, D) in CANDIDATES:
            edges, cons, status = CANDIDATES[(d, D)]
            ef = f"`{edges}`"
            construction = cons
        else:
            ef = "—"
            status = "not a Haar graph or regular lift per its construction name; not done"
        lines.append(f"| ({d}, {D}) | {n:,} | {construction} | {ef} | {status} |")
    lines += [
        "",
        f"Every other gap cell has more than 12,000 vertices (the smallest is {min_rest[0]} with {min_rest[1]:,} vertices), "
        "so it is out of scope here.",
        "",
    ]
    OUT.write_text("\n".join(lines))
    print(f"wrote {OUT}: {len(rows)} cells, {len(no_master)} without a Lean proof on master, "
          f"{len(small_gap)} of them at most 12,000 vertices")


if __name__ == "__main__":
    main()
