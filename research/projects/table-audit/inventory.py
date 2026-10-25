"""Cell inventory for the table audit: one row per (Delta, D) of the published bipartite table.

Table values: research/frontier/heuristic.py TABLE, with (13,3) and (15,3) set to the wiki's 2022 values (274, 374)
as recorded in research/frontier/TABLE.md. Our best values: parsed from the README results table.
Writes cells.csv next to this file. Usage: python3 inventory.py  (run from anywhere; paths are repo-relative)."""
import csv, math, os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "research", "frontier"))
from heuristic import TABLE  # noqa: E402

TABLE = {d: list(row) for d, row in TABLE.items()}
TABLE[13][0] = 274   # wiki 2022 (TABLE.md); heuristic.py still has the 2013 survey value 270
TABLE[15][0] = 374   # wiki 2022 (TABLE.md); heuristic.py still has 370

def moore(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))

def prime_power(q):
    if q < 2:
        return False
    for p in range(2, q + 1):
        if q % p == 0:
            while q % p == 0:
                q //= p
            return q == 1
    return False

# Our best values from the README results table: "| (Delta, D) | Table | Ours | ..."
ours = {}
for line in open(os.path.join(ROOT, "README.md"), encoding="utf-8"):
    m = re.match(r"^\|\s*\((\d+),\s*(\d+)\)[^|]*\|\s*([\d,]+)\s*\|\s*\**([\d,]+)\**\s*\|", line)
    if m:
        d, D = int(m.group(1)), int(m.group(2))
        ours[(d, D)] = int(m.group(4).replace(",", ""))

# Holders recorded in TABLE.md (survey Table 4 + wiki colour key where read) and README "Where the old records come from".
HOLDER_OLD = {
    (4, 5): "Hafner; independently Loz (wiki colour key)",
    (5, 5): "Loz, Perez-Roses, Pineda-Villavicencio (Loz's project)",
    (7, 4): "Delorme-Farhi (graph duplication)",
    (11, 3): "Feria-Puron, Miller, Pineda-Villavicencio; independently Araujo-Pardo, Lopez",
    (13, 3): "Araujo-Pardo, Lopez (2022)",
    (15, 3): "Araujo-Pardo, Lopez (2022)",
    (11, 4): "Delorme-Farhi (graph duplication)",
    (7, 5): "Loz, Perez-Roses, Pineda-Villavicencio (Loz's computer-search project)",
}
SOURCE = "Miller-Sirán survey DS14v2 (2013) Table 4; wiki (Mar 2013 / Jan 2012 revisions)"

def status(d, D):
    if D in (3, 4, 6) and prime_power(d - 1) and d in (3, 4, 5, 6, 8, 9, 10, 12, 14) and D != 3 or \
       (D == 3 and d in (3, 4, 5, 6, 8, 9, 10, 12, 14)):
        return "M"
    if (d, D) in ((3, 5), (7, 3)):
        return "opt"
    return "open"

rows = []
for D in range(3, 11):
    for d in range(3, 17):
        t = TABLE[d][D - 3]
        if t is None:
            rows.append(dict(delta=d, D=D, table="", moore="", status="unreadable", ours="", beaten="",
                             holder="", source="", notes="wiki cell unreadable in the survey PDF text (TABLE.md)"))
            continue
        st = status(d, D)
        mb = moore(d, D)
        o = ours.get((d, D), "")
        beaten = "" if st != "open" else ("yes" if o and o > t else "no")
        holder = HOLDER_OLD.get((d, D), "")
        if st == "M":
            holder = "Moore graph (incidence graph of a generalized polygon)"
        elif st == "opt":
            holder = "optimal (proof: Jorgensen (3,5); Feria-Puron, Miller, Pineda-Villavicencio (7,3))"
        elif not holder:
            holder = "not traced (survey attributes D>=5 mostly to Loz / Perez-Roses / Pineda-Villavicencio lifts)"
        rows.append(dict(delta=d, D=D, table=t, moore=mb, status=st, ours=o, beaten=beaten,
                         holder=holder, source=SOURCE, notes=""))
        assert t <= mb, (d, D, t, mb)

out = os.path.join(os.path.dirname(__file__), "cells.csv")
with open(out, "w", newline="", encoding="utf-8") as f:
    w = csv.DictWriter(f, fieldnames=["delta", "D", "table", "moore", "status", "ours", "beaten", "holder", "source", "notes"])
    w.writeheader()
    w.writerows(rows)
from collections import Counter
print(Counter(r["status"] for r in rows), "beaten:", Counter(r["beaten"] for r in rows))
print("cells:", len(rows), "ours parsed:", len(ours))
print("unbeaten open:", [(r["delta"], r["D"]) for r in rows if r["beaten"] == "no"])
