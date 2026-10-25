"""Assemble audit.csv (one row per cell of the published bipartite table) from the pieces of this audit.

Inputs (all in this folder unless noted):
  cells.csv          from inventory.py: table value, Moore bound, status, our best value, beaten, holder
  moore_results.txt  apsp lines for the Moore-bound cells (check_moore.sh / this session's runs)
  records_check.csv  apsp results for graph files found in the repo (check_records.py)
Output: audit.csv with columns
  delta, D, table, status, holder, ours, graph_file, n, rebuilt, check, notes

rebuilt = yes  : a graph of order >= the table value was rebuilt from a file in the repo or from a generator here, and
                 apsp.c (or apsp_mt.c) reported VALID for it.
rebuilt = no   : no such graph was checked. The notes say why (no file, unreadable cell, no traceable construction).
"""
import csv
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))


def load_moore():
    out = {}
    for line in open(os.path.join(HERE, "moore_results.txt"), encoding="utf-8"):
        m = re.match(r"D=(\d+) q=(\d+)\s+Delta=(\d+)\s+n=(\d+):\s+RESULT (VALID|INVALID)", line)
        if m:
            D, q, d, n, verdict = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)), m.group(5)
            out[(d, D)] = dict(n=n, verdict=verdict, file="generated: moore.py (D=3,4) / research/evenq/hexq.py (D=6)")
    return out


def load_records():
    out = {}
    path = os.path.join(HERE, "records_check.csv")
    if not os.path.exists(path):
        return out
    for r in csv.DictReader(open(path, encoding="utf-8")):
        key = (int(r["delta"]), int(r["D"]))
        out.setdefault(key, []).append(r)
    return out


def main():
    cells = list(csv.DictReader(open(os.path.join(HERE, "cells.csv"), encoding="utf-8")))
    moore = load_moore()
    records = load_records()
    rows = []
    for c in cells:
        d, D = int(c["delta"]), int(c["D"])
        row = dict(delta=d, D=D, table=c["table"], status=c["status"], holder=c["holder"], ours=c["ours"],
                   graph_file="", n="", rebuilt="no", check="not run", notes="")
        if c["status"] == "unreadable":
            row["notes"] = "table cell unreadable in the survey PDF text; no value assumed; no construction traced"
        elif c["status"] == "M":
            m = moore.get((d, D))
            if m:
                row.update(graph_file=m["file"], n=m["n"], rebuilt="yes" if m["verdict"] == "VALID" else "no",
                           check=m["verdict"])
                if str(m["n"]) != c["table"]:
                    row["notes"] = "order mismatch with table"
            else:
                row["notes"] = "Moore graph not rebuilt in this session"
        else:
            cands = [r for r in records.get((d, D), []) if int(r["n"]) >= int(c["table"] or 0)]
            valid = [r for r in cands if "VALID" in r["verdict"] and "INVALID" not in r["verdict"]]
            if valid:
                best = max(valid, key=lambda r: int(r["n"]))
                row.update(graph_file=best["file"], n=best["n"], rebuilt="yes", check=best["verdict"])
                row["notes"] = ("our record exceeds the table value; the table's own construction was not traced"
                                if c["beaten"] == "yes" else "")
            elif c["beaten"] == "yes":
                row["notes"] = "beaten by our record, but its graph file was not re-checked in this session"
            else:
                row["notes"] = "not beaten and no graph of this order found in the repo; construction not traced"
        if c["status"] == "opt":
            row["notes"] = (row["notes"] + "; " if row["notes"] else "") + "proved optimal in the literature"
        rows.append(row)
    fields = ["delta", "D", "table", "status", "holder", "ours", "graph_file", "n", "rebuilt", "check", "notes"]
    with open(os.path.join(HERE, "audit.csv"), "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)
    from collections import Counter
    print(Counter(r["rebuilt"] for r in rows))


if __name__ == "__main__":
    main()
