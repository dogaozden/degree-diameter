"""Summarize runs/*.tsv (written by run_cell.py) per cell: jobs, orders tried, best cost per order, solved orders.

Usage: python3 summarize.py [TAG_PREFIX...]     prints a markdown table per cell (Delta, D)
"""
import glob
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
TABLE = {(6, 5): 684, (3, 7): 168, (4, 7): 840, (5, 7): 3110, (3, 8): 256, (4, 8): 2184, (5, 8): 9234,
         (3, 9): 506, (4, 9): 4970, (5, 9): 27936, (3, 10): 800, (4, 10): 11748, (5, 10): 90068}


def main():
    pref = sys.argv[1:] or [""]
    cells = defaultdict(list)
    for fn in sorted(glob.glob(os.path.join(HERE, "runs", "*.tsv"))):
        tag = os.path.basename(fn)[:-4]
        if tag.endswith(".screen") or not any(tag.startswith(p) for p in pref):
            continue
        m = re.search(r"d(\d+)D(\d+)", tag)
        if not m:
            continue
        cell = (int(m.group(1)), int(m.group(2)))
        for line in open(fn):
            w = line.rstrip("\n").split("\t")
            if len(w) < 7 or w[4] == "None":
                continue
            cells[cell].append(dict(tag=tag, n=int(w[0]), h=int(w[1]), base=w[2], group=w[3], best=int(w[4]),
                                    evals=int(w[5]), secs=float(w[6])))
    print("| cell | table | jobs | CPU h | orders tried | solved above table | above the best solved order |")
    print("|---|---|---|---|---|---|---|")
    for cell in sorted(cells, key=lambda c: (c[1], c[0])):
        rs = cells[cell]
        tab = TABLE.get(cell, 0)
        orders = sorted(set(r["n"] for r in rs))
        solved = sorted(set(r["n"] for r in rs if r["best"] == 0 and r["n"] > tab))
        top = max(solved) if solved else tab
        uns = [o for o in orders if o > top]
        if uns:
            b = min((r for r in rs if r["n"] in uns), key=lambda r: (r["best"], r["n"]))
            bdesc = f"lowest cost above {top}: {b['best']} at n = {b['n']} (h={b['h']}, {b['base']}, {b['group']})"
        else:
            bdesc = "-"
        cpu = sum(r["secs"] for r in rs) / 3600
        print(f"| ({cell[0]},{cell[1]}) | {tab} | {len(rs)} | {cpu:.1f} | {orders[0]}–{orders[-1]} ({len(orders)}) | "
              f"{', '.join(map(str, solved)) or 'none'} | {bdesc} |")


if __name__ == "__main__":
    main()
