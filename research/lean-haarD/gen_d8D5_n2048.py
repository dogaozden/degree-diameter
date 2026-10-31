#!/usr/bin/env python3
"""Generate the Lean proof of the (8,5) record on 2048 vertices (route-chart lift, gaps job, see GAPS.md).

Steps, all from the edge file research/theorems/chartlift/graphs/d8D5_n2048.edges.gz:
  1. read it, check it: 8-regular, simple, bipartite, every two vertices within 5 steps (bitset check),
  2. write lean/BipartiteDD/Haar/D8D5N2048/Graph.lean (neighbour lists, colours) and copy the edge file there,
  3. read Graph.lean back and assert that its lists equal the edge file,
  4. write the staged modules (Levels, Level01 … Level04, Stage00 … Stage04, Check, Record) with
     research/lean-haarD/gen_staged_lift.py. For n < 5000 the local test is one module (Check).

usage: python3 research/lean-haarD/gen_d8D5_n2048.py
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import gen_lift_gaps as glg  # noqa: E402
import gen_staged_lift as gsl  # noqa: E402

ROOT = glg.ROOT
REC = dict(n=2048, d=8, D=5, K=11, folder="D8D5N2048", theorem="nb_8_5_n2048",
           edges=ROOT / "research/theorems/chartlift/graphs/d8D5_n2048.edges.gz")


def main():
    rec = REC
    n, edges = glg.read_edges(rec["edges"])
    assert n == rec["n"]
    adj = glg.neighbour_lists(n, edges)
    col = glg.two_colour(n, adj)
    diam = glg.check_record(rec, n, edges, adj, col)
    glg.write_graph(rec, n, adj, col, rec["folder"])
    lists, cols, lean_edges = glg.read_back(rec, n, glg.OUT / rec["folder"] / "Graph.lean")
    assert lean_edges == sorted({tuple(sorted(e)) for e in edges}), "Lean lists differ from the edge file"
    assert lists == adj and cols == col
    print(f"{rec['folder']}: n={n} d={rec['d']} diameter={diam} <= D={rec['D']}, Lean lists equal the edge file")
    gsl.main(rec["folder"], rec["theorem"], n, rec["d"], rec["D"], rec["K"], rec["edges"])


if __name__ == "__main__":
    main()
