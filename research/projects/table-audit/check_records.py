"""Re-check the record graphs in records/bipartite_dd with apsp.c (all-pairs BFS, independent of how they were built).

Each graph file is turned into a plain edge list ("n", then "u v" per line) in a scratch directory, then checked with
  apsp EDGES Delta D [threads]
where Delta and D are read from the directory name dDELTA D DIAM (e.g. d11D4 -> Delta 11, D 4).
Accepted inputs: the JSON records (output = [n, [[u, v], ...]]), and the plain edge lists (*.edges.txt, *.edges.txt.gz).
Haar-built files (*.solution.txt) are not read here: their .edges.txt.gz twin is used instead.

Usage: python3 check_records.py APSP_BINARY SCRATCH_DIR [THREADS] [SIZE_LIMIT] [DIR ...]
  SIZE_LIMIT (vertices): skip graphs bigger than this (default: no limit).
Writes records_check.csv next to this file (one row per graph; rows for the big gz files are appended as they finish).
"""
import csv
import glob
import gzip
import json
import os
import re
import subprocess
import sys
import time

REC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "records", "bipartite_dd")
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "records_check.csv")


def read_graph(path):
    """Return (n, edges) for a record file."""
    if path.endswith(".json"):
        out = json.load(open(path))["output"]
        return out[0], [tuple(e) for e in out[1]]
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt") as f:
        lines = [line.strip() for line in f if line.strip()]
    header = [l for l in lines if l.startswith("#")]
    body = [l for l in lines if not l.startswith("#")]
    if len(body[0].split()) == 1:  # "n" line, then "u v" lines (the .gz lists)
        n, body = int(body[0]), body[1:]
    else:  # ".edges.txt" with a comment header "# n=... edges=..."
        n = int(re.search(r"n=(\d+)", " ".join(header)).group(1))
    edges = [tuple(map(int, line.split())) for line in body]
    return n, edges


def check(apsp, scratch, path, threads):
    m = re.search(r"d(\d+)D(\d+)", path)
    delta, D = int(m.group(1)), int(m.group(2))
    n, edges = read_graph(path)
    tmp = os.path.join(scratch, os.path.basename(path).split(".")[0] + ".edges")
    with open(tmp, "w") as f:
        f.write(f"{n}\n")
        f.writelines(f"{u} {v}\n" for u, v in edges)
    t0 = time.time()
    res = subprocess.run([apsp, tmp, str(delta), str(D), str(threads)], capture_output=True, text=True)
    os.remove(tmp)
    lines = res.stdout.strip().splitlines()
    info = next((l for l in lines if l.startswith("n=")), "")
    verdict = next((l for l in lines if l.startswith("RESULT")), "RESULT NO OUTPUT")
    return dict(file=os.path.relpath(path, REC), delta=delta, D=D, n=n, edges=len(edges), verdict=verdict,
                info=info, seconds=round(time.time() - t0, 1))


def main():
    apsp, scratch = sys.argv[1], sys.argv[2]
    threads = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    limit = int(sys.argv[4]) if len(sys.argv) > 4 else None
    dirs = sys.argv[5:] or sorted(glob.glob(os.path.join(REC, "d*")))
    rows = []
    for d in dirs:
        d = d if os.path.isabs(d) else os.path.join(REC, os.path.basename(d))
        files = sorted(glob.glob(os.path.join(d, "*.json")) + glob.glob(os.path.join(d, "*.edges.txt")) +
                       glob.glob(os.path.join(d, "*.edges.txt.gz")))
        for path in files:
            if "program" in path:
                continue
            if limit is not None and path.endswith(".json"):
                n = json.load(open(path))["output"][0]
                if n > limit:
                    continue
            r = check(apsp, scratch, path, threads)
            rows.append(r)
            print(r["file"], r["n"], r["verdict"], r["info"], f'{r["seconds"]}s', flush=True)
    with open(OUT, "a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["file", "delta", "D", "n", "edges", "verdict", "info", "seconds"])
        if f.tell() == 0:
            w.writeheader()
        w.writerows(rows)


if __name__ == "__main__":
    main()
