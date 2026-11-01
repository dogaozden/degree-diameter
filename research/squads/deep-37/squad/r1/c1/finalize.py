"""c1 finalize: all solution files -> validity (bin/apsp 3 7), isomorphism classes (src/iso.py), |Aut|, girth.
usage: finalize.py  (reads squad/r1/c1/sol/*.edges, writes squad/r1/c1/classes.tsv and prints a summary)"""
import sys, os, glob, subprocess, collections, re, json
W = "/home/user/degree-diameter/research/squads/deep-37"
os.chdir(W); sys.path.insert(0, W + "/src")
from gutil import load, aut_gens, group_closure, bfs
from iso import certs
files = sorted(glob.glob("squad/r1/c1/sol/*.edges"))
valid, invalid = [], []
for f in files:
    out = subprocess.run(["bin/apsp", f, "3", "7"], capture_output=True, text=True).stdout
    (valid if "RESULT VALID" in out else invalid).append(f)
print("solution files:", len(files), "apsp VALID:", len(valid), "INVALID:", len(invalid), flush=True)
cs = certs(valid)
classes = collections.OrderedDict()
for f, c in zip(valid, cs):
    classes.setdefault(c, []).append(f)
rows = []
for c, fl in classes.items():
    rep = fl[0]
    n, E, adj = load(rep)
    gens, order, _ = aut_gens(adj)
    # girth: shortest cycle through BFS trees from every vertex
    girth = 10**9
    for s in range(n):
        dist = {s: 0}; par = {s: -1}; q = [s]
        for u in q:
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; par[w] = u; q.append(w)
                elif par[u] != w:
                    girth = min(girth, dist[u] + dist[w] + 1)
    grps = sorted(set(re.sub(r"_g_k\d+_\d+.*", "", os.path.basename(x)[len("n168_"):]) for x in fl))
    rows.append((c, len(fl), order, girth, rep, grps))
    print(f"class {len(rows)}: files {len(fl)} |Aut|={order} girth={girth} example={rep}", flush=True)
with open("squad/r1/c1/classes.tsv", "w") as fh:
    fh.write("class\tfiles\tAut\tgirth\tgroups\texample\n")
    for i, r in enumerate(rows, 1):
        fh.write(f"{i}\t{r[1]}\t{r[2]}\t{r[3]}\t{','.join(r[5])}\t{r[4]}\n")
print("iso classes:", len(rows))
