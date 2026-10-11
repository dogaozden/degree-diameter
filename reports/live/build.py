"""Build the live page's documents: one snapshot of the whole search, plus one 3D-laid-out graph per record.

Run from the repo root after `python reports/timeline/extract.py` (which refreshes the CSVs this reads).
Writes reports/live/out/now.json and reports/live/out/graph-<case>.json, and prints the ids of the documents
that changed since the last `--mark-pushed` run, one per line, as `live/now` or `graphs/<case>`.
"""
import csv, hashlib, json, sys
from collections import deque
from datetime import datetime, timezone
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
TL = ROOT / "reports/timeline"
OUT = ROOT / "reports/live/out"
OUT.mkdir(parents=True, exist_ok=True)
PUSHED = OUT / ".pushed.json"
YEARS = {"d4D5": "by 2009", "d5D5": "by 2009", "d7D5": "by 2009", "d7D4": "1984", "d11D4": "1984",
         "d11D3": "2013", "d13D3": "2021", "d15D3": "2021", "d6D5": "by 2009", "d16D3": "1985"}


def rows(name):
    with open(TL / f"{name}.csv", newline="") as f:
        return list(csv.DictReader(f))


def num(v):
    try:
        return int(v)
    except ValueError:
        try:
            return float(v)
        except ValueError:
            return v


def layout(n, edges, seed=7, iters=220):
    """3D layout: spectral start (Laplacian eigenvectors 1-3), then Fruchterman-Reingold, scaled to radius ~1."""
    A = np.zeros((n, n))
    e = np.array(edges)
    A[e[:, 0], e[:, 1]] = A[e[:, 1], e[:, 0]] = 1
    L = np.diag(A.sum(1)) - A
    w, v = np.linalg.eigh(L)
    pos = v[:, 1:4].copy()
    pos += np.random.default_rng(seed).normal(scale=1e-3, size=pos.shape)
    pos /= np.abs(pos).max()
    k = (1.0 / n) ** (1 / 3) * 1.6
    t = 0.12
    for i in range(iters):
        delta = pos[:, None, :] - pos[None, :, :]
        dist = np.sqrt((delta ** 2).sum(-1)) + 1e-9
        rep = (k * k / dist ** 2)[:, :, None] * delta
        disp = rep.sum(1)
        att = (A * dist / k)[:, :, None] * delta
        disp -= att.sum(1)
        length = np.sqrt((disp ** 2).sum(1)) + 1e-9
        pos += disp / length[:, None] * np.minimum(length, t)[:, None]
        pos -= pos.mean(0)
        t *= 0.985
    pos /= np.percentile(np.sqrt((pos ** 2).sum(1)), 95)
    return pos


def best_graph(case):
    files = [p for p in (ROOT / "records/bipartite_dd" / case).glob("*.json")]
    best = max(files, key=lambda p: int(p.name.split("-")[0]))
    rec = json.loads(best.read_text())
    n, edges = rec["output"]
    return best, n, [tuple(x) for x in edges]


def diameter_check(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    ecc = 0
    for s in range(n):
        d = [-1] * n; d[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x] + 1; q.append(y)
        ecc = max(ecc, max(d))
    return ecc, max(len(a) for a in adj)


records = rows("records")
fleet = rows("fleet")
now = {
    "as_of": fleet[0]["as_of"] if fleet else datetime.now(timezone.utc).isoformat(timespec="seconds"),
    "progress": [{k: num(v) for k, v in r.items()} for r in rows("progress")],
    "programs": [{k: num(v) for k, v in r.items()} for r in rows("programs")],
    "records": [{**{k: num(v) for k, v in r.items()}, "old_year": YEARS.get(r["case"], "")} for r in records],
    "fleet": [{k: num(v) if k not in ("cells", "best", "generation") else v for k, v in r.items()} for r in fleet],
    "lean": [{k: num(v) for k, v in r.items()} for r in rows("lean")],
    "milestones": rows("milestones"),
}
docs = {"live/now": now}
for r in records:
    case = r["case"]
    if not list((ROOT / "records/bipartite_dd" / case).glob("*.json")):
        continue  # no verified graph for this cell yet
    path, n, edges = best_graph(case)
    d, D = int(case[1:].split("D")[0]), int(case.split("D")[1])
    ecc, maxdeg = diameter_check(n, edges)
    assert ecc <= D and maxdeg <= d, (case, ecc, maxdeg)
    old = OUT / f"graph-{case}.json"
    if old.exists() and json.loads(old.read_text()).get("source") == path.name:
        docs[f"graphs/{case}"] = json.loads(old.read_text())
        continue
    pos = layout(n, edges)
    docs[f"graphs/{case}"] = {"case": case, "label": r["label"], "n": n, "d": d, "D": D, "table": int(r["table"]),
                              "source": path.name, "pos": [round(float(x), 3) for x in pos.ravel()],
                              "edges": [int(x) for e in edges for x in e]}
    print(f"laid out {case} n={n}", file=sys.stderr)

pushed = json.loads(PUSHED.read_text()) if PUSHED.exists() else {}
changed, digests = [], {}
for doc_id, body in docs.items():
    text = json.dumps(body, separators=(",", ":"), ensure_ascii=False)
    assert len(text.encode()) < 250_000, (doc_id, len(text))
    fname = "now.json" if doc_id == "live/now" else f"graph-{doc_id.split('/')[1]}.json"
    (OUT / fname).write_text(text)
    h = hashlib.sha256(text.encode()).hexdigest()
    digests[doc_id] = h
    if pushed.get(doc_id) != h:
        changed.append(doc_id)
VERSIONS = OUT / ".versions.json"  # store version of each document, needed as if_version on the next write
versions = json.loads(VERSIONS.read_text()) if VERSIONS.exists() else {}
if "--mark-pushed" in sys.argv:
    for c in changed:
        versions[c] = versions.get(c, 0) + 1
    VERSIONS.write_text(json.dumps(versions, indent=1))
    PUSHED.write_text(json.dumps(digests, indent=1))
else:
    for c in changed:
        print(c, versions.get(c, 0))
