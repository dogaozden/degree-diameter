"""Option A for a failing pair of a DM state: change ONE copy of the matching edge at a vertex near the failure to a
Z3-zero voltage (0 or 3), i.e. turn it into an extra base edge.  Scores every choice with z6lift (exact).
usage: python3 halfdouble.py base.in volt_file v1 v2 [radius]   (v = base vertex ids; lines n + l)"""
import sys, subprocess, os
base, volt, v1, v2 = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]); rad = int(sys.argv[5]) if len(sys.argv) > 5 else 0
f = open(base).read().split(); n, dg = int(f[0]), int(f[1]); NF = n * dg
ln = [list(map(int, f[2 + l * dg:2 + (l + 1) * dg])) for l in range(n)]; sig = list(map(int, f[2 + NF:2 + NF + n]))
sinv = [0] * n
for p, l in enumerate(sig): sinv[l] = p
eg = list(map(int, open(volt).read().split()))
# candidate points: within distance rad of v1/v2 (as base vertices), plus sigma partners
adj = [[] for _ in range(2 * n)]
for l in range(n):
    for p in ln[l]: adj[p].append(n + l); adj[n + l].append(p)
S = {v1, v2}; fr = set(S)
for _ in range(rad):
    fr = {y for x in fr for y in adj[x]} - S; S |= fr
pts = sorted({v if v < n else sinv[v - n] for v in S})
tmp = os.environ.get("TMPD", "/tmp")
res = []
for p in pts:
    for c in range(2):
        for val in (0, 3):
            e = NF + 2 * p + c; g = eg[:]; g[e] = val
            fn = f"{tmp}/hd_{p}_{c}_{val}.volt"; open(fn, "w").write("\n".join(map(str, g)) + "\n")
            out = subprocess.run(["/tmp/z6", base], env=dict(os.environ, SCORE="1", VOLT=fn), capture_output=True, text=True).stdout
            cst = int(out.split("cost ")[1].split(",")[0]); res.append((cst, p, c, val)); os.remove(fn)
res.sort(); print("candidates", len(res)); print(res[:15])
