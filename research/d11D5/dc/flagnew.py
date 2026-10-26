"""Exhaustive targeted flag swaps between new lines (ids >= 585) and lines containing a new point: (p in N, p' in L) ->
(p' in N, p in L).  Prints the best few.  usage: flagnew.py base.in [out.in]"""
import sys, subprocess, os, tempfile
t = open(sys.argv[1]).read().split(); n, dg = int(t[0]), int(t[1])
ln = [[int(x) for x in t[2+l*dg:2+l*dg+dg]] for l in range(n)]; sig = t[2+n*dg:2+n*dg+n]
def wr(fn, L):
    with open(fn, "w") as f:
        f.write(f"{n} {dg}\n")
        for l in L: f.write(" ".join(map(str, l)) + "\n")
        f.write("\n".join(sig) + "\n")
def score(fn):
    o = subprocess.run(["/tmp/po7", fn], env={"SCORE": "1"}, capture_output=True, text=True).stdout
    return int(o.split("cost=")[1].split()[0])
NEW = list(range(585, n)); SW = [l for l in range(585) if any(p >= 585 for p in ln[l])]
tmp = "fn_tmp.in"; wr(tmp, ln); base = score(tmp); res = []
for N in NEW:
    for L in SW:
        for p in ln[N]:
            if p >= 585 or p in ln[L]: continue
            for q in ln[L]:
                if q >= 585 or q in ln[N]: continue
                L2 = [l[:] for l in ln]
                L2[N] = [q if x == p else x for x in L2[N]]; L2[L] = [p if x == q else x for x in L2[L]]
                wr(tmp, L2); c = score(tmp); res.append((c, N, L, p, q))
res.sort(); print("base", base, "tried", len(res), "best", res[:8])
if len(sys.argv) > 2 and res and res[0][0] < base:
    c, N, L, p, q = res[0]; L2 = [l[:] for l in ln]
    L2[N] = [q if x == p else x for x in L2[N]]; L2[L] = [p if x == q else x for x in L2[L]]; wr(sys.argv[2], L2); print("wrote", sys.argv[2], c)
