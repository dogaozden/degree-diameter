import subprocess, os, sys, re
from groups_list import metas
T = "/home/user/degree-diameter/research/squads/b48/tools"
W = "/home/user/degree-diameter/research/squads/b48/r5/k04"
plan = []  # (basefile, N, ngroups)
plan += [("k4", N, 3) for N in (204, 208, 210, 216)]
plan += [("prism3", N, 3) for N in (136, 144)]
plan += [(f"c8_{a}", 104, 2) for a in (1, 2, 3)]
plan += [("petersen", N, 2) for N in (82, 90)]
plan += [(f"c10_{a}", 82, 2) for a in (1, 2, 3, 4)]
plan += [(f"c12_{a}", 68, 2) for a in (1, 2, 3, 4, 5)]
plan += [("c14_1", 60, 2), ("c14_3", 60, 2), ("c16_1", 52, 2), ("c16_3", 52, 2)]
secs = sys.argv[1] if len(sys.argv) > 1 else "3"
out = open(f"{W}/screen.tsv", "a")
for base, N, ng in plan:
    L = [g for g in metas(N) if g[1] >= 4] or metas(N)
    idx = sorted(set(round(i * (len(L) - 1) / max(ng - 1, 1)) for i in range(ng))) if ng > 1 else [0]
    for i in idx:
        m, k, r = L[i]
        spec = f"meta:{m}:{k}:{r}"
        env = dict(os.environ, THREADS="1", NOTREE="1", ODDSTRIDE=str(m), QUIET="1")
        p = subprocess.run(["timeout", "120", "nice", "-n", "10", f"{T}/lift", f"bases/{base}.txt", spec, "3", "10", secs, "1", "8"],
                           cwd=W, env=env, capture_output=True, text=True)
        line = [l for l in p.stdout.splitlines() if l.startswith("RESULT")]
        res = line[0] if line else ("ERR " + p.stderr.strip()[:200])
        bm = re.search(r"best=(\d+)", res); n = re.search(r"n=(\d+)", res)
        b = int(open(f"{W}/bases/{base}.txt").readline().split()[0])
        cost = int(bm.group(1)) if bm else -1
        miss = cost / b if cost >= 0 else -1
        row = f"{base}\t{spec}\t{n.group(1) if n else '?'}\t{cost}\t{miss:.2f}\t{secs}s"
        print(row, flush=True); out.write(row + "\n"); out.flush()
