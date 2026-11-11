#!/usr/bin/env python3
# i16: exhaustive exh3 scan over metacyclic groups Z_M x|_lam Z_K (faithful lam, one per cyclic subgroup), |G| in [lo, hi]
import sys, struct, subprocess, os, time, math
sys.path.insert(0, "/home/user/degree-diameter/research/d5")
import groups, numpy as np
D, lo, hi, tlimit = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
EXH = "/home/user/degree-diameter/research/frontier/beyond13/bin/exh3"
SCR = "/tmp/claude-0/-home-user-degree-diameter/8db4a241-a7fc-575b-978c-56a0ebe7fd4e/scratchpad"
OUT = "/home/user/degree-diameter/research/squads/beyond13/r6/i16/out/meta_D%d.log" % D
os.makedirs(SCR, exist_ok=True)
t0 = time.time(); cands = []
for K in range(int(os.environ.get("KMIN", "2")), hi):
    for M in range(max(3, -(-lo // K)), hi // K + 1):
        if math.gcd(M, K) != 1 and False: pass
        seen = set()
        for lam in range(2, M):
            if math.gcd(lam, M) != 1 or pow(lam, K, M) != 1 % M: continue
            # exact order K
            if any(pow(lam, j, M) == 1 % M for j in range(1, K)): continue
            sub = frozenset(pow(lam, j, M) for j in range(K))
            if sub in seen: continue
            seen.add(sub); cands.append((M, K, lam))
print(len(cands), "candidate groups", flush=True)
done = 0
for (M, K, lam) in cands:
    if time.time() - t0 > tlimit: print("TIME", flush=True); break
    T = groups.meta(M, K, lam); N = len(T)
    if not (lo <= N <= hi): continue
    fn = os.path.join(SCR, "meta_tab.bin")
    with open(fn, "wb") as f:
        f.write(struct.pack("<i", N)); f.write(np.array(T, dtype=np.uint16).tobytes())
    r = subprocess.run([EXH, fn, str(D)], capture_output=True, text=True, timeout=100)
    line = [l for l in r.stdout.splitlines() if l.startswith("GROUP") or l.startswith("RESULT")]
    done += 1
    with open(OUT, "a") as o:
        o.write(f"meta {M} {K} {lam} | " + " ".join(line) + "\n")
    if any("FOUND" in l for l in line): print("FOUND", M, K, lam, line, flush=True)
os.path.exists(fn) and os.remove(fn)
print("META DONE", done, flush=True)
