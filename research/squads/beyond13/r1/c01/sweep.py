# Top-down exhaustive metacyclic sweep at D=13 (card c01). Stops at the first group order N with a cost-0 pair.
import sys, subprocess, os, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond13/r1/c01')
from enum_groups import groups
D = 13
lo, hi = int(sys.argv[1]), int(sys.argv[2])
EXH = "/home/user/degree-diameter/research/frontier/beyond13/bin/exh3"
GEN = "/home/user/degree-diameter/research/squads/beyond13/r1/c01/gen_meta.py"
HIT = "/home/user/degree-diameter/research/squads/beyond13/r1/c01/hits"
os.makedirs(HIT, exist_ok=True)
KMIN, KMAX = int(sys.argv[3]), int(sys.argv[4])
specs = sorted([g for g in groups(lo, hi) if KMIN <= g[2] <= KMAX], reverse=True)
print(len(specs), "groups, top-down", flush=True)
for N, m, k, r in specs:
    t0 = time.time()
    fn = f"/home/user/degree-diameter/research/squads/beyond13/r1/c01/tmp/t_{m}_{k}_{r}.bin"
    subprocess.run(["python3", GEN, str(m), str(k), str(r), fn], check=True)
    pre = f"{HIT}/hit_D{D}_meta_{m}_{k}_{r}"
    out = subprocess.run(["timeout", "600", "nice", "-n", "10", EXH, fn, str(D), pre],
                         capture_output=True, text=True).stdout
    os.remove(fn)
    line = [l for l in out.splitlines() if l.startswith("GROUP")]
    res = [l for l in out.splitlines() if l.startswith("RESULT")]
    print(f"meta {m} {k} {r} | " + (line[0] if line else out[-200:]) + f" wall={time.time()-t0:.1f}", flush=True)
    if res and res[0].startswith("RESULT FOUND"):
        print("HIT", m, k, r, N, res[0], flush=True)
        # finish the rest of this N with the same sweep? stop here (first hit found).
        break
print("SWEEP DONE", flush=True)
