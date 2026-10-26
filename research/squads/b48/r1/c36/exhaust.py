# c36 step 2: exhaustive over all Z_55-parts (a1,a2,a3) for one Z_20 j-pattern (j1,j2,j3); S = {e, (a1,j1), (a2,j2), (a3,j3)}
import itertools, subprocess, sys, json
M = 55
T = "/home/user/degree-diameter/research/squads/b48/tools"
j = [int(v) for v in sys.argv[1].split(",")]
trip = list(itertools.product(range(M), repeat=3))
inp = "\n".join(f"0 {a[0]+M*j[0]} {a[1]+M*j[1]} {a[2]+M*j[2]}" for a in trip) + "\n"
out = subprocess.run([f"{T}/lift", f"{T}/bases/dipole4.txt", "meta:55:20:2", "4", "8", "eval"],
                     input=inp, capture_output=True, text=True, env={"LIMIT": "60", "PATH": "/usr/bin:/bin"},
                     timeout=110).stdout.split("\n")
best, bestA, zeros, hist = None, None, 0, {}
for a, o in zip(trip, out):
    if o in ("invalid", ""):
        continue
    c = int(o)
    hist[c] = hist.get(c, 0) + 1
    if best is None or c < best:
        best, bestA = c, a
    if c == 0:
        zeros += 1
print(json.dumps({"j": j, "best": best, "a": bestA, "zeros": zeros,
                  "hist_low": {k: hist[k] for k in sorted(hist)[:6]}, "n_lines": len(trip)}))
