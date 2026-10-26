# c36 step 1: screen all j-multisets {j1<=j2<=j3} in Z_20 (S = {e, x, y, z}, x=(a1,j1), y=(a2,j2), z=(a3,j3), a in Z_55)
# by random sampling of the Z_55-parts; cost from the lift batch scorer.
import itertools, random, subprocess, sys, json
M, K, SAMP = 55, 20, 100
T = "/home/user/degree-diameter/research/squads/b48/tools"
pats = list(itertools.combinations_with_replacement(range(K), 3))
rng = random.Random(12345)
lines, owner = [], []
for p in pats:
    for _ in range(SAMP):
        a = [rng.randrange(M) for _ in range(3)]
        idx = [0] + [a[i] + M * p[i] for i in range(3)]
        lines.append(" ".join(map(str, idx)))
        owner.append(p)
inp = "\n".join(lines) + "\n"
out = subprocess.run([f"{T}/lift", f"{T}/bases/dipole4.txt", "meta:55:20:2", "4", "8", "eval"],
                     input=inp, capture_output=True, text=True, timeout=100).stdout.split("\n")
stats = {}
for p, o in zip(owner, out):
    s = stats.setdefault(p, [0, 0, None, 0])  # count valid, sum, min, invalid
    if o == "invalid" or o == "":
        s[3] += 1; continue
    c = int(o); s[0] += 1; s[1] += c
    s[2] = c if s[2] is None else min(s[2], c)
rows = []
for p in pats:
    s = stats[p]
    mean = s[1] / s[0] if s[0] else 1e9
    rows.append({"j": list(p), "mean": round(mean, 2), "min": s[2], "invalid": s[3]})
rows.sort(key=lambda r: r["mean"])
with open("screen.json", "w") as f:
    json.dump(rows, f, indent=0)
for r in rows[:25]:
    print(r)
print("patterns", len(rows), "lines", len(lines), "outlines", len(out))
