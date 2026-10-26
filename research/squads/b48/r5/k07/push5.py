import json, sys, math
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/r5/k07")
from screen import run
bases = [json.loads(l) for l in open("/home/user/degree-diameter/research/squads/b48/r5/k07/bases.jsonl")]
b5 = [x for x in bases if x["b"] == 5]
# groups: all meta m k r with m*k = 162 (n = 810), k even, r^k = 1 mod m, r unit
grp = []
for m in range(3, 163):
    if 162 % m: continue
    k = 162 // m
    if k % 2: continue
    for r in range(2, m):
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m: grp.append((m, k, r))
print("groups of order 162:", grp, file=sys.stderr)
out = open("/home/user/degree-diameter/research/squads/b48/r5/k07/push_out.jsonl", "a")
best_base = b5[0]
items = [tuple(x) for x in best_base["items"]]
for pat in best_base["patterns"]:
    best, info = run(5, items, pat, 27, 6, 17, 0.5, 1)
    out.write(json.dumps({"stage": "pats", "items": items, "pat": "".join(map(str, pat)), "m": 27, "k": 6, "r": 17, "best": best}) + "\n"); out.flush()
