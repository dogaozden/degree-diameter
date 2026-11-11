# pick.py BLAME CUR K FIXOUT : drop K orbits chosen among the 6 most blocking (weighted by blame); write kept lines to FIXOUT
import sys, random
blame = {}
for l in open(sys.argv[1]):
    p, b = l.split(); blame[int(p)] = float(b)
cur = [l for l in open(sys.argv[2]) if l.strip()]
k = int(sys.argv[3])
order = sorted(range(len(cur)), key=lambda i: -blame.get(i, 0.0))
pool = order[:6]
w = [blame.get(i, 0.0) + 0.05 for i in pool]
drop = set()
random.seed()
for _ in range(k):
    tot = sum(w[j] for j, i in enumerate(pool) if i not in drop)
    r = random.uniform(0, tot); acc = 0.0
    for j, i in enumerate(pool):
        if i in drop: continue
        acc += w[j]
        if acc >= r: drop.add(i); break
with open(sys.argv[4], 'w') as f:
    for i, l in enumerate(cur):
        if i not in drop: f.write(l)
print(' '.join(str(i) for i in sorted(drop)))
