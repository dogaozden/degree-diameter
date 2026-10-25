# mkrand.py SEED N P MAXW OUT: random weighted graph in quotient format, and brute-force optimum to stdout
import random, sys, itertools
seed, n, p, maxw, out = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rnd = random.Random(seed)
w = [rnd.randint(1, maxw) for _ in range(n)]
adj = [set() for _ in range(n)]
for i in range(n):
    for j in range(i + 1, n):
        if rnd.random() < p:
            adj[i].add(j); adj[j].add(i)
with open(out, 'w') as f:
    f.write(f'{n}\n')
    for i in range(n):
        s = sorted(adj[i])
        f.write(f'{w[i]} {len(s)} ' + ' '.join(map(str, s)) + ('\n' if s else '\n'))
# brute force via recursion
best = 0
def rec(i, cur, cw, forb):
    global best
    if cw > best: best = cw
    for j in range(i, n):
        if j not in forb:
            rec(j + 1, cur, cw + w[j], forb | adj[j])
rec(0, [], 0, frozenset())
print(best)
