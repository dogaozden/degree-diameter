"""Tabu / min-conflicts local search for a blocking set (point set meeting every line) of W(q) of size K.
Usage: block_ls.py Q K SEED ITERS. Prints FOUND with the set, or BEST (fewest unmet lines)."""
import sys, random
q, K, seed, iters = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
rd = open('W%d_lines.txt' % q).read().split('\n')
n, nl = map(int, rd[0].split())
lines = [list(map(int, rd[1 + i].split())) for i in range(nl)]
pl = [[] for _ in range(n)]
for i, l in enumerate(lines):
    for p in l: pl[p].append(i)
inB = [False] * n
B = random.sample(range(n), K)
for p in B: inB[p] = True
hit = [0] * nl          # number of B-points on each line
for p in B:
    for i in pl[p]: hit[i] += 1
unhit = set(i for i in range(nl) if hit[i] == 0)
tabu = [0] * n
best = len(unhit)
for it in range(iters):
    if not unhit:
        print('FOUND q=%d K=%d seed=%d it=%d' % (q, K, seed, it), sorted(p for p in range(n) if inB[p])); break
    # pick a random unhit line, move one of its points out, one in that helps most
    l = random.choice(tuple(unhit))
    # candidate in: points of l
    bestmove = None; bestval = None
    outs = [p for p in range(n) if inB[p]]
    # gain of adding p: lines through p that are unhit (count); loss of removing r: lines only hit by r
    lossr = {}
    for r in outs:
        lossr[r] = sum(1 for i in pl[r] if hit[i] == 1)
    for p in lines[l]:
        if inB[p]: continue
        gain = sum(1 for i in pl[p] if hit[i] == 0)
        for r in outs:
            if tabu[r] > it: continue
            # exact delta: removing r then adding p
            d = 0
            # lines through r with hit 1 become unhit, except those also through p
            pr = set(pl[p])
            loss = sum(1 for i in pl[r] if hit[i] == 1 and i not in pr)
            delta = gain - loss
            if bestval is None or delta > bestval or (delta == bestval and random.random() < 0.3):
                bestval = delta; bestmove = (r, p)
    if bestmove is None: continue
    r, p = bestmove
    inB[r] = False; tabu[p] = it + 7
    for i in pl[r]:
        hit[i] -= 1
        if hit[i] == 0: unhit.add(i)
    inB[p] = True; tabu[r] = it + 3
    for i in pl[p]:
        if hit[i] == 0: unhit.discard(i)
        hit[i] += 1
    if len(unhit) < best:
        best = len(unhit)
else:
    print('BEST q=%d K=%d seed=%d unmet=%d' % (q, K, seed, best))
