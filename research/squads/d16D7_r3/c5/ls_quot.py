#!/usr/bin/env python3
"""ls_quot.py QUOT SOL OUT CPU_SECONDS SEED: weighted add-move local search on a quotient independent set (card c5).
Move: add an outside quotient vertex v and drop its neighbours in S; Delta = W(v) - (weight of S-neighbours of v).
Best non-tabu move with Delta >= 0 is taken (plateau moves included, random tie-break); removed vertices are tabu for
a few iterations; if no move with Delta >= 0 exists, a random vertex is added (kick). Writes OUT (quotient ids) whenever
the weight improves. Light vertices (weight 1) are first-class here, unlike in qtabu."""
import sys, random, time

def load(path):
    f = open(path)
    n = int(f.readline())
    W = [0] * n; NB = [None] * n
    for i in range(n):
        a = list(map(int, f.readline().split()))
        W[i] = a[0]; NB[i] = a[2:2 + a[1]]
    return W, NB

def main():
    quot, solf, outf = sys.argv[1], sys.argv[2], sys.argv[3]
    budget, seed = float(sys.argv[4]), int(sys.argv[5])
    W, NB = load(quot)
    n = len(W)
    rnd = random.Random(seed)
    inS = [False] * n
    sw = [0] * n                      # weight of S-neighbours of each vertex
    S = [int(l) for l in open(solf) if l.strip()]
    def add(v):
        inS[v] = True
        for z in NB[v]:
            sw[z] += W[v]
    def rem(v):
        inS[v] = False
        for z in NB[v]:
            sw[z] -= W[v]
    for v in S:
        if not inS[v]:
            if sw[v] == 0:
                add(v)
    tot = sum(W[v] for v in range(n) if inS[v])
    best = tot
    def write(path, tot_):
        ids = [v for v in range(n) if inS[v]]
        tmp = path + '.tmp'
        open(tmp, 'w').write('\n'.join(map(str, ids)) + '\n')
        import os; os.replace(tmp, path)
    write(outf, tot)
    print('start total', tot, file=sys.stderr)
    tabu = [0] * n
    it = 0
    t0 = time.process_time()
    last_log = t0
    while time.process_time() - t0 < budget:
        it += 1
        bestd = None; cands = []
        for x in range(n):
            if inS[x]:
                continue
            d = W[x] - sw[x]
            if tabu[x] > it and not (tot + d > best):
                continue
            if bestd is None or d > bestd:
                bestd = d; cands = [x]
            elif d == bestd:
                cands.append(x)
        if bestd is None or bestd < 0:
            minsw = min(sw[y] for y in range(n) if not inS[y])
            cands = [y for y in range(n) if not inS[y] and sw[y] == minsw]
            x = rnd.choice(cands)
        else:
            x = rnd.choice(cands)
        drop = [z for z in NB[x] if inS[z]]
        for z in drop:
            rem(z); tot -= W[z]; tabu[z] = it + rnd.randint(5, 15)
        add(x); tot += W[x]
        if tot > best:
            best = tot
            write(outf, best)
            print('improved to', best, 'at it', it, 't=%.1f' % (time.process_time() - t0), file=sys.stderr)
        if time.process_time() - last_log > 30:
            last_log = time.process_time()
            print('t=%.0f it=%d tot=%d best=%d' % (last_log - t0, it, tot, best), file=sys.stderr)
    # final independence check
    ids = [v for v in range(n) if inS[v]]
    bad = sum(1 for v in ids for z in NB[v] if inS[z])
    print('END it=%d best=%d current=%d independent=%s' % (it, best, tot, bad == 0), file=sys.stderr)
    print('best_total', best)

if __name__ == '__main__':
    main()
