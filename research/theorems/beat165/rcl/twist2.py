import random, sys
exec(open(__file__.replace('twist2.py', 'twist.py')).read().split('random.seed(')[0])
random.seed(int(sys.argv[1]))
# 4-walks with a given number of twisted steps (positions random)
for nt in (0, 1, 2):
    cnts = []
    for t in range(300):
        pos = set(random.sample(range(4), nt))
        fams = [(Fam(i in pos), True) for i in range(4)]
        x = random.randrange(256); cnts.append(len(endpoints(fams, x)))
    print('twisted steps %d: 4-walk endpoints mean %.1f, =256: %d/300' % (nt, sum(cnts)/len(cnts), sum(1 for c in cnts if c == 256)))
# closed-walk coverage with exactly r twisted edges at every vertex (perfect matching r = 1, 2-factor r = 2)
for r in (1, 2):
    covs = []
    for t in range(60):
        E = [(Fam(i < r), random.random() < 0.5) for i in range(4)]
        NB = [[(Fam(j < r - (1 if i < r else 0)), random.random() < 0.5) for j in range(3)] for i in range(4)]
        x = random.randrange(256); U = {x}
        for i, (f, out) in enumerate(E):
            go = (f, out); back = (f, not out)
            U |= endpoints([go, back], x)
            for j, (g, out2) in enumerate(E): U |= endpoints([go, back, (g, out2), (g, not out2)], x)
            for (g, out2) in NB[i]: U |= endpoints([go, (g, out2), (g, not out2), back], x)
        covs.append(len(U))
    print('%d twisted edges per vertex: closed-walk coverage mean %.1f max %d full %d/60' % (r, sum(covs)/len(covs), max(covs), sum(1 for c in covs if c == 256)))
