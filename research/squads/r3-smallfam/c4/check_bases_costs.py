import itertools, collections
RUNS = '/home/user/degree-diameter/research/theorems/smallfam/runs/'
# (a) enumerate connected loopless cubic bipartite multigraphs with m+m vertices, m=1..3,
#     as 3x3 / 2x2 / 1x1 nonnegative integer matrices with all line sums 3, up to row and column permutations
def classes(m):
    res = []
    rows = [r for r in itertools.product(range(4), repeat=m) if sum(r) == 3]
    mats = []
    for R in itertools.product(rows, repeat=m):
        if all(sum(R[i][j] for i in range(m)) == 3 for j in range(m)):
            mats.append(R)
    def connected(M):
        # bipartite support graph connectivity
        seen = {('a', 0)}; stack = [('a', 0)]
        while stack:
            side, x = stack.pop()
            nbrs = [('b', j) for j in range(m) if M[x][j] > 0] if side == 'a' else [('a', i) for i in range(m) if M[i][x] > 0]
            for v in nbrs:
                if v not in seen: seen.add(v); stack.append(v)
        return len(seen) == 2 * m
    canon = set()
    for M in mats:
        if not connected(M): continue
        best = None
        for p in itertools.permutations(range(m)):
            for q in itertools.permutations(range(m)):
                N = tuple(tuple(M[p[i]][q[j]] for j in range(m)) for i in range(m))
                if best is None or N < best: best = N
        canon.add(best)
    return len(mats), sorted(canon)
for m in (1, 2, 3):
    tot, cl = classes(m)
    print(f'm={m}: {tot} labelled matrices with line sums 3; connected classes up to row/col perms: {len(cl)}')
    for c in cl: print('   ', c)
# (b) best-cost summaries from the run files
def summary(fn, odd_haar=False, N_of=None):
    best_rows = []
    for line in open(RUNS + fn):
        f = line.rstrip('\n').split('\t')
        if f[5] in ('abfail', 'rank>2', 'rank>3', 'rank>4') or f[5].startswith('abfail'): continue
        if f[5].startswith('pass') or f[5] == 'lift':
            best_rows.append((int(f[8]), f[0], f[1], f[2], f[3], f[4], f[5], f[6], f[7]))
    best_rows.sort()
    return best_rows
for fn in ['allgroups_d3D7.tsv', 'lift_b22_D7.tsv', 'lift_b33_0_D7.tsv', 'lift_b33_1_D7.tsv', 'lift_b33_2_D7_idfix.tsv']:
    rows = summary(fn)
    print(fn, 'tested groups:', len(rows), 'min best:', [r[:2] + (r[0],) for r in rows[:3]])
    print('   nsol total:', sum(int(r[8]) for r in rows), ' sum tested:', sum(int(r[7]) for r in rows))
for r in summary('allgroups_d3D7.tsv')[:0]: pass
for line in open(RUNS + 'allgroups_d3D7.tsv'):
    f = line.rstrip('\n').split('\t')
    if f[0] == '96' and f[1] in ('65', '66'): print('Haar 96 row:', f)
