import collections
RUNS = '/home/user/degree-diameter/research/theorems/smallfam/runs/'
gap = {}
for line in open('nrsg_out.txt'):
    tag, n, k = line.split()
    gap[(tag, int(n))] = int(k)
files = {'B33': ['lift_b33_0_D7.tsv', 'lift_b33_1_D7.tsv', 'lift_b33_2_D7_idfix.tsv'],
         'B22': ['lift_b22_D7.tsv'], 'HAAR': ['allgroups_d3D7.tsv']}
for tag, fl in files.items():
    for fn in fl:
        rows = collections.Counter()
        ids = collections.defaultdict(set)
        for line in open(RUNS + fn):
            f = line.rstrip('\n').split('\t')
            rows[int(f[0])] += 1
            ids[int(f[0])].add(int(f[1]))
        bad = []
        for (t, n), k in sorted(gap.items()):
            if t != tag: continue
            got = rows.get(n, 0)
            # every SmallGroup id 1..k must appear exactly once
            if got != k or ids[n] != set(range(1, k + 1)):
                bad.append((n, k, got))
        extra = [n for n in rows if (tag, n) not in gap]
        total_gap = sum(k for (t, n), k in gap.items() if t == tag)
        print(f'{fn}: GAP total {total_gap}, rows {sum(rows.values())}, mismatched orders {bad}, extra orders {extra}')
