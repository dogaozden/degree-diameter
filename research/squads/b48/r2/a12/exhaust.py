# Exhaustive M-part enumeration (40^3 = 64,000) for one j-pattern class J = (0,a,b,c) on the 1,120 group.
import sys, subprocess, itertools, collections
MS = 40
T = '/home/user/degree-diameter/research/squads/b48/tools'
J = tuple(map(int, sys.argv[1].split(',')))
a, b, c = J[1], J[2], J[3]
triples = list(itertools.product(range(MS), repeat=3))
lines = ['0 %d %d %d' % (a * MS + m1, b * MS + m2, c * MS + m3) for m1, m2, m3 in triples]
p = subprocess.run([T + '/lift', T + '/bases/dipole4.txt', '/home/user/degree-diameter/research/squads/b48/r2/a12/G.bin', '4', '8', 'eval'],
                   input='\n'.join(lines) + '\n', capture_output=True, text=True, timeout=110,
                   env={'THREADS': '1', 'PATH': '/usr/bin:/bin'})
res = p.stdout.split()
assert len(res) == len(lines), (len(res), p.stderr[:300])
costs = [int(v) if v.isdigit() else 10**9 for v in res]
best = min(costs)
argm = [triples[i] for i, v in enumerate(costs) if v == best]
hist = collections.Counter(costs)
print('pattern', J, 'lines', len(lines), 'best', best, 'count_at_best', len(argm), 'first_best', argm[:3])
print('lowest 8 costs:', sorted(hist.items())[:8])
with open('exh_%s.txt' % '_'.join(map(str, J)), 'w') as f:
    f.write('best %d\n' % best)
    for m in argm[:200]:
        f.write('%d %d %d\n' % (a * MS + m[0], b * MS + m[1], c * MS + m[2]))
