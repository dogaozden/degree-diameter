# Sample random M-parts for each j-pattern class; cost from lift eval (dipole4 base, group G.bin).
import sys, subprocess, random, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r2/a12')
MS = 40
T = '/home/user/degree-diameter/research/squads/b48/tools'
BASE = T + '/bases/dipole4.txt'
reps = [tuple(map(int, l.split())) for l in open('reps.txt') if l.strip()]
SAMPLES = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
rng = random.Random(12)
START = int(sys.argv[2]) if len(sys.argv) > 2 else 0
out = open("screen.tsv", "a" if START else "w")
if START == 0: out.write("pattern\tmin_cost\tcount_cost0\tmedian\n")
t0 = time.time()
for ci in range(START, min(len(reps), START + 60), 60):
    chunk = reps[ci:ci + 60]
    lines = []
    for J in chunk:
        a, b, c = J[1], J[2], J[3]
        for _ in range(SAMPLES):
            lines.append('0 %d %d %d' % (a * MS + rng.randrange(MS), b * MS + rng.randrange(MS), c * MS + rng.randrange(MS)))
    p = subprocess.run([T + '/lift', BASE, T + '/../r2/a12/G.bin', '4', '8', 'eval'],
                       input='\n'.join(lines) + '\n', capture_output=True, text=True, timeout=110,
                       env={'THREADS': '1', 'PATH': '/usr/bin:/bin'})
    res = p.stdout.split('\n')
    assert len(res) >= len(lines), (len(res), len(lines), p.stderr[:300])
    for k, J in enumerate(chunk):
        vals = res[k * SAMPLES:(k + 1) * SAMPLES]
        cs = sorted(int(v) if v.strip().isdigit() else 10**9 for v in vals)
        out.write('%s\t%d\t%d\t%d\n' % (' '.join(map(str, J)), cs[0], sum(1 for c in cs if c == 0), cs[len(cs) // 2]))
    out.flush()
print('done', time.time() - t0, file=sys.stderr)
