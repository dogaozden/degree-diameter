"""Random-sample screen of (group, orbit type) pairs with research/structured/haar_sym (RANDORB).
usage: python3 screen_run.py GROUPS.txt "k m f" SAMPLES OUT.tsv [WORKERS]
Each group line is 'N spec...' from enum_groups.py; meta specs get a trailing cyclic factor 1."""
import sys, subprocess, re, os
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, '..', '..', '..', 'research', 'structured', 'haar_sym')
BIN = os.path.abspath(BIN)
groups, kmf, samples, outp = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
workers = int(sys.argv[5]) if len(sys.argv) > 5 else 4
rows = [l.split(None, 1) for l in open(groups) if l.strip()]
pat = re.compile(r'fix=(\d+) samples=(\d+) min=(\d+) p1=(\d+) p10=(\d+) median=(\d+) mean=\S+ var=\S+ mu=(\S+)')
def run(row):
    N, spec = row[0], row[1].strip()
    if spec.startswith('meta'):
        spec = spec + ' 1'
    env = dict(os.environ, ORBIT=kmf, RANDORB=samples, THREADS='1')
    r = subprocess.run([BIN, '6', '8', '1', '1', '8', '/dev/null'] + spec.split(), env=env, capture_output=True, text=True)
    m = pat.search(r.stdout)
    if not m:
        return '%s\t%s\t%s\tFAIL\t%s' % (N, spec, kmf, (r.stderr.strip().splitlines() or ['?'])[-1][:80])
    fix, smp, mn, p1, p10, med, mu = m.groups()
    return '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s' % (N, spec, kmf, mn, p1, p10, med, mu, fix)
with ThreadPoolExecutor(workers) as ex, open(outp, 'w') as f:
    f.write('N\tspec\torbit\tmin\tp1\tp10\tmedian\tmu\tfix\n')
    for line in ex.map(run, rows):
        f.write(line + '\n')
