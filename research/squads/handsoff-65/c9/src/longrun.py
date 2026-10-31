# longrun.py K SECS SEEDS : take the K best (lowest cost) non-error rows over runs/*.tsv (rows where base TAG is known)
# and run vl SA from fresh random starts for SECS each, SEEDS seeds per candidate. Results: runs/long.tsv
import sys, os, glob, subprocess
here = os.path.dirname(os.path.abspath(__file__)); root = os.path.join(here, '..')
K, SECS, SEEDS = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
BASES = {'A_L13': 'base_L13.base', 'A2_L13': 'base_L13.base', 'B_L7': 'base_L7.base', 'B2_L7': 'base_L7.base',
         'C_L5': 'base_L5.base', 'D_L6': 'base_L6.base', 'E_L14': 'base_L14.base', 'F_L15': 'base_L15.base'}
rows = []
for f in glob.glob(os.path.join(root, 'runs', '*.tsv')):
    tag = os.path.basename(f)[:-4]
    if tag not in BASES or tag == 'long': continue
    for l in open(f):
        p = l.rstrip('\n').split('\t')
        if len(p) < 4 or p[3] == 'ERR': continue
        rows.append((int(p[3]), tag, int(p[0]), int(p[1]), p[2]))
rows.sort()
done = set()
for cost, tag, O, gid, name in rows[:K]:
    tab = os.path.join(root, 'groups', 'sg_%d_%d.txt' % (O, gid))
    for s in range(SEEDS):
        seed = 1000 + 17 * s + gid
        rb = os.path.join(root, 'runs', 'lr_%s_%d_%d_%d.base' % (tag, O, gid, seed))
        subprocess.run(['python3', '-I', os.path.join(here, 'randbase.py'), os.path.join(root, BASES[tag]), str(O), str(seed), rb], check=True)
        out = os.path.join(root, 'runs', 'lr_%s_%d_%d_%d.sol' % (tag, O, gid, seed))
        env = dict(os.environ, SECS=SECS, ITERS='100000000', SEED=str(seed), FIXTREE='1', OUT=out)
        r = subprocess.run(['timeout', '600', 'nice', '-n', '10', os.path.join(root, '..', 'shared', 'vl'), rb, tab], env=env, capture_output=True, text=True)
        best = [l for l in r.stdout.splitlines() if l.startswith('RESULT')]
        c = best[0].split()[2] if best else 'ERR'
        with open(os.path.join(root, 'runs', 'long.tsv'), 'a') as fh:
            fh.write('%s\t%d\t%d\t%s\t%s\t%s\t%s\n' % (tag, O, gid, name, seed, SECS, c))
