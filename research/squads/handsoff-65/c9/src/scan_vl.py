# scan_vl.py TAG BASE ORDERS(comma) SECS ITERS SEED : vl annealing from a random start on BASE for every group table
# of each order (groups/sg_<order>_<id>.txt). Appends "order gid name best" to runs/<TAG>.tsv; saves cost-0 bases.
import sys, os, subprocess, glob
here = os.path.dirname(os.path.abspath(__file__)); root = os.path.join(here, '..')
TAG, BASE, ORDERS, SECS, ITERS, SEED = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(',')], sys.argv[4], sys.argv[5], int(sys.argv[6])
os.makedirs(os.path.join(root, 'runs'), exist_ok=True)
tsv = os.path.join(root, 'runs', TAG + '.tsv')
for O in ORDERS:
    for tab in sorted(glob.glob(os.path.join(root, 'groups', 'sg_%d_*.txt' % O)), key=lambda p: int(p.split('_')[-1][:-4])):
        gid = int(os.path.basename(tab).split('_')[-1][:-4])
        name = open(tab[:-4] + '.name').read().split(' abelian')[0].strip() if os.path.exists(tab[:-4] + '.name') else '?'
        rb = os.path.join(root, 'runs', 'rnd_%s_%d_%d.base' % (TAG, O, gid))
        subprocess.run(['python3', '-I', os.path.join(here, 'randbase.py'), os.path.join(root, BASE), str(O), str(SEED + gid), rb], check=True)
        env = dict(os.environ, SECS=SECS, ITERS=ITERS, SEED=str(SEED), FIXTREE='1',
                   OUT=os.path.join(root, 'runs', '%s_%d_%d.base' % (TAG, O, gid)))
        try:
            r = subprocess.run(['timeout', '600', 'nice', '-n', '10', os.path.join(root, '..', 'shared', 'vl'), rb, tab],
                               env=env, capture_output=True, text=True, timeout=600)
            best = [l for l in r.stdout.splitlines() if l.startswith('RESULT')]
            cost = best[0].split()[2] if best else 'ERR'
        except Exception as ex:
            cost = 'ERR'
        with open(tsv, 'a') as f:
            f.write('%d\t%d\t%s\t%s\n' % (O, gid, name, cost))
