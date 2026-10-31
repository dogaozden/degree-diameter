# ms.py TAG BASE "O:G,O:G,..." SEEDS SECS ITERS : several short SA restarts (full annealing schedule each) per group
import sys, os, subprocess
here = os.path.dirname(os.path.abspath(__file__)); root = os.path.join(here, '..')
TAG, BASE, PAIRS, SEEDS, SECS, ITERS = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5], sys.argv[6]
tsv = os.path.join(root, 'runs', TAG + '.tsv')
for pr in PAIRS.split(','):
    O, G = map(int, pr.split(':'))
    tab = os.path.join(root, 'groups', 'sg_%d_%d.txt' % (O, G))
    name = open(tab[:-4] + '.name').read().split(' abelian')[0].strip()
    for s in range(SEEDS):
        seed = 5000 + 31 * s + G
        rb = os.path.join(root, 'runs', 'ms_%s_%d_%d_%d.base' % (TAG, O, G, seed))
        subprocess.run(['python3', '-I', os.path.join(here, 'randbase.py'), os.path.join(root, BASE), str(O), str(seed), rb], check=True)
        out = os.path.join(root, 'runs', 'ms_%s_%d_%d_%d.sol' % (TAG, O, G, seed))
        env = dict(os.environ, SECS=SECS, ITERS=ITERS, SEED=str(seed), FIXTREE='1', OUT=out)
        r = subprocess.run(['timeout', '600', 'nice', '-n', '10', os.path.join(root, '..', 'shared', 'vl'), rb, tab], env=env, capture_output=True, text=True)
        best = [l for l in r.stdout.splitlines() if l.startswith('RESULT')]
        c = best[0].split()[2] if best else 'ERR'
        with open(tsv, 'a') as fh:
            fh.write('%d\t%d\t%s\t%s\t%d\n' % (O, G, name, c, seed))
