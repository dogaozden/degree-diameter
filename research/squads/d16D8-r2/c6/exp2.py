import sys, statistics
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D8-r2/c6')
import design, rainbow, gq
q = int(sys.argv[1]); ks = [int(x) for x in sys.argv[2].split(',')]; seeds = int(sys.argv[3])
fn = '/home/user/degree-diameter/research/squads/d16D8-r2/c6/exp2_tmp_%d.base' % q
for k in ks:
    for rf in (False, True):
        uncs = []
        for s in range(seeds):
            V, m, E, f = design.design(q, k, s, random_f=rf)
            gq.write_base(fn, V, m, E)
            uncs.append(rainbow.evaluate(fn, 6)[0])
        print('q', q, 'k', k, 'm', 5 * k, 'random_f' if rf else 'rainbow ', 'mean %.0f min %d' % (statistics.mean(uncs), min(uncs)), flush=True)
