import sys, json, numpy as np, wild
q, m, seed = 5, int(sys.argv[1]), 1
rng = np.random.default_rng(int(sys.argv[2]))
par = wild.random_rule(rng, m, q)
json.dump({'seed': seed, 'rule': par}, open(f'val_{m}_{sys.argv[2]}.json', 'w'))
base = wild.build_base(q, seed)
lift = wild.Lift(base, m); lift.set_rule(par)
N2 = 2 * base['N']
tot = 0
for s0 in range(0, N2, 200):
    srcs = np.arange(s0, min(N2, s0 + 200))
    tot += lift.deficiency(srcs)
print('python exact deficiency', tot)
wild.write_glift(q, m, seed, par, f'val_{m}_{sys.argv[2]}.txt')
