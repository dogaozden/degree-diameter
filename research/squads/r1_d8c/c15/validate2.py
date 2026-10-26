import sys, json, numpy as np, wild
q, m, seed = 5, int(sys.argv[1]), 1
rng = np.random.default_rng(int(sys.argv[2]))
par = wild.random_rule(rng, m, q)
base = wild.build_base(q, seed)
lift = wild.Lift(base, m); lift.set_rule(par)
srcs = np.array([0, 1, 2, 3906, 3907])
print('python deficiency on sources', srcs.tolist(), lift.deficiency(srcs))
wild.write_glift(q, m, seed, par, f'val_{m}_{sys.argv[2]}.txt')
