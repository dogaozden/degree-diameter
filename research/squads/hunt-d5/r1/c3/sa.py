"""Edge-switch simulated annealing over cubic bipartite graphs on m+m vertices.
Cost = same-side pairs at distance > 4 (ordered) + vertices on no 4-cycle.
usage: sa.py ITERS SEED_COUNT T0 M [M ...]"""
import sys, os, math, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ctrl

HERE = os.path.dirname(os.path.abspath(__file__))

def run(m, iters, seed, T0, T1):
    rng = random.Random(seed * 1000003 + m)
    adj = ctrl.random_cubic_bip(m, rng)
    cur = ctrl.cost(adj, m)
    best, best_adj = cur, adj
    for it in range(iters):
        if cur == 0:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        new = ctrl.switch_move(adj, m, rng)
        if new is None:
            continue
        c = ctrl.cost(new, m)
        d = c - cur
        if d <= 0 or rng.random() < math.exp(-d / T):
            adj, cur = new, c
            if cur < best:
                best, best_adj = cur, adj
    return best, best_adj

if __name__ == '__main__':
    iters = int(sys.argv[1]); seeds = int(sys.argv[2]); T0 = float(sys.argv[3])
    ms = [int(x) for x in sys.argv[4:]]
    for m in ms:
        t0 = time.time()
        overall = (10**9, None, None)
        for seed in range(seeds):
            c, adj = run(m, iters, seed, T0, 0.05)
            if c < overall[0]:
                overall = (c, adj, seed)
            if c == 0:
                break
        c, adj, seed = overall
        c4 = sum(ctrl.c4_count(adj, v) for v in range(2 * m)) / (2 * m)
        print(f'm={m} best_cost={c} seed={seed} iters={iters} seeds_run={seed+1} mean_c4_per_vertex={c4:.2f} '
              f'time={time.time()-t0:.1f}s', flush=True)
        if c == 0:
            fn = os.path.join(HERE, f'ctrl_m{m}.edges')
            ctrl.write_edges(fn, m, adj)
            print('  saved', fn, flush=True)
