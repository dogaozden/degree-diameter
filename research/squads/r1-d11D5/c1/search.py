# c1: algebraic chi-ansatz families nu(flag) = chi(F(p, l)) mod 3 on W(7); scored by zcov; simulated annealing on coefficients.
import numpy as np, json, sys, time
import feat
from feat import FP, FL, CHI, P

pairs2p = [(i, j) for i in range(4) for j in range(i, 4)]          # 10 quadratic monomials in p
pairs2l = [(a, b) for a in range(6) for b in range(a, 6)]          # 21 quadratic monomials in l
PP2 = np.stack([FP[:, i] * FP[:, j] % P for i, j in pairs2p], axis=1)   # 3200 x 10
LL2 = np.stack([FL[:, a] * FL[:, b] % P for a, b in pairs2l], axis=1)   # 3200 x 21

FAMILIES = {
    'bil':        (24, lambda x: CHI[np.einsum('fi,ij,fj->f', FP, x.reshape(4, 6), FL) % P]),
    'bil2':       (48, lambda x: (CHI[np.einsum('fi,ij,fj->f', FP, x[:24].reshape(4, 6), FL) % P]
                                  + CHI[np.einsum('fi,ij,fj->f', FP, x[24:].reshape(4, 6), FL) % P]) % 3),
    'quadp_linl': (60, lambda x: CHI[np.einsum('fa,ak,fk->f', PP2, x.reshape(10, 6), FL) % P]),
    'linp_quadl': (84, lambda x: CHI[np.einsum('fi,ib,fb->f', FP, x.reshape(4, 21), LL2) % P]),
}


def run(fam, nrand, nanneal, seed):
    m, gen = FAMILIES[fam]
    rng = np.random.default_rng(seed)
    best_c, best_x = None, None
    costs = []
    for _ in range(nrand):
        x = rng.integers(0, P, m)
        c = feat.zcov_cost(gen(x), f'{fam}_r')
        costs.append(c)
        if best_c is None or c < best_c:
            best_c, best_x = c, x.copy()
    print(f'[{fam}] random: n={nrand} min={min(costs)} median={int(np.median(costs))} max={max(costs)}', flush=True)
    cur_x, cur_c = best_x.copy(), best_c
    T0, T1 = 12.0, 0.5
    t0 = time.time()
    for it in range(nanneal):
        T = T0 * (T1 / T0) ** (it / max(1, nanneal - 1))
        y = cur_x.copy()
        k = rng.integers(m)
        y[k] = (y[k] + rng.integers(1, P)) % P
        c = feat.zcov_cost(gen(y), f'{fam}_a')
        if c <= cur_c or rng.random() < np.exp(-(c - cur_c) / T):
            cur_x, cur_c = y, c
            if c < best_c:
                best_c, best_x = c, y.copy()
    print(f'[{fam}] anneal: steps={nanneal} best={best_c} time={time.time()-t0:.0f}s', flush=True)
    lab = gen(best_x)
    # verify with zcov one more time, save labels and params
    verify = feat.zcov_cost(lab, f'best_{fam}')
    np.savetxt(f'/home/user/degree-diameter/research/squads/r1-d11D5/c1/best_{fam}_labels.txt', lab, fmt='%d')
    rec = {'family': fam, 'best_cost': int(best_c), 'verify_cost': int(verify), 'params': [int(v) for v in best_x]}
    with open('/home/user/degree-diameter/research/squads/r1-d11D5/c1/results.jsonl', 'a') as f:
        f.write(json.dumps(rec) + '\n')
    return rec


if __name__ == '__main__':
    fams = sys.argv[1].split(',')
    nrand = int(sys.argv[2]); nanneal = int(sys.argv[3]); seed = int(sys.argv[4])
    for fam in fams:
        print(run(fam, nrand, nanneal, seed + hash(fam) % 1000), flush=True)
