"""Item 1, statistics of S across records (does annealing leave a fingerprint in the normal form?).

For every record whose matrix part is a single SL/PSL(2,q), classify the quotients x = s_i^-1 s_j (i<j) by the type of
their Q-part: central (+-I), parabolic (tr = +-2, not central), split (tr^2-4 a nonzero square), elliptic (non-square).
Under a uniformly random S the quotients are uniform in G, so the expected fractions are
  SL(2,q), q odd: split q(q+1)(q-3)/2 / |SL|, elliptic q(q-1)^2/2 / |SL| (approx 1/2 each), parabolic ~ 2/q.
We compare the pooled observed counts with the pooled expectations (chi-square, 2 d.o.f.).
Second test: the full order (Q-part and Z_n part) of x; orders <= 6 give 2k-cycles of length <= 12 through
every vertex.  Expected number under random S: (#pairs) * P(order <= 6), P estimated by sampling 20000 random elements.
"""
import random, sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recs import all_records, MatG, orbit_type


def is_square(Q, t):
    if t == 0: return True
    return pow(t, (Q.q - 1) // 2, Q.q) == 1 if Q.F.k == 1 else None


def ctype(Q, x):
    A, M, neg = Q.A, Q.M, Q.neg
    a, b, c, d = x
    t = A[a][d]
    if x == Q.e or (Q.kind == 'sl' and x == (neg[1], 0, 0, neg[1])):
        return 'central'
    two = A[1][1]
    if t == two or t == neg[two]:
        return 'parabolic'
    disc = A[M[t][t]][neg[A[two][two]]]          # t^2 - 4
    # square test by table
    sq = Q._sq if hasattr(Q, '_sq') else None
    if sq is None:
        Q._sq = sq = set(M[v][v] for v in range(1, Q.q))
    return 'split' if disc in sq else 'elliptic'


def rand_elt(Q, rng):
    while True:
        a, b, c = rng.randrange(Q.q), rng.randrange(Q.q), rng.randrange(Q.q)
        if a == 0:
            continue
        # d = (1 + b c) / a
        d = Q.M[Q.A[1][Q.M[b][c]]][Q.inv_[a]]
        return Q.canon((a, b, c, d))


def main():
    rng = random.Random(1)
    obs, exp_ = Counter(), Counter()
    small_obs, small_exp = 0, 0.0
    lines = []
    for R in all_records():
        Q, G, S, n = R['Q'], R['G'], R['S'], R['n']
        if not isinstance(Q, MatG) or Q.kind not in ('sl', 'psl') or Q.q % 2 == 0:
            continue
        d = R['d']
        o = Counter()
        so = 0
        for i in range(d):
            for j in range(i + 1, d):
                x = G.mul(G.inv(S[i]), S[j])
                o[ctype(Q, x[0])] += 1
                k = G.order_of(x, cap=6)
                so += k is not None
        # expectation by sampling
        e = Counter()
        es = 0
        T = 4000
        for _ in range(T):
            y = (rand_elt(Q, rng), rng.randrange(n))
            e[ctype(Q, y[0])] += 1
            es += G.order_of(y, cap=6) is not None
        npairs = d * (d - 1) // 2
        for k in ('split', 'elliptic', 'parabolic', 'central'):
            obs[k] += o[k]
            exp_[k] += npairs * e[k] / T
        small_obs += so
        small_exp += npairs * es / T
        lines.append(f"{R['tag']}: pairs {npairs} split {o['split']} elliptic {o['elliptic']} parabolic {o['parabolic']} "
                     f"central {o['central']} | expected split {npairs*e['split']/T:.1f} elliptic {npairs*e['elliptic']/T:.1f} "
                     f"| full order<=6: {so} (expected {npairs*es/T:.2f}) | {orbit_type(R['tag'], d)}")
    out = '\n'.join(lines)
    chi = sum((obs[k] - exp_[k]) ** 2 / exp_[k] for k in ('split', 'elliptic', 'parabolic') if exp_[k] > 0)
    out += f"\n\nPOOLED over {len(lines)} records (SL/PSL(2,q), q odd):\n"
    for k in ('split', 'elliptic', 'parabolic', 'central'):
        out += f"  {k}: observed {obs[k]}, expected {exp_[k]:.1f}\n"
    out += f"  chi-square (split/elliptic/parabolic, 2 dof) = {chi:.2f}  (5% critical value 5.99)\n"
    out += f"  quotients of full order <= 6: observed {small_obs}, expected under random S {small_exp:.1f}\n"
    open('stats_S_out.txt', 'w').write(out)
    print(out[-1500:])


if __name__ == '__main__':
    main()
