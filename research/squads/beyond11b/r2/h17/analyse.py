import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from frob import Frob, covers, nb_counts
p, k, r, h, D = 761, 19, 25, 5, 11
G = Frob(p, k, r); N = G.N; d = 4; W = d * (d - 1) ** (2 * h - 1)

def coset_nb_dp(labels):
    """exact NB word counts by quotient coordinate, via label-only DP (letters distinct, labels may repeat)"""
    d = len(labels)
    # state: dict last letter -> array over Z_k (counts of partial sums), alternating signs
    # word s1^-1 s2 s3^-1 s4 ...: letter at odd position enters with -label, even with +label
    # start: first letter (odd, sign -)
    st = np.zeros((d, k))
    for i, c in enumerate(labels):
        st[i, (-c) % k] += 1
    for step in range(1, 2 * h):
        sign = -1 if (step % 2 == 0) else 1   # position step+1: odd positions negative
        sign = -1 if ((step + 1) % 2 == 1) else 1
        tot = st.sum(axis=0)
        new = np.zeros((d, k))
        for i, c in enumerate(labels):
            prev = tot - st[i]                  # arriving with last letter != i
            new[i] = np.roll(prev, (sign * c) % k)
        st = new
    return st.sum(axis=0)

def lazy_fourier(labels):
    w = np.exp(2j * np.pi / k)
    f = np.zeros(k)
    for t in range(k):
        phi = sum(w ** (t * c) for c in labels)
        val = abs(phi) ** (2 * h)
        for j in range(k):
            f[j] += (val * w ** (-t * j)).real / k
    return f

def lazy_dp(labels):
    # all words (no NB), quotient distribution, by polynomial convolution on Z_k
    poly_p = np.zeros(k); poly_m = np.zeros(k)
    for c in labels:
        poly_p[c % k] += 1; poly_m[(-c) % k] += 1
    def conv(a, b):
        out = np.zeros(k)
        for i in range(k):
            out += a[i] * np.roll(b, i)
        return out
    f = np.zeros(k); f[0] = 1
    for _ in range(h):
        f = conv(f, poly_p); f = conv(f, poly_m)
    return f

if __name__ == '__main__':
    lines = open('/home/user/degree-diameter/research/squads/beyond11b/r1/g02/sol_m761_k19_r25_s2.sol').read().split('\n')
    S = [int(l.split()[0]) for l in lines[1:] if l.strip()]
    labels = [s % k for s in S]
    c = nb_counts(G, S, 2 * h)
    Wj_graph = np.array([c[np.arange(N) % k == j].sum() for j in range(k)])
    Wj_dp = coset_nb_dp(labels)
    print('labels', labels)
    print('NB coset counts graph vs label-DP max abs diff:', np.abs(Wj_graph - Wj_dp).max())
    print('NB coset counts W_j (j=0..18):', Wj_graph.astype(int).tolist())
    print('symmetry W_j == W_-j:', np.allclose(Wj_graph, Wj_graph[(-np.arange(k)) % k]))
    fl = lazy_fourier(labels); fd = lazy_dp(labels)
    print('lazy coset counts Fourier vs DP max diff:', np.abs(fl - fd).max(), 'sum', fd.sum(), 'Delta^2h', d ** (2 * h))
    print('lazy coset counts (min,max):', fd.min(), fd.max())
    # per-element stats
    jj = np.arange(N) % k
    print('NB per-element mean kernel (j=0):', c[jj == 0].mean(), ' var', c[jj == 0].var(),
          ' | j!=0 mean', c[jj != 0].mean(), ' var', c[jj != 0].var())
    # Jensen-type size law: holes per side ~ sum_j p exp(-W_j/p) vs N exp(-W/N)
    print('size law N e^{-W/N} =', N * np.exp(-W / N))
    print('coset-level law sum_j p e^{-W_j/p} =', sum(p * np.exp(-Wj_graph[j] / p) for j in range(k)))
    print('Frob label-check: |phi_t| for t=1..', [round(abs(sum(np.exp(2j*np.pi*t*c_/k) for c_ in labels)),3) for t in range(1,k)])
