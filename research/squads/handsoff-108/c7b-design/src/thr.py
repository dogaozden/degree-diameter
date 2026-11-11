# thr.py (worker c7b): first-moment threshold for random cyclic lifts of H(q) + 2 matchings (Z_m).
# N = (q^6-1)/(q-1) points (= lines). Delta = q+3. W = sum over odd k<=7 of Delta(Delta-1)^(k-1) non-backtracking walks
# from a point, ending at lines; n = W/N walks per (point, line) pair on average.
# E(m) = expected uncovered triples = N^2 m exp(-n/m)   (Poisson; checked against hexeval random starts)
# L(m) = log(number of lift tuples) = 2 ln N! + (2N + (q+1) N) ln m     (sigma_1, sigma_2, mv_1, mv_2, hv)
# threshold m*: the largest m with L(m) >= E(m) (expected number of valid lifts >= 1 in this heuristic).
import math, sys
def stats(q, J=2):
    N = (q**6 - 1) // (q - 1)
    D = q + 1 + J
    W = sum(D * (D - 1) ** (k - 1) for k in (1, 3, 5, 7))
    n = W / N
    lnNf = math.lgamma(N + 1)
    def E(m): return N * N * m * math.exp(-n / m)
    def L(m): return J * lnNf + (J * N + (q + 1) * N) * math.log(m)
    best = None
    for m in range(2, 200):
        if L(m) >= E(m): best = m
    return N, D, W, n, E, L, best
if __name__ == '__main__':
    table = {3: 20, 4: 20, 5: 25, 7: 30}
    for q in (3, 4, 5, 7):
        N, D, W, n, E, L, best = stats(q)
        print('q=%d N=%d Delta=%d W=%d walks/pair=%.1f  heuristic threshold m*=%s  table m=%s' % (q, N, D, W, n, best, table[q]))
        for m in (12, 16, 20, 24, 28, 30, 31, 32):
            print('   m=%2d  E=%.4g  L=%.4g  E/L=%.3f  (2N m=%d)' % (m, E(m), L(m), E(m) / L(m), 2 * N * m))
