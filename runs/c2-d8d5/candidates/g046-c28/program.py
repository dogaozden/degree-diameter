import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar graph search.
#
# Haar graph H(m, S): a_i ~ b_{(i+s) mod m} for s in S, |S| = d. It is
# d-regular and bipartite on 2m vertices. The map (a_i, b_j) -> (a_{i+x}, b_{j+x})
# is an automorphism, and so is the side swap a_i <-> b_{-i}. Therefore the
# diameter is at most D iff BFS from a_0 reaches all 2m vertices within D steps.
# The annealer moves one element of S at a time and minimises the number of
# unreached vertices. This is a different construction from the bi-Cayley lifts.
# ----------------------------------------------------------------------------

C_HAAR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, m_;
static int *S_, *inS_, *dist_, *queue_;

static long long cover_cost(void) {
    int m = m_, d = d_, N = 2 * m;
    for (int v = 0; v < N; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[0] = 0;
    queue_[t++] = 0;
    while (h < t) {
        int v = queue_[h++];
        int dv = dist_[v];
        if (dv >= D_) continue;
        if (v < m) {
            for (int k = 0; k < d; k++) {
                int u = m + (v + S_[k]) % m;
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[t++] = u; }
            }
        } else {
            int j = v - m;
            for (int k = 0; k < d; k++) {
                int u = (j - S_[k] + m) % m;
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[t++] = u; }
            }
        }
    }
    return (long long)(N - t);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    m_ = atoi(argv[5]);
    if (d_ < 1 || D_ < 1 || m_ < d_ || m_ < 2 || m_ > 1000000) { printf("0 0\n"); return 0; }

    S_ = malloc(sizeof(int) * (size_t)d_);
    inS_ = calloc((size_t)m_, sizeof(int));
    dist_ = malloc(sizeof(int) * (size_t)(2 * m_));
    queue_ = malloc(sizeof(int) * (size_t)(2 * m_));
    if (!S_ || !inS_ || !dist_ || !queue_) { printf("0 0\n"); return 0; }

    for (int k = 0; k < d_; ) {
        int x = rint_(m_);
        if (!inS_[x]) { inS_[x] = 1; S_[k++] = x; }
    }

    long long cost = cover_cost();
    const double T0 = 2.0, T1 = 0.05;
    clock_t c0 = clock();
    double T = T0;
    long long it = 0;
    while (cost > 0 && m_ > d_) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            T = T0 * pow(T1 / T0, el / limit);
        }
        it++;
        int idx = rint_(d_);
        int old = S_[idx];
        int nv;
        do { nv = rint_(m_); } while (inS_[nv]);
        inS_[old] = 0; inS_[nv] = 1; S_[idx] = nv;
        long long nc = cover_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            inS_[nv] = 0; inS_[old] = 1; S_[idx] = old;
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * m_, m_ * d_);
    for (int i = 0; i < m_; i++)
        for (int k = 0; k < d_; k++)
            printf("%d %d\n", i, m_ + (i + S_[k]) % m_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _haar_in_c(d, D, m, seconds, seed):
    """Run the C Haar annealer for cyclic order m; returns (n, edges), or (0, []) on failure."""
    out = lib.run_c(C_HAAR, [d, D, seed, f"{seconds:.2f}", m],
                    stdin_graph=None, timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, always valid for D >= 2).
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            if lib.is_prime_power(d - 1):
                return best  # calibration case: exact projective-plane record
            if d >= 5 and lib.is_prime_power(d - 2):
                try:
                    consider(*lib.araujo_lopez_graph(d - 2))
                except Exception:
                    pass

    # Main search: cyclic Haar graphs of order 2m, bisecting on m.
    # lo = largest m known to give a valid graph; hi = m assumed infeasible.
    lo = best[0] // 2
    hi = max(lo + 1, lib.moore_bound(d, D) // 2 + 1)
    m = lo + max(1, lo // 40)
    while True:
        rem = deadline - time.monotonic()
        if rem < 2.0 or hi - lo <= 1:
            break
        m = min(max(m, lo + 1), hi - 1)
        slice_s = min(6.0, max(1.5, rem / 4.0))
        try:
            n_, e_ = _haar_in_c(d, D, m, slice_s, rng.randrange(1, 1 << 30))
        except Exception:
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            best = (n_, e_)
            lo = n_ // 2
        else:
            hi = m
        m = (lo + hi) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
