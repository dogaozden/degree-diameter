import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: bi-Cayley voltage lifts over a semidirect product G = Z_m x| Z_t.
#
# The graph has two sides A and B, each made of k base vertices times the group
# G. There are d layers. Layer l has a permutation P_l of the k base indices and
# a voltage v_{l,i} in G. The edge A(i,g) -- B(P_l(i), g*v_{l,i}) is added for
# every layer l. Left multiplication by G is an automorphism of the lift that
# preserves both sides. So the diameter condition only needs one BFS from each
# of the 2k base vertices, not from all 2kG vertices. The C annealer does that
# check and swaps permutations or changes voltages to remove unreached pairs.
# Duplicate edges can appear, but they do not change reachability. They are
# removed on output.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, t_, G_, N_;
static int *mul_, *inv_, *P_, *IP_, *V_, *nbr_, *vis_, *queue_;
static int stamp_ = 0;

static int gcd_(int a, int b) { while (b) { int c = a % b; a = b; b = c; } return a; }

static void build_tables(int r) {
    int *pw = malloc(sizeof(int) * (size_t)t_);
    pw[0] = 1 % m_;
    for (int b = 1; b < t_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    for (int x = 0; x < G_; x++) {
        int a = x / t_, b = x % t_;
        for (int y = 0; y < G_; y++) {
            int c = y / t_, dd = y % t_;
            mul_[x * G_ + y] = ((a + pw[b] * c) % m_) * t_ + (b + dd) % t_;
        }
    }
    free(pw);
    for (int x = 0; x < G_; x++) {
        inv_[x] = 0;
        for (int y = 0; y < G_; y++) {
            if (mul_[x * G_ + y] == 0) { inv_[x] = y; break; }
        }
    }
}

/* Neighbour table. A vertex id = i*G + g (i < k). B vertex id = k*G + j*G + h. */
static void build_nbr(void) {
    int kG = k_ * G_;
    for (int i = 0; i < k_; i++) {
        for (int g = 0; g < G_; g++) {
            int v = i * G_ + g;
            for (int l = 0; l < d_; l++) {
                int j = P_[l * k_ + i];
                int vv = V_[l * k_ + i];
                nbr_[v * d_ + l] = kG + j * G_ + mul_[g * G_ + vv];
            }
        }
    }
    for (int j = 0; j < k_; j++) {
        for (int h = 0; h < G_; h++) {
            int v = kG + j * G_ + h;
            for (int l = 0; l < d_; l++) {
                int i = IP_[l * k_ + j];
                int vv = inv_[V_[l * k_ + i]];
                nbr_[v * d_ + l] = i * G_ + mul_[h * G_ + vv];
            }
        }
    }
}

/* Sum over the 2k base vertices of the number of vertices not reached within D_ steps. */
static long long cost_all(void) {
    long long total = 0;
    for (int s = 0; s < 2 * k_; s++) {
        int src = s * G_;
        stamp_++;
        int h = 0, t = 0;
        queue_[t++] = src;
        vis_[src] = stamp_;
        for (int depth = 0; depth < D_ && h < t; depth++) {
            int end = t;
            while (h < end) {
                int v = queue_[h++];
                for (int l = 0; l < d_; l++) {
                    int u = nbr_[v * d_ + l];
                    if (vis_[u] != stamp_) { vis_[u] = stamp_; queue_[t++] = u; }
                }
            }
        }
        total += (long long)(N_ - t);
    }
    return total;
}

static void output_graph(void) {
    int kG = k_ * G_;
    int cap = kG * d_;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    int m = 0;
    for (int v = 0; v < kG; v++) {
        for (int l = 0; l < d_; l++) {
            int u = nbr_[v * d_ + l];
            int dup = 0;
            for (int q = 0; q < l; q++) {
                if (nbr_[v * d_ + q] == u) { dup = 1; break; }
            }
            if (!dup) { eu[m] = v; ev[m] = u; m++; }
        }
    }
    printf("%d %d\n", N_, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
    fflush(stdout);
    free(eu);
    free(ev);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    t_ = atoi(argv[7]);
    int r = atoi(argv[8]);

    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || k_ > 8 || m_ < 2 || t_ < 1 ||
        (long long)m_ * t_ > 1500) {
        printf("0 0\n");
        return 0;
    }
    if (r < 1 || r >= m_ || gcd_(r, m_) != 1) { printf("0 0\n"); return 0; }
    {
        long long x = 1 % m_;
        for (int i = 0; i < t_; i++) x = x * r % m_;
        if (x != 1 % m_) { printf("0 0\n"); return 0; }
    }

    G_ = m_ * t_;
    N_ = 2 * k_ * G_;
    mul_ = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    inv_ = malloc(sizeof(int) * (size_t)G_);
    P_ = malloc(sizeof(int) * (size_t)d_ * k_);
    IP_ = malloc(sizeof(int) * (size_t)d_ * k_);
    V_ = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr_ = malloc(sizeof(int) * (size_t)N_ * d_);
    vis_ = calloc((size_t)N_, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)N_);
    int *perm = malloc(sizeof(int) * (size_t)k_);
    if (!mul_ || !inv_ || !P_ || !IP_ || !V_ || !nbr_ || !vis_ || !queue_ || !perm) {
        printf("0 0\n");
        return 0;
    }

    build_tables(r);

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < k_; i++) {
            P_[l * k_ + i] = perm[i];
            IP_[l * k_ + perm[i]] = i;
        }
        for (int i = 0; i < k_; i++) V_[l * k_ + i] = rint_(G_);
    }

    build_nbr();
    long long cur = cost_all();
    if (cur == 0) { output_graph(); return 0; }

    const double T0 = 2.0, T1 = 0.05;
    double T = T0;
    clock_t c0 = clock();
    long long it = 0;
    while (1) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            T = T0 * pow(T1 / T0, el / limit);
        }
        it++;

        int l = rint_(d_);
        int typ = (k_ >= 2) ? rint_(2) : 1;
        int ia = 0, ib = 0, ja = 0, jb = 0, ii = 0, oldv = 0;
        if (typ == 0) {
            ia = rint_(k_);
            ib = rint_(k_ - 1);
            if (ib >= ia) ib++;
            int *Pl = P_ + l * k_;
            int *IPl = IP_ + l * k_;
            ja = Pl[ia];
            jb = Pl[ib];
            Pl[ia] = jb; Pl[ib] = ja;
            IPl[jb] = ia; IPl[ja] = ib;
        } else {
            ii = rint_(k_);
            oldv = V_[l * k_ + ii];
            V_[l * k_ + ii] = rint_(G_);
        }

        build_nbr();
        long long nc = cost_all();
        if (nc == 0) { output_graph(); return 0; }

        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            if (typ == 0) {
                int *Pl = P_ + l * k_;
                int *IPl = IP_ + l * k_;
                Pl[ia] = ja; Pl[ib] = jb;
                IPl[ja] = ia; IPl[jb] = ib;
            } else {
                V_[l * k_ + ii] = oldv;
            }
        }
    }

    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target_G, rng):
    """Return (m, t, r) describing Z_m x| Z_t with m*t about target_G, or None."""
    for _ in range(100):
        t = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12])
        m = max(2, -(-target_G // t))
        if t == 1:
            return m, 1, 1
        r = 1
        if m >= 3 and rng.random() < 0.7:
            for _ in range(80):
                c = rng.randrange(2, m)
                if math.gcd(c, m) == 1 and pow(c, t, m) == 1 % m:
                    r = c
                    break
        return m, t, r
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle of length 2D: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best  # exact Moore-type construction; calibration case

    # Main search: C annealer over bi-Cayley lifts, climbing in order.
    end = t0 + max(2.0, time_limit - 5.0)
    while True:
        remaining = end - time.monotonic()
        if remaining < 1.5:
            break
        budget = min(remaining - 0.5, 8.0)

        candidates = [k for k in (1, 2, 3, 4, 6, 8)
                      if (best[0] // (2 * k)) * 1.03 + 2 <= 1400]
        if not candidates:
            break
        k = rng.choice(candidates)
        base_G = best[0] // (2 * k)
        target_G = max(2, int(base_G * (1.0 + rng.uniform(0.0, 0.03))) + 1)

        g = _sample_group(target_G, rng)
        if g is None:
            continue
        m, t, r = g
        G = m * t
        if 2 * k * G <= best[0] or G > 1400:
            continue

        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, t, r],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
