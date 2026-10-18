import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley voltage annealer over Z_m x| Z_k2.
#
# Vertices are A_i(g) = i*G+g and B_j(h) = (k+j)*G+h, where G = m*k2 and
# elements are coded a*k2+b with (a,b)(c,e) = (a + r^b c, b + e).
# Layer l joins A_i to B_{P[l][i]} with voltage S[l][i]: A_i(g) ~ B_j(g*s).
# Every vertex has degree d, the graph is bipartite, and left multiplication
# is an automorphism, so each of the 2k vertex blocks is one orbit. The cost
# is therefore computed with 2k plain BFS runs from block representatives.
# Multi-edges (same i, j and s in two layers) are penalised. The first cost-0
# configuration is printed as a simple graph and the program exits.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 40
#define STALL 20000

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int *mulT, *invEl, *P, *PI, *S, *qu, *dist_, *vis;
static int stamp_ = 0;

#define PM(l,i) P[(l)*k_+(i)]
#define PIM(l,j) PI[(l)*k_+(j)]
#define SM(l,i) S[(l)*k_+(i)]

static inline int nbr(int v, int l) {
    if (v < k_ * G_) {
        int i = v / G_, g = v % G_;
        int j = PM(l, i), s = SM(l, i);
        return (k_ + j) * G_ + mulT[g * G_ + s];
    }
    int u = v - k_ * G_;
    int j = u / G_, h = u % G_;
    int i = PIM(l, j), s = SM(l, i);
    return i * G_ + mulT[h * G_ + invEl[s]];
}

/* Number of vertices at distance > D_ from src. */
static int bfs_unres(int src) {
    stamp_++;
    int head = 0, tail = 0;
    qu[tail] = src; dist_[tail] = 0; tail++;
    vis[src] = stamp_;
    while (head < tail) {
        int v = qu[head], dv = dist_[head];
        head++;
        if (dv >= D_) continue;
        for (int l = 0; l < d_; l++) {
            int u = nbr(v, l);
            if (vis[u] != stamp_) {
                vis[u] = stamp_;
                qu[tail] = u; dist_[tail] = dv + 1; tail++;
            }
        }
    }
    return N_ - tail;
}

static long long evaluate(void) {
    long long unres = 0;
    for (int b = 0; b < 2 * k_; b++) unres += bfs_unres(b * G_);
    long long dup = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (PM(l, i) == PM(l2, i) && SM(l, i) == SM(l2, i)) dup++;
    return unres + (long long)PEN * dup;
}

static void swapP(int l, int i, int i2) {
    int t = PM(l, i); PM(l, i) = PM(l, i2); PM(l, i2) = t;
    PIM(l, PM(l, i)) = i;
    PIM(l, PM(l, i2)) = i2;
}

static void randomize(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) PM(l, i) = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = PM(l, i); PM(l, i) = PM(l, j); PM(l, j) = t;
        }
        for (int i = 0; i < k_; i++) PIM(l, PM(l, i)) = i;
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++)
            SM(l, i) = rint_(G_);
}

static void output(void) {
    printf("%d %d\n", 2 * k_ * G_, d_ * k_ * G_);
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) {
            int j = PM(l, i), s = SM(l, i);
            for (int g = 0; g < G_; g++)
                printf("%d %d\n", i * G_ + g, (k_ + j) * G_ + mulT[g * G_ + s]);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || m_ < 1 || k2_ < 1) { printf("0 0\n"); return 0; }
    G_ = m_ * k2_;
    if (G_ > 2500 || k_ > 200 || d_ > 200) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

    mulT = malloc(sizeof(int) * (size_t)G_ * G_);
    invEl = malloc(sizeof(int) * G_);
    P = malloc(sizeof(int) * d_ * k_);
    PI = malloc(sizeof(int) * d_ * k_);
    S = malloc(sizeof(int) * d_ * k_);
    qu = malloc(sizeof(int) * N_);
    dist_ = malloc(sizeof(int) * N_);
    vis = calloc(N_, sizeof(int));
    int *pw = malloc(sizeof(int) * k2_);
    if (!mulT || !invEl || !P || !PI || !S || !qu || !dist_ || !vis || !pw) { printf("0 0\n"); return 0; }

    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw[b] = (int)(((long long)pw[b - 1] * r_) % m_);
    for (int x = 0; x < G_; x++) {
        int a = x / k2_, b = x % k2_;
        for (int y = 0; y < G_; y++) {
            int c = y / k2_, e = y % k2_;
            int aa = (int)(((long long)pw[b] * c + a) % m_);
            int bb = (b + e) % k2_;
            mulT[x * G_ + y] = aa * k2_ + bb;
        }
    }
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            if (mulT[x * G_ + y] == 0) invEl[x] = y;

    clock_t c0 = clock();
    randomize();
    long long cur = evaluate();
    long long runBest = cur;
    long stale = 0;
    const double T0 = 4.0, T1 = 0.05;

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        double T = T0 * pow(T1 / T0, el / tl);

        int l = rint_(d_), i = rint_(k_);
        int typ = 0, oldS = 0, i2 = 0;
        if (k_ >= 2 && rdbl() < 0.25) {
            i2 = rint_(k_);
            if (i2 == i) continue;
            swapP(l, i, i2);
            typ = 1;
        } else {
            oldS = SM(l, i);
            int ns = rint_(G_);
            if (ns == oldS) continue;
            SM(l, i) = ns;
            typ = 0;
        }

        long long nc = evaluate();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) {
                output();
                return 0;
            }
        } else {
            if (typ == 0) SM(l, i) = oldS;
            else swapP(l, i, i2);
        }

        if (cur < runBest) {
            runBest = cur;
            stale = 0;
        } else if (++stale > STALL) {
            randomize();
            cur = evaluate();
            runBest = cur;
            stale = 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_K2_CHOICES = (1, 1, 2, 2, 3, 4, 5, 6, 8)
_K_CHOICES = (1, 2, 2, 3, 3, 4)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pick_r(m, k2, rng):
    """Return r with gcd(r, m) = 1 and r^k2 = 1 mod m (r = 1 for cyclic), or None."""
    if k2 == 1:
        return 1
    for _ in range(300):
        c = rng.randrange(1, m)
        if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
            return c
    return None


def _candidate(best_n, rng):
    """Random bi-Cayley parameters (k, m, k2, r) whose order 2*k*m*k2 exceeds best_n, or None."""
    k = rng.choice(_K_CHOICES)
    g_min = best_n // (2 * k) + 1
    g_t = g_min + rng.randrange(0, max(1, g_min // 12) + 1)
    if 2 * k * g_t > 4000:
        return None
    k2 = rng.choice(_K2_CHOICES)
    if k2 > g_t:
        k2 = 1
    m = -(-g_t // k2)
    if m < 2:
        return None
    r = _pick_r(m, k2, rng)
    if r is None:
        return None
    return k, m, k2, r


def _run_voltage(d, D, k, m, k2, r, seed, budget):
    """Run the C voltage annealer; returns (n, edges), with n = 0 when nothing was found."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", k, m, k2, r],
                    timeout=budget + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            q = d - 2
            if q >= 3 and lib.is_prime_power(q):
                try:
                    consider(*lib.araujo_lopez_graph(q))
                except Exception:
                    pass
            if lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley voltage search in C, one group at a time, each larger than the best so far.
    deadline = t0 + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    fails = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0 or fails > 5:
            break
        cand = _candidate(best[0], rng)
        if cand is None:
            continue
        k, m, k2, r = cand
        budget = min(remaining - 1.0, max(3.0, min(8.0, remaining / 3.0)))
        try:
            n, e = _run_voltage(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), budget)
            consider(n, e)
        except Exception:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
