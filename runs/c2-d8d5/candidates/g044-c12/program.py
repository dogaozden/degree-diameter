import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 0 (new): bi-Cayley graphs over PSL(2,p) or PGL(2,p).
#
# Vertices: g in G on side 0 (index g) and h in G on side 1 (index G+h).
# Edges: (g, 0) ~ (g*s, 1) for each s in S, where |S| = d and S is a set of
# distinct group elements. Left multiplication is an automorphism, so the
# diameter check only needs BFS from (e,0) and (e,1). The annealer moves
# elements of S to minimise the number of unreached vertices.
# ----------------------------------------------------------------------------

C_CAYLEY = r"""
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

static int P_, KIND_, d_, D_, G_;
static int *ea, *eb, *ec, *ed;
static int *idx_;
static int *mul_, *inv_;
static int S_[64];
static int *nb_, *stamp_, *queue_;
static int curstamp_ = 0;

static int modpow(int a, int e) {
    long long r = 1, b = a % P_;
    if (b < 0) b += P_;
    while (e) {
        if (e & 1) r = r * b % P_;
        b = b * b % P_;
        e >>= 1;
    }
    return (int)r;
}

static int code4(int a, int b, int c, int e) { return ((a * P_ + b) * P_ + c) * P_ + e; }

static int norm_code(int a, int b, int c, int e) {
    int v = a ? a : (b ? b : (c ? c : e));
    int iv = modpow(v, P_ - 2);
    a = a * iv % P_;
    b = b * iv % P_;
    c = c * iv % P_;
    e = e * iv % P_;
    return code4(a, b, c, e);
}

static int build_group(int fill) {
    int P = P_;
    int cap = P * P * P;
    int *isq = calloc((size_t)P, sizeof(int));
    for (int x = 1; x < P; x++) isq[x * x % P] = 1;
    int G = 0;
    if (fill) {
        ea = malloc(sizeof(int) * (size_t)cap);
        eb = malloc(sizeof(int) * (size_t)cap);
        ec = malloc(sizeof(int) * (size_t)cap);
        ed = malloc(sizeof(int) * (size_t)cap);
        idx_ = malloc(sizeof(int) * (size_t)P * P * P * P);
        for (int i = 0; i < P * P * P * P; i++) idx_[i] = -1;
    }
    for (int a = 0; a < P; a++)
    for (int b = 0; b < P; b++)
    for (int c = 0; c < P; c++)
    for (int e = 0; e < P; e++) {
        int det = ((a * e - b * c) % P + P) % P;
        if (!det) continue;
        int v = a ? a : (b ? b : (c ? c : e));
        if (v != 1) continue;
        if (KIND_ == 0 && !isq[det]) continue;
        if (fill) {
            idx_[code4(a, b, c, e)] = G;
            ea[G] = a; eb[G] = b; ec[G] = c; ed[G] = e;
        }
        G++;
    }
    free(isq);
    return G;
}

static long long cost_of(void) {
    int G = G_, d = d_, D = D_;
    for (int g = 0; g < G; g++)
        for (int i = 0; i < d; i++)
            nb_[g * d + i] = G + mul_[g * G + S_[i]];
    for (int h = 0; h < G; h++)
        for (int i = 0; i < d; i++)
            nb_[(G + h) * d + i] = mul_[h * G + inv_[S_[i]]];
    long long cost = 0;
    int N2 = 2 * G;
    int srcs[2] = {0, G};
    for (int s = 0; s < 2; s++) {
        curstamp_++;
        int hd = 0, tl = 0;
        queue_[tl++] = srcs[s];
        stamp_[srcs[s]] = curstamp_;
        int dist = 0;
        while (hd < tl && dist < D) {
            int end = tl;
            while (hd < end) {
                int v = queue_[hd++];
                const int *nv = nb_ + (size_t)v * d;
                for (int i = 0; i < d; i++) {
                    int u = nv[i];
                    if (stamp_[u] != curstamp_) {
                        stamp_[u] = curstamp_;
                        queue_[tl++] = u;
                    }
                }
            }
            dist++;
        }
        cost += N2 - tl;
    }
    return cost;
}

static int in_S(int x, int upto) {
    for (int j = 0; j < upto; j++) if (S_[j] == x) return 1;
    return 0;
}

static void print_graph(void) {
    int G = G_, d = d_;
    printf("%d %d\n", 2 * G, G * d);
    for (int g = 0; g < G; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, G + mul_[g * G + S_[i]]);
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    P_ = atoi(argv[1]);
    KIND_ = atoi(argv[2]);
    d_ = atoi(argv[3]);
    D_ = atoi(argv[4]);
    rs ^= (u64)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[6]);
    if (P_ < 2 || P_ > 40 || (KIND_ != 0 && KIND_ != 1) || d_ < 1 || d_ > 64 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    if (KIND_ == 0 && P_ == 2) { printf("0 0\n"); return 0; }
    G_ = build_group(0);
    if (G_ > 3000 || G_ < d_ + 1) { printf("0 0\n"); return 0; }
    build_group(1);
    int G = G_;
    mul_ = malloc(sizeof(int) * (size_t)G * G);
    inv_ = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            int a = (ea[x] * ea[y] + eb[x] * ec[y]) % P_;
            int b = (ea[x] * eb[y] + eb[x] * ed[y]) % P_;
            int c = (ec[x] * ea[y] + ed[x] * ec[y]) % P_;
            int e = (ec[x] * eb[y] + ed[x] * ed[y]) % P_;
            int id = idx_[norm_code(a, b, c, e)];
            if (id < 0) { printf("0 0\n"); return 0; }
            mul_[x * G + y] = id;
        }
    }
    int ident = idx_[code4(1, 0, 0, 1)];
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mul_[x * G + y] == ident) { inv_[x] = y; break; }

    nb_ = malloc(sizeof(int) * (size_t)2 * G * d_);
    stamp_ = calloc((size_t)2 * G, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)2 * G);
    if (!nb_ || !stamp_ || !queue_) { printf("0 0\n"); return 0; }

    for (int i = 0; i < d_; i++) {
        int x;
        do { x = rint_(G); } while (in_S(x, i));
        S_[i] = x;
    }

    long long cost = cost_of();
    const double T0 = 6.0, T1 = 0.2;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int i = rint_(d_);
        int x = rint_(G);
        if (in_S(x, d_)) continue;
        int old = S_[i];
        S_[i] = x;
        long long nc = cost_of();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            S_[i] = old;
        }
    }
    if (cost != 0) { printf("0 0\n"); return 0; }
    print_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealer over the semidirect product
# Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b + e)).
# ----------------------------------------------------------------------------

C_LIFT = r"""
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

static int d_, D_, k_, m_, k2_, G_, N_;
static int *perm, *vol, *nbr, *pw, *queue_, *stamp;
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (a + (pw[b] * c) % m_) % m_;
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int t = perm[l * k + i], s = vol[l * k + i];
            for (int x = 0; x < G; x++) {
                int y = gmul(x, s);
                int a = i * G + x, b = (k + t) * G + y;
                nbr[a * d + l] = b;
                nbr[b * d + l] = a;
            }
        }
}

static long long eval_cost(void) {
    int k = k_, d = d_, G = G_, N = N_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    build_nbr();
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        curstamp++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curstamp;
        int dist = 0;
        while (h < t && dist < D_) {
            int end = t;
            while (h < end) {
                int v = queue_[h++];
                const int *nv = nbr + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int u = nv[l];
                    if (stamp[u] != curstamp) {
                        stamp[u] = curstamp;
                        queue_[t++] = u;
                    }
                }
            }
            dist++;
        }
        cost += N - t;
    }
    return cost + 50 * dups;
}

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
    r %= m_;
    G_ = m_ * k2_;
    if ((long long)G_ * 2 * k_ > 200000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!perm || !vol || !nbr || !queue_ || !stamp) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l * k_ + i];
            perm[l * k_ + i] = perm[l * k_ + j];
            perm[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) vol[l * k_ + i] = rint_(G_);
    }

    long long cost = eval_cost();
    const double T0 = 6.0, T1 = 0.15;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = rint_(d_), i = rint_(k_);
        if (k_ >= 2 && rint_(3) == 0) {
            int i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int *p1 = &perm[l * k_ + i], *p2 = &perm[l * k_ + i2];
            int t = *p1; *p1 = *p2; *p2 = t;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = *p1; *p1 = *p2; *p2 = t;
            }
        } else {
            int old = vol[l * k_ + i];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[l * k_ + i] = nv;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[l * k_ + i] = old;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    int cnt = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[v * d_ + l];
            if (u > v) pairs[cnt++] = (long long)v * N_ + u;
        }
    qsort(pairs, (size_t)cnt, sizeof(long long), cmp_ll);
    int uniq = 0;
    for (int i = 0; i < cnt; i++)
        if (i == 0 || pairs[i] != pairs[i - 1]) pairs[uniq++] = pairs[i];
    printf("%d %d\n", N_, uniq);
    for (int i = 0; i < uniq; i++)
        printf("%lld %lld\n", pairs[i] / N_, pairs[i] % N_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (from parent).
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

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
static int best_n = 0, best_m = 0;

static int isadj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a * d_ + i] == b) return 1;
    return 0;
}
static void delE1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d_ + i] == b) {
            adj[a * d_ + i] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void addE(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void delE(int a, int b) { delE1(a, b); delE1(b, a); }

static long long bad_pairs(void) {
    u64 *cur = bufA, *alt = bufB;
    W = (N + 63) / 64;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)cap_w);
    for (int v = 0; v < N; v++) cur[(size_t)v * cap_w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * cap_w;
            u64 *r = cur + (size_t)v * cap_w;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v * d_ + i] * cap_w;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - cnt;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int grow_max = argc > 5 ? atoi(argv[5]) : 60;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000 || grow_max < 0) {
        printf("0 0\n");
        return 0;
    }
    cap_n = n0 + 2 * grow_max + 2;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (side[u] == -1) { side[u] = 1 - side[v]; q[t++] = u; }
            }
        }
    }
    free(q);

    const double T0 = 30.0, T1 = 0.3;
    clock_t c0 = clock();
    long long cost = bad_pairs();
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = rint_(N), y = rint_(N);
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5)
_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
_CAYLEY_MAX_ORDER = 3000


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_candidates(d, best_n, side_bound):
    """Groups PSL(2,p) / PGL(2,p) whose order G gives 2G > best_n and G <= side_bound, ascending."""
    out = []
    for p in _PRIMES:
        for kind in (0, 1):
            if kind == 0 and p == 2:
                continue
            order = p * (p * p - 1) // (2 if kind == 0 else 1)
            if 2 * order > best_n and order <= side_bound and order <= _CAYLEY_MAX_ORDER and order > d:
                out.append((order, p, kind))
    out.sort()
    return out


def _cayley_in_c(p, kind, d, D, seconds, seed):
    """Run the C bi-Cayley annealer over PSL/PGL(2,p); returns (n, edges) or (0, [])."""
    out = lib.run_c(C_CAYLEY, [p, kind, d, D, seed, f"{seconds:.2f}"],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _pick_k(rng, stats):
    """Bandit choice of base-block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.2:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C toggle annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
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

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase A (new construction): bi-Cayley graphs over PSL(2,p) / PGL(2,p),
    # tried in ascending order of group size so that each success raises the bar.
    side_bound = lib.moore_bound(d, D) // 2
    cay_end = t0 + 0.6 * time_limit
    for order, p, kind in _group_candidates(d, best[0], side_bound):
        if 2 * order <= best[0]:
            continue
        remaining = cay_end - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, max(2.0, 0.45 * remaining))
        try:
            n_, e_ = _cayley_in_c(p, kind, d, D, slice_s, rng.randrange(1, 1 << 30))
        except RuntimeError:
            continue
        consider(n_, e_)

    # Phase B (fallback): C lift annealing over groups, with an adaptive target size.
    lift_end = t0 + 0.8 * time_limit
    stats = {k: [0, 0] for k in _KS}
    frac = 0.08
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = _pick_k(rng, stats)
        target_n = int(best[0] * (1.0 + frac)) + 2
        g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        stats[k][0] += 1
        slice_s = min(4.0, max(1.0, 0.25 * remaining))
        try:
            n_, e_ = _lift_in_c(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
        except RuntimeError:
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            stats[k][1] += 1
            best = (n_, e_)
            frac = min(0.25, frac * 1.3)
        else:
            frac = max(0.003, frac * 0.85)

    # Phase C: C toggle annealer tries to add vertex pairs to the best graph.
    c_budget = time_limit - (time.monotonic() - t0) - 4.0
    if c_budget >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, c_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
