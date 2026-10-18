"""Lift search engine: C-native bi-Cayley voltage-lift simulated annealing over semidirect
products Z_m x| Z_k2, with focused moves and a ratcheted order goal. Exact constructions
(projective planes, Araujo-Pardo-Lopez, generalized quadrangles) are used when they apply.
Every returned graph is checked with lib.is_valid, and K_{d,d} is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift search over Z_m x| Z_k2.
 * Usage:  prog d D seed budget start_n
 * Stdin is ignored. Stdout: "n m" + edges of the best valid lift found, or "0 0".
 *
 * Vertices: A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h, for i, j < K and g, h in the group.
 * Layer l sends A-block i to B-block perm[l][i] with voltage sv[l][i]:
 *     A_{i,g} ~ B_{p,g*s}   and   B_{p,h} ~ A_{i,h*s^-1}.
 * Each layer is a permutation, so every vertex has degree d. The lift is left-invariant,
 * so diameter <= D holds iff every block representative reaches every vertex within D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 4
#define MAXN 40000
#define MAXE (MAXD * MAXN / 2)
#define PEN 100

typedef struct {
    int m, k2, G;
    int powr[40];
} Group;

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static int K, G, N;
static Group grp;
static int perm[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int nb[MAXD][MAXN];
static unsigned char mk[MAXN], mk2[MAXN], acc[MAXN];
static int bu[MAXE], bv[MAXE];
static int be_n = 0, be_m = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(int dd, int DD) {
    if (DD <= 0 || dd <= 0) return 1;
    if (dd == 1) return 2;
    if (dd == 2) return 2L * DD;
    long s = 0, p = 1;
    for (int i = 0; i < DD; i++) {
        s += p;
        p *= (dd - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

static int gcdi(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int pmod(long long b, long long e, long long m) {
    long long r = 1 % m, x = ((b % m) + m) % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int gmul(const Group *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2;
    int c = y / g->k2, e = y % g->k2;
    int aa = (int)((a + (long long)g->powr[b] * c) % g->m);
    return aa * g->k2 + (b + e) % g->k2;
}

static int ginv(const Group *g, int x) {
    int a = x / g->k2, b = x % g->k2;
    int nbk = (g->k2 - b) % g->k2;
    int na = (int)((g->m - (long long)g->powr[nbk] * a % g->m) % g->m);
    return na * g->k2 + nbk;
}

/* Random semidirect group Z_m x| Z_k2 with m*k2 >= target; r = 1 gives the direct product. */
static int sample_group(int target, Group *g) {
    static const int K2[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    int k2 = K2[rndint(20)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && rnd01() < 0.8) {
        for (int t = 0; t < 80; t++) {
            int c = 1 + rndint(m - 1);
            if (gcdi(c, m) == 1 && pmod(c, k2, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    g->m = m;
    g->k2 = k2;
    g->G = m * k2;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        g->powr[b] = (int)p;
        p = p * r % m;
    }
    return g->G;
}

/* Recompute all neighbour entries of layer l from perm and sv. */
static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int p = perm[l][i], s = sv[l][i];
        int si = ginv(&grp, s);
        int Ab = i * G, Bb = (K + p) * G;
        for (int g = 0; g < G; g++) {
            nb[l][Ab + g] = Bb + gmul(&grp, g, s);
            nb[l][Bb + g] = Ab + gmul(&grp, g, si);
        }
    }
}

/* Number of duplicated (block, perm, voltage) darts; a duplicate is a multi-edge. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (perm[l][i] == perm[l2][i] && sv[l][i] == sv[l2][i]) c++;
    return c;
}

/* Count unreached (vertex, representative) pairs; leaves the final masks in mk. */
static int eval_unreached(void) {
    for (int v = 0; v < N; v++) mk[v] = 0;
    for (int b = 0; b < 2 * K; b++) mk[b * G] |= (unsigned char)(1u << b);
    unsigned char *cur = mk, *nxt = mk2;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            unsigned char x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nb[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        unsigned char *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    if (cur != mk) memcpy(mk, cur, (size_t)N);
    int un = 0;
    for (int v = 0; v < N; v++) un += 2 * K - __builtin_popcount((unsigned)mk[v]);
    return un;
}

static int total_cost(void) {
    int dc = dupcount();
    int un = eval_unreached();
    return un + PEN * dc;
}

/* Simulated annealing with focused voltage moves and block-permutation swaps.
 * Returns 1 when the lift is valid; the accepted state is then in perm, sv and nb. */
static int sa_run(long iters, long patience, double deadline) {
    int full = (1 << (2 * K)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) sv[l][i] = rndint(G);
        rebuild_layer(l);
    }
    int cost = total_cost();
    memcpy(acc, mk, (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int best = cost;
    long last = 0;

    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double T = 0.02 * c0 * (1.0 - (double)t / (double)iters);
        if (T < 0.3) T = 0.3;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int p1 = perm[l][i1], p2 = perm[l][i2];
            perm[l][i1] = p2;
            perm[l][i2] = p1;
            rebuild_layer(l);
            int c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                memcpy(acc, mk, (size_t)N);
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                perm[l][i1] = p1;
                perm[l][i2] = p2;
                rebuild_layer(l);
                memcpy(mk, acc, (size_t)N);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.5) {
            int start = rndint(N), v = -1;
            for (int q = 0; q < N; q++) {
                int w = start + q;
                if (w >= N) w -= N;
                if (mk[w] != full) {
                    v = w;
                    break;
                }
            }
            if (v >= 0) {
                int b = v / G;
                l = rndint(d);
                if (b < K) {
                    i = b;
                } else {
                    int j = b - K;
                    for (int ii = 0; ii < K; ii++)
                        if (perm[l][ii] == j) {
                            i = ii;
                            break;
                        }
                }
            }
        }
        if (i < 0) {
            l = rndint(d);
            i = rndint(K);
        }

        int old = sv[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        sv[l][i] = nw;
        rebuild_layer(l);
        int c2 = total_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            memcpy(acc, mk, (size_t)N);
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            sv[l][i] = old;
            rebuild_layer(l);
            memcpy(mk, acc, (size_t)N);
        }
    }
    return cost == 0;
}

static void store_best(void) {
    int m = 0, A = K * G;
    for (int l = 0; l < d; l++)
        for (int u = 0; u < A; u++) {
            bu[m] = u;
            bv[m] = nb[l][u];
            m++;
        }
    be_n = N;
    be_m = m;
}

static int pick_k(const int *trials, const int *wins) {
    if (rnd01() < 0.2) return 1 + rndint(4);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= 4; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) {
            bs = s;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    long start_n = atol(argv[5]);
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double deadline = t0 + budget;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long moore = moore_bound(d, D);
    long cap = moore < MAXN ? moore : MAXN;
    double goal = (double)start_n * 1.05;
    if (goal < 2.0 * d) goal = 2.0 * d;
    long found_n = 0;
    int trials[MAXK + 1] = {0};
    int wins[MAXK + 1] = {0};

    while (now() < deadline) {
        if (goal > 0.995 * (double)cap) goal = 0.995 * (double)cap;
        int k = pick_k(trials, wins);
        int target = (int)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        sample_group(target, &grp);
        long NN = 2L * k * grp.G;
        if (NN > cap) continue;
        long bref = found_n > start_n ? found_n : start_n;
        if (NN <= bref) {
            if (goal < (double)bref * 1.02) goal = (double)bref * 1.02;
            continue;
        }
        trials[k]++;
        K = k;
        G = grp.G;
        N = (int)NN;
        double rem = deadline - now();
        double slice = rem / 3.0;
        if (slice < 3.0) slice = 3.0;
        double dl = now() + slice;
        if (dl > deadline) dl = deadline;
        int ok = sa_run(20000, 3000, dl);
        if (ok) {
            wins[k]++;
            found_n = N;
            store_best();
            if (goal < (double)N * 1.04) goal = (double)N * 1.04;
        } else {
            double g2 = (double)bref * 1.02;
            double g3 = goal * 0.99;
            goal = g2 > g3 ? g2 : g3;
        }
    }

    if (found_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", be_n, be_m);
    for (int e = 0; e < be_m; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Lift search in C, using the remaining time. The C engine returns its best lift,
    # which Python validates before keeping.
    if d >= 3:
        remaining = final - time.monotonic() - 3.0
        if remaining > 3.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                                 timeout=remaining + 20.0)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
