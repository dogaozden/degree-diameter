import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: a DIFFERENT search from the parent's breakout local search.
#
# Single-class bi-Cayley lifts over a group G = Z_m x|_r Z_k with connection
# set S = {s_1..s_d} (distinct). Vertices A_x = x and B_y = G + y; edge
# A_x -- B_{x*s_l}. Left translation by h acts transitively on each side and
# preserves edges, so the diameter condition reduces to two BFS runs: one from
# A_0 and one from B_0, each of depth D. The cost is the number of vertices not
# reached. Simulated annealing moves one connection element at a time. Each
# group order G is tried in a slice; the order climbs by one after each success
# and falls back if the start order fails.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 64
#define MAXGRP 2000
#define SA_ITERS 60000
#define T0 2.5
#define T1 0.05

typedef struct {
    int G, m, k, r;
    int s[MAXDEG];
} Best;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static double deadline = 0.0;

static int G = 1, GM = 1, GK = 1, GR = 1;
static int gpow_[MAXGRP + 1];
static int *MUL = NULL, *INV = NULL;
static int capMUL = 0;
static int *Q = NULL, *VIS = NULL;
static int capV = 0;
static int stamp = 0;

static int build_group(int m, int k, int r) {
    int g = m * k;
    if (g > MAXGRP || g < 4 || m < 1 || k < 1) return 0;
    GM = m;
    GK = k;
    GR = r;
    G = g;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow_[b] = (int)p;
        p = (p * r) % m;
    }
    if (capMUL < g * g) {
        free(MUL);
        free(INV);
        MUL = malloc(sizeof(int) * (size_t)g * (size_t)g);
        INV = malloc(sizeof(int) * (size_t)g);
        if (!MUL || !INV) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        capMUL = g * g;
    }
    if (capV < 2 * g) {
        free(Q);
        free(VIS);
        Q = malloc(sizeof(int) * (size_t)(2 * g));
        VIS = calloc((size_t)(2 * g), sizeof(int));
        if (!Q || !VIS) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        capV = 2 * g;
        stamp = 0;
    }
    for (int x = 0; x < g; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < g; y++) {
            int c = y / k, d = y % k;
            int t = (int)(((long long)a + (long long)gpow_[b] * (long long)c) % m);
            MUL[x * g + y] = t * k + (b + d) % k;
        }
    }
    for (int x = 0; x < g; x++) INV[x] = -1;
    for (int x = 0; x < g; x++)
        for (int y = 0; y < g; y++)
            if (MUL[x * g + y] == 0) INV[x] = y;
    for (int x = 0; x < g; x++)
        if (INV[x] < 0) return 0;
    return 1;
}

/* Number of vertices not reached within DD steps from src. */
static int bfs_unreached(int src, const int *s, const int *si, int d) {
    int g = G;
    if (stamp > 2000000000) {
        memset(VIS, 0, sizeof(int) * (size_t)(2 * g));
        stamp = 0;
    }
    stamp++;
    int head = 0, tail = 0;
    Q[tail++] = src;
    VIS[src] = stamp;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = Q[head++];
            if (u < g) {
                const int *row = MUL + (size_t)u * (size_t)g;
                for (int l = 0; l < d; l++) {
                    int v = g + row[s[l]];
                    if (VIS[v] != stamp) {
                        VIS[v] = stamp;
                        Q[tail++] = v;
                    }
                }
            } else {
                int y = u - g;
                const int *row = MUL + (size_t)y * (size_t)g;
                for (int l = 0; l < d; l++) {
                    int v = row[si[l]];
                    if (VIS[v] != stamp) {
                        VIS[v] = stamp;
                        Q[tail++] = v;
                    }
                }
            }
        }
    }
    return 2 * g - tail;
}

static int cost_of(const int *s, const int *si, int d) {
    return bfs_unreached(0, s, si, d) + bfs_unreached(G, s, si, d);
}

static int pick_new(const int *s, int count, int g) {
    for (;;) {
        int v = rint_(g);
        int dup = 0;
        for (int q = 0; q < count; q++) {
            if (s[q] == v) {
                dup = 1;
                break;
            }
        }
        if (!dup) return v;
    }
}

static int sa_run(int *s, int *si) {
    int d = Dd, g = G;
    if (g < 2 * d) return 0;
    for (int l = 0; l < d; l++) {
        s[l] = pick_new(s, l, g);
        si[l] = INV[s[l]];
    }
    int cur = cost_of(s, si, d);
    for (long t = 0; t < SA_ITERS && cur > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)SA_ITERS);
        int l = rint_(d);
        int v = pick_new(s, d, g);
        int ov = s[l], oi = si[l];
        s[l] = v;
        si[l] = INV[v];
        int nc = cost_of(s, si, d);
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            s[l] = ov;
            si[l] = oi;
        }
    }
    return cur == 0;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20,
                         21, 24, 27, 28, 30, 32, 36, 40, 48, 56, 64};

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void sample_group(int g, int *om, int *ok, int *orr) {
    int cands[64], nc = 0;
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    for (int i = 0; i < nk; i++) {
        if (g % KF[i] == 0 && g / KF[i] >= 2) cands[nc++] = KF[i];
    }
    int k = cands[rint_(nc)];
    int m = g / k;
    int r = 1;
    if (k > 1) {
        int found = 0;
        for (int t = 0; t < 300; t++) {
            int c = 1 + rint_(m - 1);
            if (gcd_i(c, m) == 1 && powmod_ll(c, k, m) == 1 % m) {
                r = c;
                found = 1;
                break;
            }
        }
        if (!found) {
            k = 1;
            m = g;
            r = 1;
        }
    }
    *om = m;
    *ok = k;
    *orr = r;
}

static int try_G(int g, double t_end, Best *out) {
    int s[MAXDEG], si[MAXDEG];
    while (now_s() < t_end && now_s() < deadline) {
        int m, k, r;
        sample_group(g, &m, &k, &r);
        if (!build_group(m, k, r)) continue;
        if (sa_run(s, si)) {
            out->G = G;
            out->m = m;
            out->k = k;
            out->r = r;
            memcpy(out->s, s, sizeof(int) * (size_t)Dd);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int start_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXDEG || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    double slice = 0.1 * tl;
    if (slice < 0.5) slice = 0.5;

    int g = start_n / 2;
    if (g < 2 * Dd) g = 2 * Dd;
    if (g > MAXGRP) g = MAXGRP;

    Best best, cand;
    int found = 0;
    while (!found && now_s() < deadline) {
        if (try_G(g, now_s() + slice, &cand)) {
            found = 1;
            best = cand;
        } else {
            int step = g / 50;
            if (step < 1) step = 1;
            g -= step;
            if (g < 2 * Dd) break;
        }
    }

    if (found) {
        while (now_s() < deadline && best.G + 1 <= MAXGRP) {
            if (try_G(best.G + 1, now_s() + slice, &cand)) {
                best = cand;
            } else {
                break;
            }
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }

    build_group(best.m, best.k, best.r);
    int gg = best.G;
    printf("%d %d\n", 2 * gg, Dd * gg);
    for (int l = 0; l < Dd; l++) {
        for (int x = 0; x < gg; x++) {
            printf("%d %d\n", x, gg + MUL[x * gg + best.s[l]]);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer, always with a
# valid fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Araujo-Pardo and Lopez record family for d = q + 2 (diameter 3, valid for D >= 3).
    if D >= 3 and d >= 5 and lib.is_prime_power(d - 2) and not lib.is_prime_power(d - 1):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Single-class bi-Cayley lifts over semidirect products, searched by
    # simulated annealing with a two-BFS diameter test. The start order is a
    # fraction of the Moore bound, so the C engine descends or climbs from there.
    if d >= 3 and D >= 3 and time.monotonic() < deadline:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            try:
                moore = lib.moore_bound(d, D)
                start_n = max(best_n, int(0.33 * moore))
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", start_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
