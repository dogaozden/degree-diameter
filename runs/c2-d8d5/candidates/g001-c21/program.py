import itertools
import time

import lib


# The C engine performs a bi-Cayley lift search over Z_m x| Z_k2 (element (a,b) coded as a*k2+b,
# (a,b)(c,e) = (a + r^b c, b+e)). A base of k vertices per side with d layers gives a d-regular
# bipartite graph on 2*k*G vertices, where every layer is a permutation of the k A-blocks and
# carries a voltage per A-block.
#
# Search: simulated annealing on the unreached (block-representative, vertex) pairs plus a duplicate-edge
# penalty. New in this version: iterated local search with elite restarts. When a trial stagnates,
# it restores its best state and applies a kick (re-randomise one layer, or perturb a few voltages)
# instead of restarting from scratch. The C engine also ramps the target order up by itself: every
# success raises the bar, so it keeps searching for graphs larger than the best found so far.

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 6
#define MAXG 2500
#define MAXN (2 * MAXK * MAXG)
#define PEN 1000L
#define ITERS 80000L
#define PATIENCE 2500L
#define NK2 19

static int dd, DD;
static int K, G, M, K2, R, N;
static int *Ts = NULL, *Invs = NULL;
static int lay[MAXD * MAXK], vol[MAXD * MAXK];
static int bestLay[MAXD * MAXK], bestVol[MAXD * MAXK];
static int mvLay[MAXD * MAXK], mvVol[MAXD * MAXK];
static int adj[MAXN * MAXD];
static uint32_t S1[MAXN], S2[MAXN], RA[MAXN], RB[MAXN];
static int pw[64];
static uint64_t rs = 1;
static double t_end = 0.0;
static const int KS[MAXK] = {1, 2, 3, 4, 5, 6};
static const int K2LIST[NK2] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static uint64_t nextr(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rint_(int n) { return (int)((nextr() >> 11) % (uint64_t)n); }
static double rdbl(void) { return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int pc32(uint32_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int a2 = (int)(((long long)a + (long long)pw[b] * c) % M);
    return a2 * K2 + (b + e) % K2;
}

/* Builds the multiplication table tables Ts[s][g] = g*s and Invs[s][h] = g with g*s = h. */
static int build_group(void) {
    G = M * K2;
    N = 2 * K * G;
    for (int t = 0; t < K2; t++) pw[t] = (int)powmod_(R, t, M);
    free(Ts);
    free(Invs);
    Ts = malloc(sizeof(int) * (size_t)G * G);
    Invs = malloc(sizeof(int) * (size_t)G * G);
    if (!Ts || !Invs) return 0;
    for (int s = 0; s < G; s++)
        for (int g = 0; g < G; g++) {
            int h = gmul(g, s);
            Ts[(size_t)s * G + g] = h;
            Invs[(size_t)s * G + h] = g;
        }
    return 1;
}

/* Writes layer l's darts for A-block i and for the B-block it is matched to. */
static void set_dart(int l, int i) {
    int idx = l * K + i, j = lay[idx], s = vol[idx];
    const int *T = Ts + (size_t)s * G;
    const int *I = Invs + (size_t)s * G;
    int Bbase = (K + j) * G;
    for (int g = 0; g < G; g++) {
        adj[(size_t)(i * G + g) * dd + l] = Bbase + T[g];
        adj[(size_t)(Bbase + g) * dd + l] = i * G + I[g];
    }
}

static void rewrite_all(void) {
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static void shuffle_layer(int l) {
    int p[MAXK];
    for (int i = 0; i < K; i++) p[i] = i;
    for (int i = K - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = p[i]; p[i] = p[j]; p[j] = t;
    }
    for (int i = 0; i < K; i++) {
        lay[l * K + i] = p[i];
        vol[l * K + i] = rint_(G);
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < dd; l++)
            for (int l2 = l + 1; l2 < dd; l2++) {
                int a = l * K + i, b = l2 * K + i;
                if (lay[a] == lay[b] && vol[a] == vol[b]) c++;
            }
    return c;
}

/* Fills res with the reach bitmask of every vertex (bit b = block representative b within D).
   Returns the number of unreached (representative, vertex) pairs. */
static long eval_cost(uint32_t *res) {
    uint32_t *cur = S1, *nxt = S2, *tmp;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[(size_t)b * G] = 1u << b;
    for (int t = 0; t < DD; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            const int *a = &adj[(size_t)v * dd];
            for (int l = 0; l < dd; l++) x |= cur[a[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    memcpy(res, cur, sizeof(uint32_t) * (size_t)N);
    long unr = 0;
    int full = 2 * K;
    for (int v = 0; v < N; v++) unr += full - pc32(res[v]);
    return unr;
}

static long full_cost(uint32_t *res) {
    return eval_cost(res) + PEN * (long)dupcount();
}

/* Picks a (layer, A-block) pair; with prob 0.4 it is aimed at a defective vertex. */
static void pick_pair(const uint32_t *R0, int *pl, int *pi) {
    if (rdbl() < 0.4) {
        uint32_t fullm = (1u << (2 * K)) - 1;
        int u = -1;
        for (int tries = 0; tries < 40; tries++) {
            int v = rint_(N);
            if (R0[v] != fullm) { u = v; break; }
        }
        if (u >= 0) {
            int block = u / G;
            int l = rint_(dd);
            int i = -1;
            if (block < K) {
                i = block;
            } else {
                int j = block - K;
                for (int ii = 0; ii < K; ii++)
                    if (lay[l * K + ii] == j) { i = ii; break; }
            }
            if (i >= 0) { *pl = l; *pi = i; return; }
        }
    }
    *pl = rint_(dd);
    *pi = rint_(K);
}

/* Kick used by the iterated local search: re-randomise a layer, or perturb a few voltages. */
static void kick(void) {
    if (rint_(2) == 0) {
        shuffle_layer(rint_(dd));
    } else {
        int c = 2 + rint_(3);
        for (int q = 0; q < c; q++) {
            int l = rint_(dd), i = rint_(K);
            vol[l * K + i] = rint_(G);
        }
    }
    rewrite_all();
}

/* One annealing trial with elite restarts. Returns 1 if a valid graph (cost 0) is in lay/vol/adj. */
static int trial(long iters, long patience) {
    for (int l = 0; l < dd; l++) shuffle_layer(l);
    rewrite_all();
    uint32_t *Rcur = RA, *Rcand = RB, *tmp;
    long cost = full_cost(Rcur);
    long bestC = cost;
    double T0 = 0.02 * (double)cost;
    if (T0 < 1.0) T0 = 1.0;
    memcpy(bestLay, lay, sizeof lay);
    memcpy(bestVol, vol, sizeof vol);
    long last = 0;

    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if ((t & 255) == 0 && now() > t_end) break;

        if (t - last > patience) {
            memcpy(lay, bestLay, sizeof lay);
            memcpy(vol, bestVol, sizeof vol);
            kick();
            cost = full_cost(Rcur);
            last = t;
            continue;
        }

        double frac = (double)t / (double)iters;
        double T = T0 * (1.0 - frac) + 0.15;
        int touchL[4], touchI[4], nt = 0;
        memcpy(mvLay, lay, sizeof lay);
        memcpy(mvVol, vol, sizeof vol);
        double x = rdbl();

        if (K >= 2 && x < 0.15) {
            int l = rint_(dd), i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int a = l * K + i1, b = l * K + i2;
            int sw = lay[a]; lay[a] = lay[b]; lay[b] = sw;
            touchL[nt] = l; touchI[nt] = i1; nt++;
            touchL[nt] = l; touchI[nt] = i2; nt++;
        } else {
            int reps = (x > 0.92) ? 2 : 1;
            for (int q = 0; q < reps; q++) {
                int l, i;
                pick_pair(Rcur, &l, &i);
                int idx = l * K + i;
                int old = vol[idx], nv;
                do { nv = rint_(G); } while (nv == old);
                vol[idx] = nv;
                touchL[nt] = l; touchI[nt] = i; nt++;
            }
        }
        for (int q = 0; q < nt; q++) set_dart(touchL[q], touchI[q]);

        long c2 = full_cost(Rcand);
        int acc = (c2 <= cost) || (rdbl() < exp(-(double)(c2 - cost) / T));
        if (acc) {
            tmp = Rcur; Rcur = Rcand; Rcand = tmp;
            cost = c2;
            if (cost < bestC) {
                bestC = cost;
                last = t;
                memcpy(bestLay, lay, sizeof lay);
                memcpy(bestVol, vol, sizeof vol);
            }
        } else {
            memcpy(lay, mvLay, sizeof lay);
            memcpy(vol, mvVol, sizeof vol);
            for (int q = 0; q < nt; q++) set_dart(touchL[q], touchI[q]);
        }
    }
    return cost == 0;
}

static int pick_k(const int *wins, const int *trials) {
    if (rdbl() < 0.2) return rint_(MAXK);
    int best = 0;
    double bv = -1.0;
    for (int i = 0; i < MAXK; i++) {
        double v = (wins[i] + 1.0) / (trials[i] + 2.0) + 0.02 * rdbl();
        if (v > bv) { bv = v; best = i; }
    }
    return best;
}

static int pick_R(void) {
    if (K2 == 1) return 1;
    if (K2 == 2 && rdbl() < 0.3) return (M - 1 >= 1) ? M - 1 : 1;
    if (M < 3) return 1;
    for (int tries = 0; tries < 200; tries++) {
        int c = 2 + rint_(M - 2);
        if (gcd_(c, M) == 1 && powmod_(c, K2, M) == 1 % M) return c;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) nextr();
    t_end = now() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (m0 < 0) m0 = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    int read_m = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        read_m++;
    }
    m0 = read_m;

    long bestN = n0;
    int have = 0;
    int *ou = NULL, *ov = NULL;
    int om = 0, on = 0;

    if (dd >= 2 && dd <= MAXD && DD >= 2) {
        int wins[MAXK] = {0}, trials[MAXK] = {0};
        while (now() < t_end) {
            int ki = pick_k(wins, trials);
            K = KS[ki];
            long Gmin = bestN / (2L * K) + 1;
            Gmin += rint_((int)(Gmin / 12 + 2));
            K2 = K2LIST[rint_(NK2)];
            long Ml = (Gmin + K2 - 1) / K2;
            if (Ml < 2) Ml = 2;
            M = (int)Ml;
            if (M * K2 > MAXG) continue;
            R = pick_R();
            if (!build_group()) break;
            trials[ki]++;
            if (trial(ITERS, PATIENCE)) {
                wins[ki]++;
                long newN = 2L * K * G;
                if (newN > bestN) {
                    bestN = newN;
                    have = 1;
                    free(ou);
                    free(ov);
                    int nA = K * G;
                    om = nA * dd;
                    on = N;
                    ou = malloc(sizeof(int) * (size_t)om);
                    ov = malloc(sizeof(int) * (size_t)om);
                    int c = 0;
                    for (int v = 0; v < nA; v++)
                        for (int l = 0; l < dd; l++) {
                            ou[c] = v;
                            ov[c] = adj[(size_t)v * dd + l];
                            c++;
                        }
                }
            }
        }
    }

    if (have) {
        printf("%d %d\n", on, om);
        for (int i = 0; i < om; i++) printf("%d %d\n", ou[i], ov[i]);
    } else if (n0 > 0) {
        printf("%d %d\n", n0, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search in C, starting from the best graph found so far.
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    remaining = time_limit - (time.monotonic() - t0)
    budget = min(budget, remaining - 6.0)
    if budget >= 1.0:
        try:
            text = lib.run_c(
                C_SOURCE,
                [d, D, seed, f"{budget:.2f}"],
                stdin_graph=best,
                timeout=max(1.0, time_limit - (time.monotonic() - t0) - 3.0),
            )
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
