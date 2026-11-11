import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# One C program, two engines.
#
# Mode "L" (argv[1] == "L"): bi-Cayley lift annealer. The graph is a lift of a
# base bipartite multigraph with K vertices per side over the semidirect
# product G = Z_m x| Z_k2 (element a*k2+b). Each of the d layers is a
# permutation of the K A-bases onto the K B-bases, with one group voltage per
# dart. Left multiplication by G is an automorphism, so the distance cost only
# needs BFS from one representative per base block (2K BFS runs instead of N).
# Cost = unreached/too-far pairs from those representatives + duplicate-dart
# penalty.
#
# Mode otherwise: the edge-toggle annealer with vertex growth (parent engine).
# It reads a start graph on stdin and grows a valid graph by vertex pairs.
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

/* ============================ edge annealer ============================ */

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

static int edge_main(int argc, char **argv) {
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

/* ============================ bi-Cayley lift annealer ============================ */

static int LK, LM, LK2, LR, LG, LN, LDEG, LDIAM;
static int *Lpow;    /* Lpow[t] = LR^t mod LM */
static int *lay;     /* lay[l*LK + i] = B-base of A-base i in layer l */
static int *vol;     /* vol[l*LK + i] = voltage of that dart */
static int *invlay;  /* invlay[l*LK + j] = A-base i with lay[l*LK+i] == j */
static int *nbrL;    /* nbrL[v*LDEG + l] = neighbour of v in layer l */
static int *dist, *qu;

static int gmul(int x, int y) {
    int a1 = x / LK2, b1 = x - a1 * LK2;
    int a2 = y / LK2, b2 = y - a2 * LK2;
    long long t = (long long)Lpow[b1] * a2 + a1;
    int a = (int)(t % LM);
    int b = (b1 + b2) % LK2;
    return a * LK2 + b;
}

static int ginv(int x) {
    int a = x / LK2, b = x - a * LK2;
    int nb = (LK2 - b) % LK2;
    long long t = ((long long)(LM - Lpow[nb]) % LM) * a % LM;
    return (int)t * LK2 + nb;
}

static void build_nbr(void) {
    for (int l = 0; l < LDEG; l++)
        for (int i = 0; i < LK; i++)
            invlay[l * LK + lay[l * LK + i]] = i;
    for (int b = 0; b < LK; b++)
        for (int x = 0; x < LG; x++) {
            int v = b * LG + x;
            for (int l = 0; l < LDEG; l++) {
                int j = lay[l * LK + b];
                nbrL[v * LDEG + l] = (LK + j) * LG + gmul(x, vol[l * LK + b]);
            }
        }
    for (int j = 0; j < LK; j++)
        for (int y = 0; y < LG; y++) {
            int v = (LK + j) * LG + y;
            for (int l = 0; l < LDEG; l++) {
                int i = invlay[l * LK + j];
                nbrL[v * LDEG + l] = i * LG + gmul(y, ginv(vol[l * LK + i]));
            }
        }
}

static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < LK; i++)
        for (int l1 = 0; l1 < LDEG; l1++)
            for (int l2 = l1 + 1; l2 < LDEG; l2++)
                if (lay[l1 * LK + i] == lay[l2 * LK + i] && vol[l1 * LK + i] == vol[l2 * LK + i])
                    c++;
    return c;
}

/* Cost = duplicate darts (heavy) + pairs not within LDIAM, counted from the block representatives. */
static long long lift_cost(void) {
    long long c = (long long)dup_count() * 50;
    build_nbr();
    int NN = LN;
    for (int b = 0; b < 2 * LK; b++) {
        int src = b * LG;
        for (int v = 0; v < NN; v++) dist[v] = -1;
        int h = 0, t = 0, seen = 1;
        dist[src] = 0;
        qu[t++] = src;
        while (h < t) {
            int v = qu[h++];
            int dv = dist[v];
            if (dv >= LDIAM) continue;
            for (int l = 0; l < LDEG; l++) {
                int u = nbrL[v * LDEG + l];
                if (dist[u] < 0) {
                    dist[u] = dv + 1;
                    qu[t++] = u;
                    seen++;
                }
            }
        }
        c += NN - seen;
    }
    return c;
}

static void lift_random(void) {
    int *perm = malloc(sizeof(int) * LK);
    for (int l = 0; l < LDEG; l++) {
        for (int i = 0; i < LK; i++) perm[i] = i;
        for (int i = LK - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < LK; i++) {
            lay[l * LK + i] = perm[i];
            vol[l * LK + i] = rint_(LG);
        }
    }
    free(perm);
}

static void lift_output(void) {
    int NA = LK * LG;
    long long m = (long long)NA * LDEG;
    printf("%d %lld\n", LN, m);
    for (int v = 0; v < NA; v++)
        for (int l = 0; l < LDEG; l++)
            printf("%d %d\n", v, nbrL[v * LDEG + l]);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int lift_fail(void) {
    printf("0 0\n");
    return 0;
}

/* argv: L d D seed limit k m k2 r */
static int lift_main(int argc, char **argv) {
    if (argc < 10) return lift_fail();
    LDEG = atoi(argv[2]);
    LDIAM = atoi(argv[3]);
    rs ^= (u64)strtoull(argv[4], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[5]);
    LK = atoi(argv[6]);
    LM = atoi(argv[7]);
    LK2 = atoi(argv[8]);
    LR = atoi(argv[9]);
    if (LDEG < 1 || LDEG > 64 || LDIAM < 1 || LK < 1 || LK > 64) return lift_fail();
    if (LM < 3 || LM > 100000 || LK2 < 1 || LK2 > 64) return lift_fail();
    if (LR < 1 || LR >= LM || gcd_i(LR, LM) != 1) return lift_fail();
    long long pw = 1 % LM;
    for (int t = 0; t < LK2; t++) pw = pw * LR % LM;
    if (pw != 1 % LM) return lift_fail();

    LG = LM * LK2;
    LN = 2 * LK * LG;
    if (LN > 200000) return lift_fail();

    Lpow = malloc(sizeof(int) * LK2);
    lay = malloc(sizeof(int) * LK * LDEG);
    vol = malloc(sizeof(int) * LK * LDEG);
    invlay = malloc(sizeof(int) * LK * LDEG);
    nbrL = malloc(sizeof(int) * (size_t)LN * LDEG);
    dist = malloc(sizeof(int) * LN);
    qu = malloc(sizeof(int) * LN);
    if (!Lpow || !lay || !vol || !invlay || !nbrL || !dist || !qu) return lift_fail();

    Lpow[0] = 1 % LM;
    for (int t = 1; t < LK2; t++) Lpow[t] = (int)((long long)Lpow[t - 1] * LR % LM);

    const double T0 = 6.0, T1 = 0.4;
    const int ITERS = 20000;
    clock_t c0 = clock();
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        lift_random();
        long long cost = lift_cost();
        for (int it = 0; it < ITERS && cost != 0; it++) {
            if ((it & 31) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC >= limit) break;
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            if (rdbl() < 0.5) {
                int idx = rint_(LDEG * LK);
                int old = vol[idx];
                int nv = rint_(LG);
                if (nv == old) continue;
                vol[idx] = nv;
                long long nc = lift_cost();
                if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
                else vol[idx] = old;
            } else {
                if (LK < 2) continue;
                int l = rint_(LDEG);
                int i1 = rint_(LK), i2 = rint_(LK);
                if (i1 == i2) continue;
                int a = l * LK + i1, b = l * LK + i2;
                int t = lay[a]; lay[a] = lay[b]; lay[b] = t;
                long long nc = lift_cost();
                if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
                else { t = lay[a]; lay[a] = lay[b]; lay[b] = t; }
            }
        }
        if (cost == 0) {
            build_nbr();
            lift_output();
            return 0;
        }
    }
    return lift_fail();
}

int main(int argc, char **argv) {
    if (argc >= 2 && argv[1][0] == 'L' && argv[1][1] == '\0') return lift_main(argc, argv);
    return edge_main(argc, argv);
}
"""


# ----------------------------------------------------------------------------
# Python glue and constructions.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5)
_K2S = (2, 3, 4, 5, 6, 8, 9, 10, 12)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_options(G, rng):
    """Groups Z_m x| Z_k2 of order G = m*k2. The first option is always cyclic."""
    opts = [(G, 1, 1)]
    for k2 in _K2S:
        if G % k2:
            continue
        m = G // k2
        if m < 3:
            continue
        cands = [x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k2, m) == 1]
        if not cands:
            continue
        for r in rng.sample(cands, min(2, len(cands))):
            opts.append((m, k2, r))
    return opts


def _lift_in_c(d, D, k, opt, seed, seconds):
    """Run the C lift annealer for base size k over the group opt = (m, k2, r). Returns (n, edges) or None."""
    m, k2, r = opt
    out = lib.run_c(C_SOURCE, ["L", d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 15.0)
    n, e = lib.parse_graph_text(out)
    if n < 2 or not e:
        return None
    return n, e


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C edge annealer from a valid graph; returns parsed (n, edges) (may be (0, []))."""
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

    # Phase 1: C bi-Cayley lift search, growing the order one group step at a time.
    lift_end = t0 + max(1.0, 0.7 * time_limit - 2.0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    errors = 0

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while errors < 3:
        remaining = lift_end - time.monotonic()
        if remaining < 0.8:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        G = base + 1 + rng.randrange(0, max(1, base // 60))
        opts = _group_options(G, rng)
        cyc, nonc = opts[0], opts[1:]
        if nonc and rng.random() < 0.7:
            opt = rng.choice(nonc)
        else:
            opt = cyc
        slice_s = min(remaining, max(1.5, 0.12 * (lift_end - t0)))
        trials[k] += 1
        try:
            res = _lift_in_c(d, D, k, opt, rng.randrange(1, 1 << 30), slice_s)
        except Exception:
            res = None
            errors += 1
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: C edge annealer grows the best valid graph by vertex pairs.
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
