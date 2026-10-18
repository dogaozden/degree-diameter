"""Multi-orbit voltage lifts over several group families for the bipartite degree-diameter problem.

Idea: the parent searches only single-orbit Haar graphs (base = one left and one right vertex)
over affine groups. This version uses base multigraphs with B = 1..4 left and B right
vertices. Each base vertex has d darts, one per layer t. Layer t sends left u to right
sigma_t(u), where sigma_t is a random permutation, so every right vertex also gets d darts.
Each dart carries a voltage in a group G, and the lift has 2*B*|G| vertices and is d-regular
and bipartite.

Left multiplication by G is an automorphism of each lift, so the diameter is decided by
2B BFS runs, one from each fiber's identity. The C engine uses simulated annealing over the
voltages, with fresh random layer permutations at each restart. Candidate groups are cyclic,
semidirect Z_m x| Z_k, and affine F_p x| H_c with p prime. Candidates are binary-searched by
total order, as in the parent, and then extended upward.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines. Every returned
graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*B*|G|.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1700
#define MAXB 4
#define MAXDD 16
#define MAXV (2 * MAXB * MAXG)
#define MAXCAND 200000
#define ITERS 1500

typedef struct { int total, G, b, type, x, y, z; unsigned key; } Cand;
/* type 0: cyclic Z_G (x = G). type 1: Z_m x| Z_k (x = m, y = k, z = r). type 2: F_p x| H_c (x = p, y = c). */

static int d, D, B;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static Cand *cand;
static int nc = 0;

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
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ groups */

static int MT[MAXG * MAXG];
static int INV[MAXG];
static int GN;

static long powmod(long a, long e, long m) {
    long r = 1 % m;
    a %= m;
    while (e > 0) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int is_prime_i(int n) {
    if (n < 2) return 0;
    for (int f = 2; f * f <= n; f++)
        if (n % f == 0) return 0;
    return 1;
}

static void build_group(const Cand *c) {
    int G = c->G;
    GN = G;
    if (c->type == 0) {
        for (int x = 0; x < G; x++)
            for (int y = 0; y < G; y++)
                MT[x * G + y] = (x + y) % G;
    } else if (c->type == 1) {
        int m = c->x, k = c->y, r = c->z;
        int pw[MAXG];
        pw[0] = 1 % m;
        for (int i = 1; i < k; i++) pw[i] = (int)((long)pw[i - 1] * r % m);
        for (int x = 0; x < G; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < G; y++) {
                int cc = y / k, dd = y % k;
                int na = (int)(((long)a + (long)pw[b] * cc) % m);
                int nb = (b + dd) % k;
                MT[x * G + y] = na * k + nb;
            }
        }
    } else {
        int p = c->x, cc = c->y;
        int g;
        for (g = 2; g < p; g++) {
            long xx = g;
            int ord = 1;
            while (xx != 1) { xx = xx * g % p; ord++; }
            if (ord == p - 1) break;
        }
        int s = (p - 1) / cc;
        int Hel[MAXG];
        for (int j = 0; j < cc; j++) Hel[j] = (int)powmod(g, (long)j * s, p);
        for (int x = 0; x < G; x++) {
            int a = x / cc, j = x % cc;
            for (int y = 0; y < G; y++) {
                int bb = y / cc, t = y % cc;
                int na = (int)(((long)a + (long)Hel[j] * bb) % p);
                int nt = (j + t) % cc;
                MT[x * G + y] = na * cc + nt;
            }
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) INV[x] = y;
}

/* ------------------------------------------------------------ lift state */

static int sig[MAXDD][MAXB], sinv[MAXDD][MAXB], vol[MAXDD][MAXB];
static int fsig[MAXDD][MAXB], fvol[MAXDD][MAXB];
static int bsig[MAXDD][MAXB], bvol[MAXDD][MAXB];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int bestIdx = -1, bestTotal = 0;

/* Number of vertices within distance D of src. */
static int reach_count(int src) {
    int G = GN, BG = B * G;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BG) {
                int u = v / G, x = v - u * G;
                for (int t = 0; t < d; t++) {
                    int w = BG + sig[t][u] * G + MT[x * G + vol[t][u]];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            } else {
                int r = v - BG;
                int wv = r / G, y = r - wv * G;
                for (int t = 0; t < d; t++) {
                    int u = sinv[t][wv];
                    int w = u * G + MT[y * G + INV[vol[t][u]]];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Fiber transitivity: BFS from one identity vertex per base vertex suffices. */
static long cover_cost(void) {
    int G = GN, V = 2 * B * G;
    long c = 0;
    for (int u = 0; u < B; u++) c += V - reach_count(u * G);
    for (int v = 0; v < B; v++) c += V - reach_count(B * G + v * G);
    return c;
}

/* Voltage g on dart (t,u) keeps the graph simple: darts from u with equal targets need distinct voltages. */
static int ok_volt(int t, int u, int g) {
    for (int t2 = 0; t2 < d; t2++)
        if (t2 != t && sig[t2][u] == sig[t][u] && vol[t2][u] == g) return 0;
    return 1;
}

static void random_sigma(void) {
    for (int t = 0; t < d; t++) {
        int perm[MAXB];
        for (int u = 0; u < B; u++) perm[u] = u;
        for (int u = B - 1; u > 0; u--) {
            int j = rndint(u + 1);
            int tmp = perm[u]; perm[u] = perm[j]; perm[j] = tmp;
        }
        for (int u = 0; u < B; u++) {
            sig[t][u] = perm[u];
            sinv[t][perm[u]] = u;
        }
    }
}

static int init_volt(void) {
    for (int t = 0; t < d; t++)
        for (int u = 0; u < B; u++) vol[t][u] = -1;
    for (int t = 0; t < d; t++)
        for (int u = 0; u < B; u++) {
            int tries = 0, g;
            do {
                g = rndint(GN);
                tries++;
            } while (!ok_volt(t, u, g) && tries < 100000);
            if (tries >= 100000) return 0;
            vol[t][u] = g;
        }
    return 1;
}

static void save_found(void) {
    memcpy(fsig, sig, sizeof sig);
    memcpy(fvol, vol, sizeof vol);
}

/* Simulated annealing over the voltages for the current group and base size.
 * Returns 1 when cost 0 (diameter <= D) is reached, 0 on timeout. */
static int search_candidate(double until) {
    int G = GN;
    while (now() < until) {
        random_sigma();
        if (!init_volt()) continue;
        long cost = cover_cost();
        if (cost == 0) { save_found(); return 1; }
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int t = rndint(d), u = rndint(B);
            int g = rndint(G);
            if (g == vol[t][u] || !ok_volt(t, u, g)) continue;
            int old = vol[t][u];
            vol[t][u] = g;
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                vol[t][u] = old;
            }
        }
        if (cost == 0) { save_found(); return 1; }
    }
    return 0;
}

static int try_cand(int i, double until) {
    build_group(&cand[i]);
    B = cand[i].b;
    if (search_candidate(until)) {
        if (cand[i].total > bestTotal) {
            bestTotal = cand[i].total;
            bestIdx = i;
            memcpy(bsig, fsig, sizeof bsig);
            memcpy(bvol, fvol, sizeof bvol);
        }
        return 1;
    }
    return 0;
}

static void print_result(const Cand *c) {
    build_group(c);
    int b = c->b, G = c->G, BG = b * G;
    printf("%d %d\n", 2 * BG, BG * d);
    for (int u = 0; u < b; u++)
        for (int x = 0; x < G; x++)
            for (int t = 0; t < d; t++) {
                int left = u * G + x;
                int right = BG + bsig[t][u] * G + MT[x * G + bvol[t][u]];
                printf("%d %d\n", left, right);
            }
}

static void add_cand(int G, int b, int type, int x, int y, int z) {
    if (nc >= MAXCAND) return;
    Cand c;
    c.total = 2 * b * G;
    c.G = G; c.b = b; c.type = type; c.x = x; c.y = y; c.z = z;
    c.key = (unsigned)rnd();
    cand[nc++] = c;
}

static int cmp_cand(const void *A, const void *Bp) {
    const Cand *a = A, *b = Bp;
    if (a->total != b->total) return a->total < b->total ? -1 : 1;
    if (a->key != b->key) return a->key < b->key ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    cand = malloc(sizeof(Cand) * MAXCAND);
    if (!cand) { printf("0 0\n"); return 0; }

    for (int b = 1; b <= MAXB; b++) {
        long Gmin = (lo + 2L * b - 1) / (2L * b);
        long Gmax = hi / (2L * b);
        if (Gmax > MAXG) Gmax = MAXG;
        if (Gmin < d) Gmin = d;
        if (Gmin < 2) Gmin = 2;
        for (int G = (int)Gmin; G <= Gmax; G++) {
            if (2L * b * G < lo || 2L * b * G > hi) continue;
            add_cand(G, b, 0, G, 0, 0);
            for (int m = 2; m <= G / 2; m++) {
                if (G % m) continue;
                int k = G / m;
                if (k < 2) continue;
                for (int r = 1; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod(r, k, m) != 1 % m) continue;
                    add_cand(G, b, 1, m, k, r);
                }
            }
            for (int p = 3; p <= G / 2; p++) {
                if (G % p) continue;
                if (!is_prime_i(p)) continue;
                int cc = G / p;
                if (cc < 2 || (p - 1) % cc != 0) continue;
                add_cand(G, b, 2, p, cc, 0);
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Phase 1: binary search over candidates sorted by total order. Each probe gets an
     * equal share of the remaining time over the probes still needed. */
    int a = 0, bb = nc - 1;
    while (a <= bb && now() < t_end) {
        int mid = (a + bb) / 2;
        int span = bb - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        if (rem <= 0) break;
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (try_cand(mid, now() + slice)) a = mid + 1;
        else bb = mid - 1;
    }

    /* Phase 2: spend leftover time on the next candidates above the best. */
    int fails = 0;
    int idx = bestIdx < 0 ? 0 : bestIdx + 1;
    while (idx < nc && now() < t_end && fails < 3) {
        if (cand[idx].total <= bestTotal) { idx++; continue; }
        double rem = t_end - now();
        if (rem <= 0) break;
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (try_cand(idx, now() + slice)) fails = 0;
        else fails++;
        idx++;
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        free(cand);
        return 0;
    }
    print_result(&cand[bestIdx]);
    free(cand);
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Multi-orbit voltage lifts. Total vertex count must lie in [lo, hi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 4)
        hi = min(mb, 2 * lo)
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
