import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley search over Z_m x| Z_k2 with exact cost and tabu search.
#
# Changes from the previous annealer:
#  * Cost is exact. For a bi-Cayley graph, left multiplication by the group is an
#    automorphism, so distances from the 2k block representatives (b, identity)
#    determine all distances. One BFS per representative gives the number of
#    unreached vertices, and zero means the graph is valid.
#  * Search is tabu search. Each step samples several candidate moves (voltage
#    changes at defect-targeted darts, or swaps inside a layer), applies the best
#    non-tabu one, and keeps the best graph seen.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define PENALTY 1000L
#define NCAND 40
#define TABU_BASE 6

static clock_t g_t0;
static double g_budget = 1.0;
static uint64_t g_rs = 88172645463325252ULL;

/* group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e); identity is index 0 */
static int GM = 1, GK = 1, GG = 1;
static int64_t PW[64];

static long g_best_n = 0;
static long g_best_m = 0;
static int *g_edges = NULL;

/* evaluation state */
static int G_D = 1, G_K = 1, G_N = 1, G_DEG = 1;
static int **G_NBR = NULL;
static int *G_DIST = NULL, *G_Q = NULL;
static long G_BAD[8];

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    uint64_t x = g_rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    g_rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int64_t t = (a + PW[b] * (int64_t)c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int64_t t = (-(PW[nb] * (int64_t)a)) % GM;
    if (t < 0) t += GM;
    return (int)(t * GK + nb);
}

static void set_group(int m, int k2, int64_t r) {
    GM = m;
    GK = k2;
    GG = m * k2;
    int64_t p = 1 % m;
    for (int t = 0; t < k2; t++) {
        PW[t] = p;
        p = (p * r) % m;
    }
}

static const int KCH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int sample_group(long target, int *mo, int *ko, int64_t *ro) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = KCH[rnd(20)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = 1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndf() < 0.3) {
            r = m - 1;
            if (gcd64(r, m) != 1 || powmod(r, 2, m) != 1 % m) continue;
        } else {
            int found = 0;
            for (int t = 0; t < 60; t++) {
                int64_t c = (m > 2) ? 2 + (int64_t)rnd((uint64_t)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) continue;
        }
        *mo = (int)m;
        *ko = k2;
        *ro = r;
        return 1;
    }
    return 0;
}

/* A-block i joins B-block j = lay[l*k+i] with voltage s = S[l*k+i]. */
static void set_dart(int **nbr, const int *lay, const int *S, int k, int l, int i) {
    int j = lay[l * k + i];
    int s = S[l * k + i];
    int si = ginv(s);
    int Ab = i * GG, Bb = (k + j) * GG;
    int *nb = nbr[l];
    for (int g = 0; g < GG; g++) {
        nb[Ab + g] = Bb + gmul(g, s);
        nb[Bb + g] = Ab + gmul(g, si);
    }
}

/* Exact unreached count from the 2k representatives (b, identity). */
static long eval_cost(void) {
    long total = 0;
    int N = G_N;
    for (int b = 0; b < 2 * G_K; b++) {
        int src = b * GG;
        for (int v = 0; v < N; v++) G_DIST[v] = -1;
        int head = 0, tail = 0;
        G_Q[tail++] = src;
        G_DIST[src] = 0;
        while (head < tail) {
            int v = G_Q[head++];
            if (G_DIST[v] >= G_D) continue;
            for (int l = 0; l < G_DEG; l++) {
                int u = G_NBR[l][v];
                if (G_DIST[u] < 0) {
                    G_DIST[u] = G_DIST[v] + 1;
                    G_Q[tail++] = u;
                }
            }
        }
        G_BAD[b] = (long)N - tail;
        total += G_BAD[b];
    }
    return total;
}

static long dupcount(const int *lay, const int *S, int d, int k) {
    int tot = d * k;
    long dup = 0;
    for (int a = 0; a < tot; a++) {
        int la = a / k, ia = a % k;
        for (int b = 0; b < a; b++) {
            int lb = b / k, ib = b % k;
            if (ia == ib && lay[la * k + ia] == lay[lb * k + ib] && S[la * k + ia] == S[lb * k + ib]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static long full_cost(const int *lay, const int *S, int d, int k) {
    return eval_cost() + PENALTY * dupcount(lay, S, d, k);
}

static void store_best(int **nbr, int d, int k) {
    long A = (long)k * GG;
    long n = 2 * A;
    if (n <= g_best_n) return;
    long cnt = A * d;
    int *e = malloc(sizeof(int) * 2 * (size_t)cnt);
    if (!e) return;
    long c = 0;
    for (long u = 0; u < A; u++) {
        for (int l = 0; l < d; l++) {
            e[2 * c] = (int)u;
            e[2 * c + 1] = nbr[l][u];
            c++;
        }
    }
    free(g_edges);
    g_edges = e;
    g_best_m = cnt;
    g_best_n = n;
}

/* Choose a dart, preferring blocks whose representative has unreached vertices. */
static void pick_dart(const int *lay, int d, int k, const long *bad, int *lo, int *io) {
    long tot = 0;
    for (int b = 0; b < 2 * k; b++) tot += bad[b];
    int l = 0, i = 0;
    if (tot > 0 && rndf() < 0.6) {
        long pick = (long)rnd((uint64_t)tot);
        int b = 0;
        while (b < 2 * k - 1 && pick >= bad[b]) {
            pick -= bad[b];
            b++;
        }
        l = (int)rnd((uint64_t)d);
        if (b < k) {
            i = b;
        } else {
            i = -1;
            for (int q = 0; q < k; q++) {
                if (lay[l * k + q] == b - k) {
                    i = q;
                    break;
                }
            }
            if (i < 0) i = (int)rnd((uint64_t)k);
        }
    } else {
        l = (int)rnd((uint64_t)d);
        i = (int)rnd((uint64_t)k);
    }
    *lo = l;
    *io = i;
}

static int run_trial(int d, int D, int k, long max_iters, long patience) {
    int N = 2 * k * GG;
    int K = d * k;
    int *lay = malloc(sizeof(int) * (size_t)K);
    int *S = malloc(sizeof(int) * (size_t)K);
    int **nbr = malloc(sizeof(int *) * (size_t)d);
    long *tabu = calloc((size_t)K, sizeof(long));
    int *dist = malloc(sizeof(int) * (size_t)N);
    int *queue = malloc(sizeof(int) * (size_t)N);
    for (int l = 0; l < d; l++) nbr[l] = malloc(sizeof(int) * (size_t)N);
    G_D = D;
    G_K = k;
    G_N = N;
    G_DEG = d;
    G_NBR = nbr;
    G_DIST = dist;
    G_Q = queue;

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = (int)rnd((uint64_t)(i + 1));
            int t = lay[l * k + i];
            lay[l * k + i] = lay[l * k + j];
            lay[l * k + j] = t;
        }
    }
    for (int q = 0; q < K; q++) S[q] = (int)rnd((uint64_t)GG);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(nbr, lay, S, k, l, i);

    long cost = full_cost(lay, S, d, k);
    long best_cost = cost;
    long bad0[8];
    int ok = 0;
    if (cost == 0) {
        store_best(nbr, d, k);
        ok = 1;
    }
    long last = 0;

    for (long it = 0; !ok && it < max_iters; it++) {
        if (elapsed() > g_budget) break;
        if (it - last > patience) break;
        for (int b = 0; b < 2 * k; b++) bad0[b] = G_BAD[b];

        long bc = -1;
        int bt = 0, bl = 0, bi1 = 0, bi2 = 0, bs = 0;
        for (int c = 0; c < NCAND; c++) {
            if (k >= 2 && rndf() < 0.2) {
                /* swap two entries of one layer */
                int l = (int)rnd((uint64_t)d);
                int i1 = (int)rnd((uint64_t)k);
                int i2 = (int)rnd((uint64_t)(k - 1));
                if (i2 >= i1) i2++;
                int tv = lay[l * k + i1];
                lay[l * k + i1] = lay[l * k + i2];
                lay[l * k + i2] = tv;
                set_dart(nbr, lay, S, k, l, i1);
                set_dart(nbr, lay, S, k, l, i2);
                long c2 = full_cost(lay, S, d, k);
                tv = lay[l * k + i1];
                lay[l * k + i1] = lay[l * k + i2];
                lay[l * k + i2] = tv;
                set_dart(nbr, lay, S, k, l, i1);
                set_dart(nbr, lay, S, k, l, i2);
                int tabu_hit = (tabu[l * k + i1] > it) || (tabu[l * k + i2] > it);
                if (tabu_hit && c2 >= best_cost) continue;
                if (bc < 0 || c2 < bc || (c2 == bc && rnd(2) == 0)) {
                    bc = c2;
                    bt = 1;
                    bl = l;
                    bi1 = i1;
                    bi2 = i2;
                }
            } else {
                /* voltage change */
                int l, i;
                pick_dart(lay, d, k, bad0, &l, &i);
                int idx = l * k + i;
                int s = (int)rnd((uint64_t)GG);
                if (s == S[idx]) continue;
                int old = S[idx];
                S[idx] = s;
                set_dart(nbr, lay, S, k, l, i);
                long c2 = full_cost(lay, S, d, k);
                S[idx] = old;
                set_dart(nbr, lay, S, k, l, i);
                if (tabu[idx] > it && c2 >= best_cost) continue;
                if (bc < 0 || c2 < bc || (c2 == bc && rnd(2) == 0)) {
                    bc = c2;
                    bt = 0;
                    bl = l;
                    bi1 = i;
                    bs = s;
                }
            }
        }
        if (bc < 0) continue;

        long tt = TABU_BASE + (long)rnd((uint64_t)(TABU_BASE + 1));
        if (bt == 0) {
            int idx = bl * k + bi1;
            S[idx] = bs;
            set_dart(nbr, lay, S, k, bl, bi1);
            tabu[idx] = it + tt;
        } else {
            int tv = lay[bl * k + bi1];
            lay[bl * k + bi1] = lay[bl * k + bi2];
            lay[bl * k + bi2] = tv;
            set_dart(nbr, lay, S, k, bl, bi1);
            set_dart(nbr, lay, S, k, bl, bi2);
            tabu[bl * k + bi1] = it + tt;
            tabu[bl * k + bi2] = it + tt;
        }
        cost = full_cost(lay, S, d, k);
        if (cost < best_cost) {
            best_cost = cost;
            last = it;
        }
        if (cost == 0) {
            store_best(nbr, d, k);
            ok = 1;
        }
    }

    for (int l = 0; l < d; l++) free(nbr[l]);
    free(nbr);
    free(lay);
    free(S);
    free(tabu);
    free(dist);
    free(queue);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D seed budget min_n\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    g_rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (g_rs == 0) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    g_best_n = atol(argv[5]);
    g_t0 = clock();

    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    long trials[5] = {0, 0, 0, 0, 0};
    long wins[5] = {0, 0, 0, 0, 0};

    while (elapsed() < g_budget) {
        int k;
        if (rndf() < 0.2) {
            k = 1 + (int)rnd(4);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= 4; kk++) {
                double v = ((double)wins[kk] + 1.0) / ((double)trials[kk] + 2.0) + 0.02 * rndf();
                if (v > bv) {
                    bv = v;
                    k = kk;
                }
            }
        }
        long base = g_best_n / (2L * k);
        long span = base / 6 + 2;
        long target = base + 1 + (long)rnd((uint64_t)span);
        if (target < 2) target = 2;

        int m = 0, k2 = 1;
        int64_t r = 1;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        if (2L * k * GG <= g_best_n) continue;

        trials[k]++;
        if (run_trial(d, D, k, 3000, 500)) wins[k]++;
    }

    if (g_best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", g_best_n, g_best_m);
    for (long c = 0; c < g_best_m; c++) {
        printf("%d %d\n", g_edges[2 * c], g_edges[2 * c + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, budget, min_n, timeout):
    """Run the C engine; returns (n, edges), or (0, []) if it found nothing better than min_n."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n], timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

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
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except Exception:
                pass
        if D == 3 and pg is not None and lib.is_prime_power(d - 1):
            return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: tabu search over bi-Cayley voltages in C.
    c_budget = deadline - time.monotonic()
    if c_budget > 0.5:
        timeout = max(1.0, min(c_budget + 3.0, time_limit - (time.monotonic() - start) - 1.5))
        try:
            n, e = _c_search(d, D, seed, c_budget, best_n, timeout)
            consider(n, e)
        except Exception:
            pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
