import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Program: bi-Cayley voltage search with EXACT cost, over semidirect products
# Z_M x| Z_K2 (including abelian Z_M x Z_K2 when r = 1), base sizes K = 1..6.
#
# Changes from the parent:
#  * Exact cost. The parent's bitmask proxy only checked distances from one
#    vertex per block, which is not enough for a group lift. Here, by left
#    translation, every pair (v, w) is at distance <= D iff, for each of the
#    2K block representatives r_b, all vertices lie within D of r_b. So the
#    cost is an exact count of bad (representative, vertex) pairs from 2K BFS
#    runs. Cost 0 means a valid simple bipartite graph of diameter <= D.
#  * Base size up to K = 6, and a wider group family (abelian products too).
#  * Iterated local search from the best near miss, with voltage kicks.
#  * Python keeps exact constructions (PG(2,q), W(q)) and a K_{d,d} fallback,
#    and every returned graph passes lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 6
#define NCH 12
#define PEN 40
#define MAXCAP 1000000

static const int K2_CHOICES[NCH] = {1, 2, 2, 3, 4, 4, 5, 6, 6, 8, 10, 12};

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int DEG, DIAM, CAP;
static int K, K2, M, R, G, N;
static int64_t PWR[64];
static int *AA, *BB;
static int *adj;                 /* adj[v*DEG + l] */
static int *lay, *vol, *nr_lay, *nr_vol;
static int *best_adj;
static int *vis, *dep, *que;
static int stamp_now;
static int timed_out;
static double TL, tstart;
static int have_best, best_N;
static int have_near, nr_K, nr_M, nr_K2, nr_R, nr_N;
static int64_t nr_cost, LASTCOST;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
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

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Group: elements (a,b) coded a*K2+b; (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_group(void) {
    G = M * K2;
    N = 2 * K * G;
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* Dart (left base i) -- (right base p) with voltage s:
   (i,g) ~ (K+p, g*s) for all g. Both directions are written. */
static void set_dart(int l, int i, int p, int s) {
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int y = gmul(g, s);
        adj[(size_t)(Ab + g) * DEG + l] = Bb + y;
        adj[(size_t)(Bb + y) * DEG + l] = Ab + g;
    }
}

static void rebuild_all(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i, lay[l * K + i], vol[l * K + i]);
}

/* Exact count of (representative, vertex) pairs at distance > DIAM. */
static int64_t eval_cost(void) {
    int64_t bad = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        stamp_now++;
        int head = 0, tail = 0;
        vis[src] = stamp_now;
        dep[src] = 0;
        que[tail++] = src;
        while (head < tail) {
            int v = que[head++];
            if (dep[v] >= DIAM) continue;
            const int *row = adj + (size_t)v * DEG;
            for (int l = 0; l < DEG; l++) {
                int w = row[l];
                if (vis[w] != stamp_now) {
                    vis[w] = stamp_now;
                    dep[w] = dep[v] + 1;
                    que[tail++] = w;
                }
            }
        }
        bad += N - tail;
    }
    return bad;
}

static int dupcount(void) {
    int dup = 0;
    int n = DEG * K;
    for (int e = 0; e < n; e++) {
        int i = e % K;
        for (int f = i; f < e; f += K) {
            if (lay[f] == lay[e] && vol[f] == vol[e]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static int64_t total_cost(void) {
    return eval_cost() + (int64_t)PEN * dupcount();
}

static int accept_move(int64_t c2, int64_t cost, double temp) {
    if (c2 <= cost) return 1;
    return rnd01() < exp(-(double)(c2 - cost) / temp);
}

static int run_trial(int iters, int patience, int reinit) {
    timed_out = 0;
    if (reinit) {
        for (int l = 0; l < DEG; l++) {
            int perm[MAXK];
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
        }
        for (int e = 0; e < DEG * K; e++) vol[e] = rndint(G);
    }
    rebuild_all();
    int64_t cost = total_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    int64_t best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 15) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double frac = (double)t / (double)iters;
        double temp = 0.03 * c0 * (1.0 - frac) + 0.3;
        double mv = rnd01();
        int64_t c2 = 0;

        if (K >= 2 && mv < 0.20) {
            /* swap two permutation entries in one layer */
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tp = lay[e1];
            lay[e1] = lay[e2];
            lay[e2] = tp;
            set_dart(l, i1, lay[e1], vol[e1]);
            set_dart(l, i2, lay[e2], vol[e2]);
            c2 = total_cost();
            if (accept_move(c2, cost, temp)) {
                cost = c2;
                if (cost < best_cost) {
                    best_cost = cost;
                    last = t;
                }
            } else {
                tp = lay[e1];
                lay[e1] = lay[e2];
                lay[e2] = tp;
                set_dart(l, i1, lay[e1], vol[e1]);
                set_dart(l, i2, lay[e2], vol[e2]);
            }
        } else if (DEG >= 2 && mv < 0.35) {
            /* exchange voltages of base vertex i between two layers */
            int l1 = rndint(DEG);
            int l2 = rndint(DEG - 1);
            if (l2 >= l1) l2++;
            int i = rndint(K);
            int e1 = l1 * K + i, e2 = l2 * K + i;
            int v1 = vol[e1], v2 = vol[e2];
            if (v1 == v2) continue;
            vol[e1] = v2;
            vol[e2] = v1;
            set_dart(l1, i, lay[e1], vol[e1]);
            set_dart(l2, i, lay[e2], vol[e2]);
            c2 = total_cost();
            if (accept_move(c2, cost, temp)) {
                cost = c2;
                if (cost < best_cost) {
                    best_cost = cost;
                    last = t;
                }
            } else {
                vol[e1] = v1;
                vol[e2] = v2;
                set_dart(l1, i, lay[e1], v1);
                set_dart(l2, i, lay[e2], v2);
            }
        } else {
            /* change one voltage */
            int l = rndint(DEG);
            int i = rndint(K);
            int e = l * K + i;
            int old = vol[e];
            int nw = rndint(G);
            if (nw == old) continue;
            vol[e] = nw;
            set_dart(l, i, lay[e], nw);
            c2 = total_cost();
            if (accept_move(c2, cost, temp)) {
                cost = c2;
                if (cost < best_cost) {
                    best_cost = cost;
                    last = t;
                }
            } else {
                vol[e] = old;
                set_dart(l, i, lay[e], old);
            }
        }
    }
    LASTCOST = cost;
    return cost == 0;
}

static void save_near(void) {
    have_near = 1;
    nr_K = K;
    nr_M = M;
    nr_K2 = K2;
    nr_R = R;
    nr_N = N;
    nr_cost = LASTCOST;
    memcpy(nr_lay, lay, sizeof(int) * (size_t)DEG * MAXK);
    memcpy(nr_vol, vol, sizeof(int) * (size_t)DEG * MAXK);
}

/* Sample a group with base size k and 2*k*M*K2 slightly above minN. */
static int sample_group(int k, long long minN) {
    for (int att = 0; att < 300; att++) {
        int k2 = K2_CHOICES[rndint(NCH)];
        long long per = 2LL * k * k2;
        long long want = minN + 1 + rndint((int)(minN / 12 + 2));
        long long m = (want + per - 1) / per + rndint(2);
        if (m < 2) m = 2;
        long long Nn = per * m;
        if (Nn <= minN || Nn > CAP) continue;
        int64_t r = 1;
        if (k2 >= 2 && m >= 3 && rnd01() < 0.65) {
            int ok = 0;
            for (int tries = 0; tries < 80 && !ok; tries++) {
                int64_t c = 2 + rndint((int)(m - 2));
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    ok = 1;
                }
            }
            if (!ok) r = 1;
        }
        K = k;
        K2 = k2;
        M = (int)m;
        R = (int)r;
        setup_group();
        return 1;
    }
    return 0;
}

static int pick_k(const double *tr, const double *wn) {
    if (rnd01() < 0.25) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wn[k] + 1.0) / (tr[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D best cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    long long capl = atoll(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    if (DEG < 3 || DEG > 64 || DIAM < 3 || capl < 8) {
        printf("0 0\n");
        return 0;
    }
    if (capl > MAXCAP) capl = MAXCAP;
    CAP = (int)capl;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    AA = malloc(sizeof(int) * (size_t)(CAP + 1));
    BB = malloc(sizeof(int) * (size_t)(CAP + 1));
    adj = malloc(sizeof(int) * (size_t)DEG * (CAP + 1));
    best_adj = malloc(sizeof(int) * (size_t)DEG * (CAP + 1));
    vis = calloc((size_t)(CAP + 1), sizeof(int));
    dep = malloc(sizeof(int) * (size_t)(CAP + 1));
    que = malloc(sizeof(int) * (size_t)(CAP + 1));
    lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    nr_lay = malloc(sizeof(int) * (size_t)DEG * MAXK);
    nr_vol = malloc(sizeof(int) * (size_t)DEG * MAXK);
    if (!AA || !BB || !adj || !best_adj || !vis || !dep || !que ||
        !lay || !vol || !nr_lay || !nr_vol) {
        printf("0 0\n");
        return 0;
    }

    double tr[MAXK + 1], wn[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) {
        tr[k] = 0.0;
        wn[k] = 0.0;
    }
    long long found = best0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = 1;
        int ok = 0;

        if (have_near && nr_N > found && rnd01() < 0.5) {
            /* iterated local search: kick the saved near miss and re-anneal */
            k = nr_K;
            K = nr_K;
            K2 = nr_K2;
            M = nr_M;
            R = nr_R;
            setup_group();
            memcpy(lay, nr_lay, sizeof(int) * (size_t)DEG * MAXK);
            memcpy(vol, nr_vol, sizeof(int) * (size_t)DEG * MAXK);
            int kicks = 2 + rndint(4);
            for (int q = 0; q < kicks; q++) {
                int l = rndint(DEG), i = rndint(K);
                vol[l * K + i] = rndint(G);
            }
            ok = run_trial(4000, 1500, 0);
        } else {
            k = pick_k(tr, wn);
            if (!sample_group(k, found)) continue;
            tr[k] += 1.0;
            ok = run_trial(6000, 2000, 1);
        }

        int extra = 0;
        while (!ok && !timed_out && extra < 3 &&
               LASTCOST <= (int64_t)N / 20 + 4 && elapsed() < TL) {
            ok = run_trial(6000, 2000, 0);
            extra++;
        }

        if (!ok && !timed_out && LASTCOST > 0) {
            if (!have_near || LASTCOST < nr_cost) save_near();
        }

        if (ok) {
            wn[k] += 1.0;
            found = N;
            memcpy(best_adj, adj, sizeof(int) * (size_t)DEG * N);
            best_N = N;
            have_best = 1;
            have_near = 0;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int half = best_N / 2;   /* left vertices 0..half-1 carry all edges */
    printf("%d %d\n", best_N, half * DEG);
    for (int u = 0; u < half; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, best_adj[(size_t)u * DEG + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as the start graph.
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
# Main build: exact constructions, then the exact-cost C search, then slack.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search, entirely in C.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), 1_000_000)
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 20.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
