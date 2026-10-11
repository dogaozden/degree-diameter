import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (from both parents).
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
# Pair insertion by edge cutting (from parent g016).
#
# Pick k = d-1 edges x_i y_i (x_i side 0, y_i side 1, all distinct). Delete
# them, add a (side 0) joined to every y_i, b (side 1) joined to every x_i,
# and a-b. Degrees stay <= d, bipartite is kept, order grows by 2. Each trial
# is checked with lib.within_diameter; rejected trials change nothing.
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    """Return a 0/1 side label for every vertex (a proper 2-colouring of a bipartite graph)."""
    adj = lib.adjacency(n, edges)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _pair_extend(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex pair by edge cutting while the diameter stays <= D."""
    k = d - 1
    edges = [(int(u), int(v)) for u, v in edges]
    if k < 1 or len(edges) < k:
        return n, edges
    col = _two_colour(n, edges)
    while time.monotonic() < deadline:
        picked = []
        used_x, used_y, chosen = set(), set(), set()
        for _ in range(64 * k):
            if len(picked) == k:
                break
            i = rng.randrange(len(edges))
            if i in chosen:
                continue
            u, v = edges[i]
            x, y = (u, v) if col[u] == 0 else (v, u)
            if x in used_x or y in used_y:
                continue
            chosen.add(i)
            picked.append((i, x, y))
            used_x.add(x)
            used_y.add(y)
        if len(picked) < k:
            continue
        a, b = n, n + 1
        new = [e for i, e in enumerate(edges) if i not in chosen]
        for _, x, y in picked:
            new.append((a, y))
            new.append((b, x))
        new.append((a, b))
        if lib.within_diameter(n + 2, new, D):
            edges = new
            col.append(0)
            col.append(1)
            n += 2
    return n, edges


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over Z_m x|_r Z_k2, searched by breakout local
# search (weighted pairs, from parent g016) with reheating from the best
# state of the current group (from parent g002) and a unit-weight polish.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart e = l*K+i joins
# A_{i,g} to B_{dJ[e], g*dS[e]}. Each layer l is a permutation dJ on the K
# indices, so every vertex has degree DEG. Left multiplication is an
# automorphism, so BFS from the 2K representatives decides the diameter.
# Cost = weighted unreached (rep, vertex) pairs + PEN * duplicate darts.
#
# Usage: prog d D seed time_limit min_n
# Prints the largest valid graph found ("n m" + edges), or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define PEN 1000
#define BREAK_ITERS 20000
#define STUCK 60
#define POLISH_T 80
#define GROUP_RESTARTS 3
#define MAXG 12000
#define MAXK 2
#define MAXDEG 64
#define MAXNE (MAXDEG * MAXK)
#define MAXN (2 * MAXK * MAXG)
#define MAXPOW 64

static int DEG = 3, DIAM = 3;
static int K = 1, MM = 1, K2 = 1, RR = 1, G = 1, N = 2, NE = 3;
static int POWR[MAXPOW];

static int dI[MAXNE], dJ[MAXNE], dS[MAXNE];
static int gJ[MAXNE], gS[MAXNE], pJ[MAXNE], pS[MAXNE];
static int oJ[MAXNE], oS[MAXNE];
static int *perm = NULL, *adj = NULL, *cnt = NULL, *fr = NULL, *nx = NULL;
static uint32_t *vis = NULL;
static long long *wt = NULL;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;
static int g_raw = 0;
static int found_flag = 0;
static int have = 0;
static int lowN = 0;
static int oK = 1, oM = 1, oK2 = 1, oR = 1;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void set_group(int m, int k2, int r) {
    MM = m;
    K2 = k2;
    G = m * k2;
    RR = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        POWR[b] = (int)p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, d = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * (long long)c) % MM;
    return (int)(t * K2 + (b + d) % K2);
}

static void set_perm_e(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

/* Returns weighted cost (weights of unreached pairs + PEN * duplicates).
   Sets g_raw to the unweighted cost. If bump is set, the weight of every
   currently unreached pair is increased by one. */
static long long evalc(int bump) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    long long ws = 0;
    long raw = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        int *cur = fr, *nxt = nx;
        int fn = 1;
        cur[0] = src;
        vis[src] = stamp;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                const int *au = adj + (size_t)cur[q] * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            int *tmp = cur;
            cur = nxt;
            nxt = tmp;
            fn = nn;
        }
        long long *w = wt + (size_t)ri * N;
        for (int v = 0; v < N; v++) {
            if (vis[v] != stamp) {
                raw++;
                ws += w[v];
                if (bump) w[v]++;
            }
        }
    }
    g_raw = (int)(raw + (long)PEN * dup);
    return ws + (long long)PEN * dup;
}

static void record_valid(void) {
    found_flag = 1;
    have = 1;
    lowN = N;
    oK = K;
    oM = MM;
    oK2 = K2;
    oR = RR;
    memcpy(oJ, dJ, sizeof(int) * NE);
    memcpy(oS, dS, sizeof(int) * NE);
}

static void reset_wt(void) {
    size_t tot = (size_t)2 * K * N;
    for (size_t j = 0; j < tot; j++) wt[j] = 1;
}

static void init_random(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            dI[l * K + i] = i;
            dJ[l * K + i] = p[i];
        }
    }
    for (int e = 0; e < NE; e++) {
        dS[e] = rint_(G);
        set_perm_e(e);
    }
}

/* Breakout local search on the weighted cost. Stops early when a valid
   graph is found (record_valid sets found_flag). Ends in the run-best state. */
static void breakout(void) {
    long long wc = evalc(0);
    if (g_raw == 0) {
        record_valid();
        return;
    }
    int runbest = g_raw;
    memcpy(pJ, dJ, sizeof(int) * NE);
    memcpy(pS, dS, sizeof(int) * NE);
    int stuck = 0;
    for (int t = 0; t < BREAK_ITERS; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
        int acc = 0;
        long long wc2 = wc;
        if (K > 1 && rint_(3) == 0) {
            int l = rint_(DEG), i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tmp = dJ[e1];
            dJ[e1] = dJ[e2];
            dJ[e2] = tmp;
            wc2 = evalc(0);
            if (wc2 <= wc) {
                acc = 1;
            } else {
                tmp = dJ[e1];
                dJ[e1] = dJ[e2];
                dJ[e2] = tmp;
            }
        } else {
            int e = rint_(NE), ns = rint_(G), old = dS[e];
            if (ns == old) continue;
            dS[e] = ns;
            set_perm_e(e);
            wc2 = evalc(0);
            if (wc2 <= wc) {
                acc = 1;
            } else {
                dS[e] = old;
                set_perm_e(e);
            }
        }
        if (acc) {
            stuck = (wc2 < wc) ? 0 : stuck + 1;
            wc = wc2;
            if (g_raw == 0) {
                record_valid();
                return;
            }
            if (g_raw < runbest) {
                runbest = g_raw;
                memcpy(pJ, dJ, sizeof(int) * NE);
                memcpy(pS, dS, sizeof(int) * NE);
            }
        } else {
            stuck++;
        }
        if (stuck >= STUCK) {
            evalc(1);
            wc = evalc(0);
            stuck = 0;
        }
    }
    memcpy(dJ, pJ, sizeof(int) * NE);
    memcpy(dS, pS, sizeof(int) * NE);
    for (int e = 0; e < NE; e++) set_perm_e(e);
    evalc(0);
}

/* Best-improvement coordinate sweeps over dart voltages with unit weights. */
static void polish(void) {
    evalc(0);
    int cost = g_raw;
    int improved = 1;
    while (improved && cost > 0) {
        improved = 0;
        for (int e = 0; e < NE && cost > 0; e++) {
            if (now_s() > deadline) return;
            int old = dS[e], bestv = old, bestc = cost;
            for (int s = 0; s < G; s++) {
                if (s == old) continue;
                dS[e] = s;
                set_perm_e(e);
                evalc(0);
                if (g_raw < bestc) {
                    bestc = g_raw;
                    bestv = s;
                }
            }
            dS[e] = bestv;
            set_perm_e(e);
            if (bestv != old) {
                improved = 1;
                cost = bestc;
                if (cost == 0) {
                    record_valid();
                    return;
                }
            }
        }
    }
    evalc(0);
}

/* Restarts within one group; later restarts may reheat from the group's
   best state with a random kick. */
static void run_group(void) {
    long long gcost = 0;
    int have_g = 0;
    for (int rr = 0; rr < GROUP_RESTARTS; rr++) {
        if (now_s() >= deadline) return;
        if (have_g && rint_(2) == 0) {
            memcpy(dJ, gJ, sizeof(int) * NE);
            memcpy(dS, gS, sizeof(int) * NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rint_(NE)] = rint_(G);
            for (int e = 0; e < NE; e++) set_perm_e(e);
        } else {
            init_random();
        }
        reset_wt();
        breakout();
        if (found_flag) return;
        if (g_raw <= POLISH_T) {
            polish();
            if (found_flag) return;
        }
        if (!have_g || (long long)g_raw < gcost) {
            gcost = g_raw;
            have_g = 1;
            memcpy(gJ, dJ, sizeof(int) * NE);
            memcpy(gS, dS, sizeof(int) * NE);
        }
    }
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

/* Pick Z_m x|_r Z_k with m*k >= target and m*k <= MAXG. */
static int sample_group(long long target, int *oM_, int *oKk, int *oR_) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    if (m * k > MAXG) return 0;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM_ = (int)m;
    *oKk = k;
    *oR_ = r;
    return 1;
}

static void print_best(void) {
    if (!have) {
        printf("0 0\n");
        return;
    }
    int k = oK;
    set_group(oM, oK2, oR);
    int Gl = oM * oK2;
    int n = 2 * k * Gl;
    int ne = DEG * k;
    printf("%d %ld\n", n, (long)ne * Gl);
    for (int e = 0; e < ne; e++) {
        int i = e % k;
        int j = oJ[e], s = oS[e];
        for (int g = 0; g < Gl; g++) {
            printf("%d %d\n", i * Gl + g, (k + j) * Gl + gmul(g, s));
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd64();

    perm = malloc(sizeof(int) * (size_t)MAXNE * MAXG);
    adj = malloc(sizeof(int) * (size_t)MAXN * DEG);
    cnt = malloc(sizeof(int) * MAXN);
    fr = malloc(sizeof(int) * MAXN);
    nx = malloc(sizeof(int) * MAXN);
    vis = calloc(MAXN, sizeof(uint32_t));
    wt = malloc(sizeof(long long) * (size_t)2 * MAXK * MAXN);
    if (!perm || !adj || !cnt || !fr || !nx || !vis || !wt) {
        printf("0 0\n");
        return 0;
    }

    deadline = now_s() + tl;
    lowN = min_n;
    while (now_s() < deadline) {
        int Kc = (rint_(100) < 70) ? 1 : 2;
        long long g0 = (long long)lowN / (2 * Kc) + 1;
        long long span = g0 / 25 + 6;
        long long target = g0 + (long long)rint_((int)span);
        int M, Kk, R;
        if (!sample_group(target, &M, &Kk, &R)) continue;
        K = Kc;
        set_group(M, Kk, R);
        NE = DEG * K;
        N = 2 * K * G;
        if (N <= lowN || N > MAXN) continue;
        found_flag = 0;
        run_group();
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the C search, then pair insertion.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C search: breakout + reheating over bi-Cayley lifts, seeded with the
    # best known order as a lower bound. Pair insertion gets a reserved tail.
    if d >= 3 and D >= 3:
        pair_reserve = 0.12 * budget
        c_budget = deadline - time.monotonic() - pair_reserve - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best[0]],
                                timeout=c_budget + 20.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    # Grow the best valid graph by vertex pairs using edge cutting.
    if d >= 2 and D >= 2 and deadline - time.monotonic() > 0.5:
        try:
            n2, e2 = _pair_extend(best[0], best[1], d, D, deadline, random.Random(seed))
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
