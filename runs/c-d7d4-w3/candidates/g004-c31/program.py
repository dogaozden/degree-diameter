import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving growth with annealing on the bad-pair count.
#
# State: a bipartite graph (left = col 0, right = col 1) with max degree d.
# Moves: edge switches (a-b, c-e -> a-e, c-b), which keep all degrees, and
# insertion of a new left/right pair built by taking d disjoint edges
# (x_i, y_i) and replacing them with (a, y_i), (x_i, b). Saturation adds edges
# between deficient vertices. Cost = number of vertex pairs at distance > D.
# The best zero-cost graph seen is printed at the end, so the output is always
# valid (or "0 0", which the Python side treats as no result).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXD 64
#define MAXE 300000

static int d, D;
static int n, m;
static int col[MAXN];
static int deg[MAXN];
static int adjv[MAXN][MAXD];
static int eu[MAXE], ev[MAXE];
static int ru[MAXE], rv[MAXE];
static int bu[MAXE], bv[MAXE];
static int bn, bm, have_best;
static int perm[MAXE];
static int mark[MAXN];
static int stampc;
static long cur_cost;
static clock_t deadline_clk;
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int irand(int k) {
    return (int)(rnd() % (uint64_t)k);
}

static void shuffle_int(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = irand(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int t = 0; t < deg[u]; t++)
        if (adjv[u][t] == v) return 1;
    return 0;
}

static void adj_add(int u, int v) {
    adjv[u][deg[u]++] = v;
}

static void adj_del(int u, int v) {
    for (int t = 0; t < deg[u]; t++) {
        if (adjv[u][t] == v) {
            adjv[u][t] = adjv[u][--deg[u]];
            return;
        }
    }
}

static void add_edge(int a, int b) {
    eu[m] = a;
    ev[m] = b;
    m++;
    adj_add(a, b);
    adj_add(b, a);
}

static void rebuild(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        adj_add(eu[i], ev[i]);
        adj_add(ev[i], eu[i]);
    }
}

/* Number of ordered-pair-free bad pairs (distance > D, unreachable included). */
static long eval_cost(void) {
    int w = (n + 63) >> 6;
    uint64_t (*cu)[MAXW] = bufA;
    uint64_t (*nx)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) cu[v][k] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int k = 0; k < w; k++) nx[v][k] = cu[v][k];
            for (int t = 0; t < deg[v]; t++) {
                int u = adjv[v][t];
                for (int k = 0; k < w; k++) nx[v][k] |= cu[u][k];
            }
        }
        uint64_t (*tmp)[MAXW] = cu;
        cu = nx;
        nx = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(cu[v][k]);
        bad += n - c;
    }
    return bad / 2;
}

static void saturate(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        if (deg[a] >= d) continue;
        for (int j = 0; j < nr; j++) {
            int b = R[j];
            if (deg[b] >= d) continue;
            if (has_edge(a, b)) continue;
            if (m >= MAXE) return;
            add_edge(a, b);
        }
    }
}

static int insert_pair(void) {
    if (n + 2 > MAXN || m + d + 2 > MAXE || m < d) return 0;
    for (int i = 0; i < m; i++) perm[i] = i;
    shuffle_int(perm, m);
    stampc++;
    int picked[MAXD];
    int np = 0;
    for (int t = 0; t < m && np < d; t++) {
        int idx = perm[t];
        int x = eu[idx], y = ev[idx];
        if (mark[x] == stampc || mark[y] == stampc) continue;
        mark[x] = stampc;
        mark[y] = stampc;
        picked[np++] = idx;
    }
    if (np < d) return 0;
    int a = n++;
    int b = n++;
    col[a] = 0;
    col[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    for (int k = 0; k < d; k++) {
        int idx = picked[k];
        int x = eu[idx], y = ev[idx];
        adj_del(x, y);
        adj_del(y, x);
        eu[idx] = a;
        ev[idx] = y;
        adj_add(a, y);
        adj_add(y, a);
        add_edge(x, b);
    }
    return 1;
}

/* Degree-preserving switch. Returns 1 if the move was kept. */
static int try_switch(double T, int force) {
    if (m < 2) return 0;
    int i = irand(m), j = irand(m);
    if (i == j) return 0;
    int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    adj_del(a, b);
    adj_del(b, a);
    adj_del(c, e);
    adj_del(e, c);
    adj_add(a, e);
    adj_add(e, a);
    adj_add(c, b);
    adj_add(b, c);
    ev[i] = e;
    ev[j] = b;
    long nc = eval_cost();
    long delta = nc - cur_cost;
    int acc = force || delta <= 0 || (T > 0 && urand() < exp(-(double)delta / T));
    if (acc) {
        cur_cost = nc;
        return 1;
    }
    adj_del(a, e);
    adj_del(e, a);
    adj_del(c, b);
    adj_del(b, c);
    adj_add(a, b);
    adj_add(b, a);
    adj_add(c, e);
    adj_add(e, c);
    ev[i] = b;
    ev[j] = e;
    return 0;
}

static long grow_iters(void) {
    return 2000L + 20L * (long)n;
}

static int anneal(long iters, double T0) {
    for (long it = 0; it < iters; it++) {
        if (cur_cost == 0) return 1;
        if ((it & 31) == 0 && clock() >= deadline_clk) return 0;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.03;
        try_switch(T, 0);
    }
    return cur_cost == 0;
}

static void save_best(void) {
    bn = n;
    bm = m;
    memcpy(bu, eu, sizeof(int) * (size_t)m);
    memcpy(bv, ev, sizeof(int) * (size_t)m);
    have_best = 1;
}

static void restore_best(void) {
    n = bn;
    m = bm;
    memcpy(eu, bu, sizeof(int) * (size_t)m);
    memcpy(ev, bv, sizeof(int) * (size_t)m);
    rebuild();
    cur_cost = eval_cost();
}

static int color_graph(int nn, int mm, const int *a, const int *b, int *c) {
    for (int v = 0; v < nn; v++) c[v] = -1;
    for (int s = 0; s < nn; s++) {
        if (c[s] >= 0) continue;
        c[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int i = 0; i < mm; i++) {
                int u = a[i], v = b[i];
                if (c[u] >= 0 && c[v] < 0) {
                    c[v] = 1 - c[u];
                    changed = 1;
                } else if (c[v] >= 0 && c[u] < 0) {
                    c[u] = 1 - c[v];
                    changed = 1;
                }
            }
        }
    }
    for (int i = 0; i < mm; i++)
        if (c[a[i]] == c[b[i]]) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed seconds\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double budget = atof(argv[4]);
    deadline_clk = clock() + (clock_t)(budget * CLOCKS_PER_SEC);
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int rn = 0, rm = 0;
    if (scanf("%d %d", &rn, &rm) != 2) {
        rn = 0;
        rm = 0;
    }
    if (rn < 0 || rm < 0 || rn > MAXN - 2 || rm > MAXE - 2 * MAXD) {
        printf("0 0\n");
        return 0;
    }
    if (rn == 0) {
        n = 2 * d;
        m = 0;
        for (int i = 0; i < n; i++) col[i] = (i < d) ? 0 : 1;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) {
                eu[m] = i;
                ev[m] = d + j;
                m++;
            }
    } else {
        for (int i = 0; i < rm; i++) {
            if (scanf("%d %d", &ru[i], &rv[i]) != 2) {
                printf("0 0\n");
                return 0;
            }
            if (ru[i] < 0 || ru[i] >= rn || rv[i] < 0 || rv[i] >= rn || ru[i] == rv[i]) {
                printf("0 0\n");
                return 0;
            }
        }
        if (!color_graph(rn, rm, ru, rv, col)) {
            printf("0 0\n");
            return 0;
        }
        n = rn;
        m = 0;
        for (int i = 0; i < rm; i++) {
            int u = ru[i], v = rv[i];
            if (col[u] == 0) {
                eu[m] = u;
                ev[m] = v;
            } else {
                eu[m] = v;
                ev[m] = u;
            }
            m++;
        }
    }

    rebuild();
    saturate();
    cur_cost = eval_cost();
    if (cur_cost == 0) save_best();

    int fails = 0;
    while (clock() < deadline_clk) {
        if (!have_best) {
            anneal(grow_iters(), 0.8);
            if (cur_cost == 0) save_best();
            continue;
        }
        restore_best();
        if (!insert_pair()) break;
        saturate();
        cur_cost = eval_cost();
        if (fails % 5 == 4) {
            for (int k = 0; k < 40; k++) try_switch(0.0, 1);
        }
        if (anneal(grow_iters(), 0.8)) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }

    if (have_best) {
        printf("%d %d\n", bn, bm);
        for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (structured starting points).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) with q the largest prime power <= min(d-1, 7)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _candidates(d, D):
    out = []
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
    if D >= 4:
        g = _best_gq(d)
        if g is not None:
            out.append(g)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = 2, [(0, 1)]

    for n, e in _candidates(d, D):
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Hand the best structured graph to the C annealing engine.
    remaining = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if remaining >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                             stdin_graph=(best_n, best_e), timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(text)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, list(e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
