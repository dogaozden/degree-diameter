import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXDEG 40
#define RESET_STEPS 30000L

typedef uint64_t Row[MAXW];

static int n = 0, dd = 3, DD = 3;
static int adjl[MAXN][MAXDEG];
static int deg[MAXN];
static int col[MAXN];
static Row BA[MAXN], BB[MAXN];
static int bn = -1;
static int badj[MAXN][MAXDEG];
static int bdeg[MAXN];
static int bcol[MAXN];
static int la[8][2], lr[8][2];
static int nla = 0, nlr = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int adjacent(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adjl[u][i] == v) return 1;
    return 0;
}
static void add_e(int u, int v) {
    adjl[u][deg[u]++] = v;
    adjl[v][deg[v]++] = u;
}
static void del_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adjl[u][i] == v) { adjl[u][i] = adjl[u][--deg[u]]; return; }
}
static void del_e(int u, int v) { del_one(u, v); del_one(v, u); }
static void log_add(int u, int v) { la[nla][0] = u; la[nla][1] = v; nla++; }
static void log_rem(int u, int v) { lr[nlr][0] = u; lr[nlr][1] = v; nlr++; }

static void undo(void) {
    for (int i = nla - 1; i >= 0; i--) del_e(la[i][0], la[i][1]);
    for (int i = nlr - 1; i >= 0; i--) add_e(lr[i][0], lr[i][1]);
}

/* Bitset balls of radius r around every vertex. */
static Row *balls(int r) {
    int W = (n + 63) >> 6;
    Row *src = BA, *dst = BB;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < W; k++) src[v][k] = 0;
        src[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int k = 0; k < W; k++) dst[v][k] = src[v][k];
            for (int i = 0; i < deg[v]; i++) {
                int u = adjl[v][i];
                for (int k = 0; k < W; k++) dst[v][k] |= src[u][k];
            }
        }
        Row *t = src; src = dst; dst = t;
    }
    return src;
}

/* Number of unordered pairs at distance > DD (unreachable counts). */
static long cost_now(void) {
    Row *b = balls(DD);
    int W = (n + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < W; k++) c += pc64(b[v][k]);
        bad += n - c;
    }
    return bad / 2;
}

/* Try to add one new vertex whose neighbourhood covers everything within DD-1. */
static int try_grow(void) {
    if (n >= MAXN - 1 || n < 2) return 0;
    int W = (n + 63) >> 6;
    Row full;
    for (int k = 0; k < MAXW; k++) full[k] = 0;
    for (int v = 0; v < n; v++) full[v >> 6] |= 1ULL << (v & 63);
    Row *b = balls(DD - 1);
    static int cand[MAXN];
    static char used[MAXN];
    for (int att = 0; att < 12; att++) {
        int c = rndi(2);
        int nc = 0;
        for (int v = 0; v < n; v++) if (col[v] == c && deg[v] < dd) cand[nc++] = v;
        if (nc == 0) continue;
        for (int i = 0; i < nc; i++) used[cand[i]] = 0;
        Row cov;
        for (int k = 0; k < W; k++) cov[k] = 0;
        int chosen[MAXDEG];
        int nch = 0;
        while (nch < dd) {
            int ok = 1;
            for (int k = 0; k < W; k++) if (cov[k] != full[k]) { ok = 0; break; }
            if (ok) break;
            int bi = -1, bestg = 0, ties = 0;
            if (att > 0 && rnd01() < 0.2) {
                int st = rndi(nc);
                for (int t = 0; t < nc; t++) {
                    int s = cand[(st + t) % nc];
                    if (used[s]) continue;
                    int g = 0;
                    for (int k = 0; k < W; k++) g += pc64(b[s][k] & ~cov[k]);
                    if (g > 0) { bi = s; break; }
                }
            } else {
                for (int i = 0; i < nc; i++) {
                    int s = cand[i];
                    if (used[s]) continue;
                    int g = 0;
                    for (int k = 0; k < W; k++) g += pc64(b[s][k] & ~cov[k]);
                    if (g > bestg) { bestg = g; bi = s; ties = 1; }
                    else if (g == bestg && g > 0 && att > 0) {
                        ties++;
                        if (rndi(ties) == 0) bi = s;
                    }
                }
            }
            if (bi < 0) break;
            used[bi] = 1;
            chosen[nch++] = bi;
            for (int k = 0; k < W; k++) cov[k] |= b[bi][k];
        }
        int full_ok = 1;
        for (int k = 0; k < W; k++) if (cov[k] != full[k]) { full_ok = 0; break; }
        if (full_ok && nch > 0) {
            int w = n;
            n++;
            col[w] = 1 - c;
            deg[w] = 0;
            for (int i = 0; i < nch; i++) add_e(chosen[i], w);
            return 1;
        }
    }
    return 0;
}

static void record_best(void) {
    bn = n;
    for (int v = 0; v < n; v++) {
        bdeg[v] = deg[v];
        bcol[v] = col[v];
        for (int i = 0; i < deg[v]; i++) badj[v][i] = adjl[v][i];
    }
}

static void restore_best(void) {
    n = bn;
    for (int v = 0; v < n; v++) {
        deg[v] = bdeg[v];
        col[v] = bcol[v];
        for (int i = 0; i < deg[v]; i++) adjl[v][i] = badj[v][i];
    }
}

/* Move: add an edge between two spare-degree vertices on opposite sides. */
static void mv_add(void) {
    static int sp[MAXN];
    int ns = 0;
    for (int v = 0; v < n; v++) if (deg[v] < dd) sp[ns++] = v;
    if (ns < 2) return;
    for (int t = 0; t < 40; t++) {
        int a = sp[rndi(ns)], b = sp[rndi(ns)];
        if (a == b || col[a] == col[b] || adjacent(a, b)) continue;
        add_e(a, b);
        log_add(a, b);
        return;
    }
}

/* Move: delete an edge, then reattach one endpoint to a spare opposite vertex. */
static void mv_swap(void) {
    static int cd[MAXN];
    int u = -1;
    for (int t = 0; t < 50 && u < 0; t++) {
        int x = rndi(n);
        if (deg[x] > 0) u = x;
    }
    if (u < 0) return;
    int v = adjl[u][rndi(deg[u])];
    del_e(u, v);
    log_rem(u, v);
    int e, f;
    if (rndi(2)) { e = u; f = v; } else { e = v; f = u; }
    int nc = 0;
    for (int x = 0; x < n; x++)
        if (col[x] != col[e] && x != f && deg[x] < dd && !adjacent(e, x))
            cd[nc++] = x;
    if (nc == 0) return;
    int x = cd[rndi(nc)];
    add_e(e, x);
    log_add(e, x);
}

/* Move: delete a random edge. */
static void mv_remove(void) {
    int u = -1;
    for (int t = 0; t < 50 && u < 0; t++) {
        int x = rndi(n);
        if (deg[x] > 0) u = x;
    }
    if (u < 0) return;
    int v = adjl[u][rndi(deg[u])];
    del_e(u, v);
    log_rem(u, v);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DD = atoi(argv[2]);
    uint64_t sd = (uint64_t)strtoull(argv[3], NULL, 10);
    rs ^= sd * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    dd = d;
    if (dd > MAXDEG) dd = MAXDEG;
    if (dd < 1) dd = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 2 || n0 > MAXN - 64 || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= dd || deg[v] >= dd || adjacent(u, v)) continue;
        add_e(u, v);
    }

    static int q[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adjl[x][i];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; }
            }
        }
    }

    clock_t t0 = clock();
    long cur = cost_now();
    if (cur == 0) record_best();
    long steps = 0, last_imp = 0;

    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        steps++;

        if (cur == 0) {
            if (n > bn) { record_best(); last_imp = steps; }
            if ((steps & 7) == 0 && try_grow()) {
                cur = cost_now();
                if (cur == 0 && n > bn) { record_best(); last_imp = steps; }
                continue;
            }
        }
        if (bn >= 0 && steps - last_imp > RESET_STEPS) {
            restore_best();
            cur = cost_now();
            last_imp = steps;
            continue;
        }

        nla = nlr = 0;
        double r = rnd01();
        if (r < 0.4) {
            mv_add();
            if (nla == 0) mv_swap();
        } else if (r < 0.95) {
            mv_swap();
        } else {
            mv_remove();
        }
        long nc = cost_now();
        double T = 0.2 + 1.3 * rnd01();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            undo();
        }
    }

    if (bn < 0) record_best();
    int m = 0;
    for (int v = 0; v < bn; v++) m += bdeg[v];
    m /= 2;
    printf("%d %d\n", bn, m);
    for (int v = 0; v < bn; v++)
        for (int i = 0; i < bdeg[v]; i++) {
            int u = badj[v][i];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: structured base, then the C engine searches concrete graphs by
# annealing edge moves and growing vertices whenever the diameter bound holds.
# Every returned graph passes lib.is_valid; the fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        fallback = (2, [(0, 1)])
    best_n, best_e = fallback[0], list(fallback[1])

    if best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None and base[0] > best_n and lib.is_valid(base[0], base[1], d, D):
        best_n, best_e = base[0], list(base[1])

    if best_n >= lib.moore_bound(d, D) or D < 2 or time_limit < 8:
        return best_n, best_e

    budget = max(1.0, 0.75 * time_limit - 3.0)
    timeout = budget + min(6.0, 0.15 * time_limit)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(best_n, best_e), timeout=timeout)
        n, e = lib.parse_graph_text(out)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
