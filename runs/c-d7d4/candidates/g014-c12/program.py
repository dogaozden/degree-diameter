import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1400
#define MAXD 24
#define WMAX 22
#define ITER 1500

static int d, D, n;
static int dg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static int badv[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double t_start = 0.0, t_limit = 1.0;
static uint64_t BA[MAXN][WMAX], BB[MAXN][WMAX];
static int bn = 0;
static int bdg[MAXN], bcol[MAXN];
static int badj[MAXN][MAXD];

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC - t_start; }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static int has_edge(int a, int b) {
    for (int k = 0; k < dg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static void rm_half(int a, int b) {
    for (int k = 0; k < dg[a]; k++)
        if (adj[a][k] == b) { adj[a][k] = adj[a][--dg[a]]; return; }
}
static void add_edge(int a, int b) { adj[a][dg[a]++] = b; adj[b][dg[b]++] = a; }
static void rm_edge(int a, int b) { rm_half(a, b); rm_half(b, a); }

/* Bad pairs (distance > D, unreachable included); also sets badv[]. */
static long long cost(void) {
    int words = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = BA;
    uint64_t (*nxt)[WMAX] = BB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < words; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < words; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < dg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < words; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur; cur = nxt; nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < words; w++) pc += popc(cur[v][w]);
        badv[v] = n - pc;
        tot += n - pc;
    }
    return tot / 2;
}

/* Bipartite double-edge switches minimising bad pairs. Returns final cost. */
static long long anneal(long long iters, double T0, double T1) {
    static int side0[MAXN];
    long long cur = cost();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > t_limit) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int ns = 0;
        for (int v = 0; v < n; v++) if (col[v] == 0 && dg[v] > 0) side0[ns++] = v;
        if (ns < 2) break;
        int a = side0[rndint(ns)];
        int b = adj[a][rndint(dg[a])];
        int c = side0[rndint(ns)];
        if (c == a) continue;
        int e = adj[c][rndint(dg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        rm_edge(a, b); rm_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long long nc = cost();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            rm_edge(a, e); rm_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur;
}

/* Add cross-side edges between deficient vertices (never hurts validity). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (dg[v] < d) { if (col[v] == 0) L[nl++] = v; else R[nr++] = v; }
    }
    for (int i = nl - 1; i > 0; i--) { int j = rndint(i + 1); int t = L[i]; L[i] = L[j]; L[j] = t; }
    for (int i = nr - 1; i > 0; i--) { int j = rndint(i + 1); int t = R[i]; R[i] = R[j]; R[j] = t; }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && dg[a] < d; j++) {
            int b = R[j];
            if (dg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* New vertex of colour c joined to up to d opposite-side vertices. */
static void add_vertex(int c) {
    static int cand[MAXN];
    int w = n++;
    col[w] = c;
    dg[w] = 0;
    int nc = 0;
    for (int v = 0; v < w; v++) if (col[v] != c) cand[nc++] = v;
    for (int i = nc - 1; i > 0; i--) { int j = rndint(i + 1); int t = cand[i]; cand[i] = cand[j]; cand[j] = t; }
    int p = 0;
    for (int i = 0; i < nc; i++) {
        if (dg[cand[i]] < d) { int t = cand[i]; cand[i] = cand[p]; cand[p] = t; p++; }
    }
    int take = d < nc ? d : nc;
    for (int i = 0; i < take; i++) {
        int x = cand[i];
        if (dg[x] >= d) {
            int y = adj[x][rndint(dg[x])];
            rm_edge(x, y);
        }
        add_edge(w, x);
    }
}

/* Remove vertex x, moving the last vertex into its slot. */
static void delete_vertex(int x) {
    for (int k = 0; k < dg[x]; k++) rm_half(adj[x][k], x);
    int L = n - 1;
    if (x != L) {
        col[x] = col[L];
        dg[x] = dg[L];
        for (int k = 0; k < dg[L]; k++) adj[x][k] = adj[L][k];
        for (int k = 0; k < dg[x]; k++) {
            int z = adj[x][k];
            for (int j = 0; j < dg[z]; j++) {
                if (adj[z][j] == L) { adj[z][j] = x; break; }
            }
        }
    }
    dg[L] = 0;
    n--;
}

/* Delete the k vertices with most bad pairs (uses badv from the last cost()). */
static void delete_worst(int k) {
    static int idx[MAXN];
    static long long key[MAXN];
    if (k > n - 2) k = n - 2;
    if (k < 1) return;
    for (int v = 0; v < n; v++) {
        idx[v] = v;
        key[v] = (long long)badv[v] * 4096 + rndint(4096);
    }
    for (int i = 0; i < k; i++) {
        int bi = i;
        for (int j = i + 1; j < n; j++) if (key[idx[j]] > key[idx[bi]]) bi = j;
        int t = idx[i]; idx[i] = idx[bi]; idx[bi] = t;
    }
    for (int i = 1; i < k; i++) {
        int x = idx[i], j = i - 1;
        while (j >= 0 && idx[j] > x) { idx[j + 1] = idx[j]; j--; }
        idx[j + 1] = x;
    }
    for (int i = k - 1; i >= 0; i--) delete_vertex(idx[i]);
}

static void save_best(void) {
    bn = n;
    memcpy(bdg, dg, sizeof(int) * (size_t)n);
    memcpy(bcol, col, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(adj));
}

static void restore_best(void) {
    n = bn;
    memcpy(dg, bdg, sizeof(int) * (size_t)bn);
    memcpy(col, bcol, sizeof(int) * (size_t)bn);
    memcpy(adj, badj, sizeof(adj));
}

static void print_kdd(int dd) {
    printf("%d %d\n", 2 * dd, dd * dd);
    for (int i = 0; i < dd; i++)
        for (int j = 0; j < dd; j++)
            printf("%d %d\n", i, dd + j);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long long sd = atoll(argv[3]);
    rs ^= (uint64_t)sd * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    t_start = (double)clock() / CLOCKS_PER_SEC;
    t_limit = atof(argv[4]);
    if (d < 1 || d > MAXD - 2 || D < 1) { printf("1 0\n"); return 0; }

    n = 0;
    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2) { n = 0; m0 = 0; }
    if (n < 0 || n > MAXN - 64) { n = 0; m0 = 0; }
    int nin = n;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nin || v >= nin || u == v) continue;
        if (dg[u] >= d || dg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* Bipartite colouring of the loaded graph. */
    for (int v = 0; v < n; v++) col[v] = -1;
    static int queue[MAXN];
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt && ok) {
            int u = queue[qh++];
            for (int k = 0; k < dg[u]; k++) {
                int v = adj[u][k];
                if (col[v] == -1) { col[v] = 1 - col[u]; queue[qt++] = v; }
                else if (col[v] == col[u]) { ok = 0; break; }
            }
        }
    }
    if (!ok) {
        for (int v = 0; v < nin; v++) dg[v] = 0;
        n = 0;
    }
    if (n == 0) {
        n = 2 * d;
        for (int v = 0; v < n; v++) { dg[v] = 0; col[v] = (v < d) ? 0 : 1; }
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++)
                add_edge(i, d + j);
    }

    bn = 0;
    while (now() < t_limit) {
        long long c = cost();
        if (c > 0) {
            c = anneal(ITER, 1.2, 0.08);
            if (c > 0) {
                cost();
                if (n <= 3) break;
                if (bn > 0 && (double)n < 0.85 * (double)bn && rnd01() < 0.5)
                    restore_best();
                else
                    delete_worst(n / 40 + 1);
                continue;
            }
        }
        /* Valid graph here. */
        if (n > bn) save_best();
        if (n + 2 >= MAXN) break;
        fill();
        add_vertex(rndint(2));
        fill();
    }

    if (bn == 0) { print_kdd(d); return 0; }
    long long m = 0;
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < bdg[v]; k++)
            if (v < badj[v][k]) m++;
    printf("%d %lld\n", bn, m);
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < bdg[v]; k++) {
            int u = badj[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Constructions.
# ----------------------------------------------------------------------------

def _largest_pp(m, cap=10 ** 9):
    """Largest prime power q with 2 <= q <= min(m, cap), or None."""
    for q in range(min(m, cap), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _smallest_pp(lo, cap):
    """Smallest prime power q with lo <= q <= cap, or None."""
    for q in range(max(2, lo), cap + 1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4, order 2(q+1)(q^2+1)."""
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
    edges = []
    nl = 0
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
            for p in L:
                edges.append((p, P + nl))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nl += 1
    return 2 * P, edges


def _starts(d, D):
    """Structured valid starts. Each has degree q+1 (possibly above d); the C engine thins them."""
    starts = []
    if D == 3:
        q = _largest_pp(d - 1)
        if q:
            starts.append(lib.projective_plane_incidence(q))
        q2 = _smallest_pp(d, 13)
        if q2:
            starts.append(lib.projective_plane_incidence(q2))
    elif D >= 4:
        q = _largest_pp(d - 1, 16)
        if q:
            starts.append(_gq_w(q))
        q2 = _smallest_pp(d, 11)
        if q2:
            starts.append(_gq_w(q2))
    return starts


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = list(lib.haar_graph(d, range(d)))  # K_{d,d}, always valid for D >= 2
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, list(e)

    if best[0] >= moore:
        return best[0], best[1]

    starts = _starts(d, D)
    for n0, e0 in starts:
        consider(n0, e0)
    if best[0] >= moore:
        return best[0], best[1]

    avail = max(1.0, 0.8 * time_limit - 3.0)
    runs = starts if starts else [None]
    per = avail / len(runs)
    rng = random.Random(seed)

    for idx, st in enumerate(runs):
        elapsed = time.monotonic() - t0
        budget = min(per, 0.85 * time_limit - elapsed - 1.0)
        if budget < 0.5:
            break
        if st is None:
            stdin = None
        else:
            edges = list(st[1])
            rng.shuffle(edges)
            stdin = (st[0], edges)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 31 + idx, f"{budget:.2f}"],
                            stdin_graph=stdin, timeout=budget + 5.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass
        if best[0] >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        n, e = lib.haar_graph(d, range(d))
        return n, list(e)
    return best[0], best[1]
