"""Island program: araujo-lopez base for D=3 plus a C vertex-insertion annealer.

C engine: starts from the best valid graph, appends one vertex, and anneals
(2-switches, edge adds, targeted edge removals) to minimise
bad_pairs + 2 * degree_excess. When the cost reaches zero the graph is valid
with one more vertex, so the engine grows again from there.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

TIME_FRAC = 0.8               # fraction of time_limit used in total
C_MARGIN = 3.0                # seconds reserved for compile and output
GQ_Q_MAX = 9                  # largest q for which W(q) is built


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1024
#define WMAX 16
#define DEGCAP 128
#define EMAX 65536

typedef uint64_t Row[WMAX];

static int dd, DD;
static int n, m;
static int eu[EMAX], ev[EMAX];
static unsigned char A[NMAX][NMAX];
static int deg[NMAX];
static int col[NMAX];
static int adjc[NMAX];
static int adjl[NMAX][DEGCAP];
static Row bufA[NMAX], bufB[NMAX];
static int bn, bmm;
static int bu[EMAX], bv[EMAX];
static uint64_t rs;
static double budget;
static clock_t c0;
static time_t w0;

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int time_up(void) {
    double cpu = (double)(clock() - c0) / CLOCKS_PER_SEC;
    double wall = difftime(time(NULL), w0);
    return cpu >= budget || wall >= budget + 1.0;
}

static void build_adj(void) {
    int i;
    for (i = 0; i < n; i++) adjc[i] = 0;
    for (i = 0; i < m; i++) {
        int a = eu[i], b = ev[i];
        adjl[a][adjc[a]++] = b;
        adjl[b][adjc[b]++] = a;
    }
}

/* cost = bad unordered pairs (distance > DD) + 2 * degree excess over dd */
static int cost_of(int *bad_out, int *exc_out) {
    int v, k, r, t;
    build_adj();
    int W = (n + 63) >> 6;
    Row *R = bufA, *X = bufB;
    for (v = 0; v < n; v++) {
        for (k = 0; k < W; k++) R[v][k] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DD; r++) {
        int changed = 0;
        for (v = 0; v < n; v++) {
            for (k = 0; k < W; k++) X[v][k] = R[v][k];
            for (t = 0; t < adjc[v]; t++) {
                int u = adjl[v][t];
                for (k = 0; k < W; k++) X[v][k] |= R[u][k];
            }
            for (k = 0; k < W; k++) if (X[v][k] != R[v][k]) changed = 1;
        }
        Row *tmp = R; R = X; X = tmp;
        if (!changed) break;
    }
    long long cov = 0;
    for (v = 0; v < n; v++)
        for (k = 0; k < W; k++) cov += popc(R[v][k]);
    int bad = (int)(((long long)n * n - cov) / 2);
    int exc = 0;
    for (v = 0; v < n; v++) if (deg[v] > dd) exc += deg[v] - dd;
    *bad_out = bad;
    *exc_out = exc;
    return bad + 2 * exc;
}

static void add_edge(int u, int v) {
    eu[m] = u; ev[m] = v; m++;
    A[u][v] = 1; A[v][u] = 1;
    deg[u]++; deg[v]++;
}

static void pop_edge(void) {
    m--;
    int u = eu[m], v = ev[m];
    A[u][v] = 0; A[v][u] = 0;
    deg[u]--; deg[v]--;
}

static void remove_at(int i) {
    int u = eu[i], v = ev[i];
    m--;
    eu[i] = eu[m]; ev[i] = ev[m];
    A[u][v] = 0; A[v][u] = 0;
    deg[u]--; deg[v]--;
}

static void undo_remove(int i, int u, int v) {
    eu[m] = eu[i]; ev[m] = ev[i];
    eu[i] = u; ev[i] = v;
    m++;
    A[u][v] = 1; A[v][u] = 1;
    deg[u]++; deg[v]++;
}

/* change edge idx from (uo,vo) to (un,vn); degrees untouched */
static void set_edge(int idx, int un, int vn, int uo, int vo) {
    A[uo][vo] = 0; A[vo][uo] = 0;
    A[un][vn] = 1; A[vn][un] = 1;
    eu[idx] = un; ev[idx] = vn;
}

static void reset_to(int nn, const int *U, const int *V, int mm) {
    int i;
    int lim = n > nn ? n : nn;
    for (i = 0; i < lim; i++) {
        memset(A[i], 0, (size_t)lim);
        deg[i] = 0;
    }
    n = nn;
    m = 0;
    for (i = 0; i < mm; i++) add_edge(U[i], V[i]);
}

static void save_best(void) {
    bn = n;
    bmm = m;
    memcpy(bu, eu, sizeof(int) * (size_t)m);
    memcpy(bv, ev, sizeof(int) * (size_t)m);
}

static void grow_vertex(void) {
    int x = n;
    n++;
    deg[x] = 0;
    col[x] = (int)(rnd64() & 1);
    for (int a = 0; a < 8 * dd + 16 && deg[x] < dd; a++) {
        int v = rndint(x);
        if (col[v] == col[x] || A[x][v] || deg[v] > dd) continue;
        add_edge(x, v);
    }
}

/* anneal from the current state; returns 1 as soon as cost is zero */
static int stage(long iters, double T0, double T1) {
    int bad, exc;
    int cost = cost_of(&bad, &exc);
    if (cost == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 63) == 0 && time_up()) return 0;
        double frac = (double)it / (double)iters;
        double T = T1 + (T0 - T1) * (1.0 - frac);
        double r = rnd01();
        int kind;
        int nb = 0, ne = 0, nc;
        int acc;
        if (exc > 0) kind = (r < 0.35) ? 2 : (r < 0.8 ? 0 : 1);
        else kind = (r < 0.75) ? 0 : 1;

        if (kind == 0) {
            if (m < 2) continue;
            int i = rndint(m), j = rndint(m);
            if (i == j) continue;
            int p = eu[i], q = ev[i], s = eu[j], t = ev[j];
            int a1 = (col[p] == 0) ? p : q, b1 = (col[p] == 0) ? q : p;
            int a2 = (col[s] == 0) ? s : t, b2 = (col[s] == 0) ? t : s;
            if (a1 == a2 || b1 == b2 || A[a1][b2] || A[a2][b1]) continue;
            set_edge(i, a1, b2, a1, b1);
            set_edge(j, a2, b1, a2, b2);
            nc = cost_of(&nb, &ne);
            acc = (nc <= cost) || (rnd01() < exp(-(double)(nc - cost) / T));
            if (acc) {
                cost = nc; bad = nb; exc = ne;
            } else {
                set_edge(i, a1, b1, a1, b2);
                set_edge(j, a2, b2, a2, b1);
            }
        } else if (kind == 1) {
            int u = rndint(n), v = rndint(n);
            if (u == v || col[u] == col[v] || A[u][v] || deg[u] > dd || deg[v] > dd) continue;
            add_edge(u, v);
            nc = cost_of(&nb, &ne);
            acc = (nc <= cost) || (rnd01() < exp(-(double)(nc - cost) / T));
            if (acc) {
                cost = nc; bad = nb; exc = ne;
            } else {
                pop_edge();
            }
        } else {
            if (m < 1) continue;
            int i = -1;
            for (int tr = 0; tr < 50; tr++) {
                int c = rndint(m);
                if (exc == 0 || deg[eu[c]] > dd || deg[ev[c]] > dd) { i = c; break; }
            }
            if (i < 0) continue;
            int u = eu[i], v = ev[i];
            remove_at(i);
            nc = cost_of(&nb, &ne);
            acc = (nc <= cost) || (rnd01() < exp(-(double)(nc - cost) / T));
            if (acc) {
                cost = nc; bad = nb; exc = ne;
            } else {
                undo_remove(i, u, v);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void emit(void) {
    printf("%d %d\n", bn, bmm);
    for (int i = 0; i < bmm; i++) printf("%d %d\n", bu[i], bv[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    c0 = clock();
    w0 = time(NULL);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 2 || m0 < 0 || m0 > EMAX || n0 > NMAX || dd < 1 || DD < 1) {
        printf("0 0\n");
        return 0;
    }

    n = n0;
    m = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (A[u][v]) continue;
        if (deg[u] >= DEGCAP - 2 || deg[v] >= DEGCAP - 2) continue;
        add_edge(u, v);
    }
    save_best();

    /* 2-colour the input; the engine needs every edge to join opposite colours */
    build_adj();
    for (int v = 0; v < n; v++) col[v] = -1;
    {
        int st[NMAX];
        for (int s = 0; s < n; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int sp = 0;
            st[sp++] = s;
            while (sp > 0) {
                int u = st[--sp];
                for (int t = 0; t < adjc[u]; t++) {
                    int w = adjl[u][t];
                    if (col[w] == -1) {
                        col[w] = 1 - col[u];
                        st[sp++] = w;
                    }
                }
            }
        }
    }
    for (int i = 0; i < m; i++) {
        if (col[eu[i]] == col[ev[i]]) { emit(); return 0; }
    }

    double T0 = 1.0, T1 = 0.05;
    long iters = 40000;
    int fails = 0;
    while (!time_up()) {
        if (bn + 1 >= NMAX) break;
        reset_to(bn, bu, bv, bmm);
        grow_vertex();
        if (stage(iters, T0, T1)) {
            save_best();
            fails = 0;
        } else {
            fails++;
            if (fails % 4 == 0 && iters < 400000) iters = iters * 3 / 2;
        }
    }
    emit();
    return 0;
}
"""


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
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
    return color


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the current graph."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

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
    """W(q) for the largest prime power q with q <= d-1 and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + TIME_FRAC * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    if d >= 3 and D == 3:
        base = _pg_base(d)
        if base is not None and lib.is_prime_power(d - 1):
            return _finish(cands + [base], d, D)   # Moore-extremal

    # D = 3, d - 2 a prime power: Araujo-Pardo & Lopez record, order 2(q^2+q+5), degree d.
    if D == 3 and d >= 5:
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                cands.append(lib.araujo_lopez_graph(q))
            except ValueError:
                pass

    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.append(_extend(g[0], g[1], d, D, rng,
                                     min(end, time.monotonic() + 0.3)))

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_extend(g[0], g[1], d, D, rng,
                                     min(end, time.monotonic() + 0.3)))

    best = _finish(cands, d, D)

    # Vertex-insertion annealing in C, starting from the best valid graph.
    remaining = end - time.monotonic() - C_MARGIN
    if remaining >= 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                             stdin_graph=best, timeout=remaining + 5.0)
            n2, e2 = lib.parse_graph_text(text)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except (RuntimeError, ValueError, OSError):
            pass

    return best
