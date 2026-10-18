import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baselines: projective plane and generalized quadrangle incidence graphs.
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


def _is_regular(g, d):
    """True if every vertex of graph g = (n, edges) has degree exactly d."""
    n, e = g
    deg = [0] * n
    for u, v in e:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (simulated annealing).
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d exactly.
# The search returns (n, edges, cost); cost 0 means valid, otherwise the
# oversized near-valid graph is handed to the C repair engine.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges, cost); cost 0 means valid."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges), cost


# ----------------------------------------------------------------------------
# C engine.
#
# Mode 0: iterated defect-deletion repair + greedy vertex extension (ILS).
# Mode 1: pair growth on a d-regular valid bipartite graph. Insert two new
#         vertices by splitting d edges, then anneal with degree-preserving
#         2-switches to remove all pairs at distance > D. Accept only valid
#         results, otherwise restore the backup.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define EXTRA 3000
#define EXT_FAILS 150
#define PAIR_ITERS 800

static int d, D, cnt, CAP, WCAP;
static int *nb, *deg, *col, *badv, *cl;
static int *bk_nb, *bk_deg, *bk_col, bk_cnt;
static int *pb_perm, *pb_pa, *pb_pb;
static char *usedA;
static uint64_t *RA, *RB;
static uint64_t rs;
static double budget_s;
static clock_t t0;
static int best_n = 1, best_m = 0;
static int *best_eu = NULL, *best_ev = NULL;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static int timeup(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC > budget_s;
}

static int has_edge(int a, int b) {
    for (int j = 0; j < deg[a]; j++) if (nb[a * d + j] == b) return 1;
    return 0;
}

static void drop_from(int v, int u) {
    int *L = nb + (size_t)v * d;
    for (int j = 0; j < deg[v]; j++) {
        if (L[j] == u) { L[j] = L[deg[v] - 1]; deg[v]--; return; }
    }
}

static void add_edge(int a, int b) {
    nb[a * d + deg[a]++] = b;
    nb[b * d + deg[b]++] = a;
}

static void replace_nb(int a, int old, int nw) {
    int *L = nb + (size_t)a * d;
    for (int j = 0; j < deg[a]; j++) if (L[j] == old) { L[j] = nw; return; }
}

static int color_graph(void) {
    int *q = malloc(sizeof(int) * (size_t)(cnt + 1));
    int head = 0, tail = 0, ok = 1;
    for (int v = 0; v < cnt; v++) col[v] = -1;
    for (int s = 0; s < cnt && ok; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        q[tail++] = s;
        while (head < tail && ok) {
            int u = q[head++];
            for (int j = 0; j < deg[u]; j++) {
                int v = nb[u * d + j];
                if (col[v] == -1) { col[v] = 1 - col[u]; q[tail++] = v; }
                else if (col[v] == col[u]) { ok = 0; break; }
            }
        }
    }
    free(q);
    return ok;
}

/* badv[v] = number of vertices farther than D from v; returns number of bad pairs. */
static long eval(void) {
    int n = cnt;
    if (n == 0) return 0;
    size_t W = (size_t)(n + 63) / 64;
    uint64_t *R = RA, *S = RB;
    memset(R, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) R[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *out = S + (size_t)v * W;
            const uint64_t *in = R + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * W);
            for (int j = 0; j < deg[v]; j++) {
                const uint64_t *y = R + (size_t)nb[v * d + j] * W;
                for (size_t w = 0; w < W; w++) out[w] |= y[w];
            }
            if (!changed && memcmp(out, in, sizeof(uint64_t) * W) != 0) changed = 1;
        }
        uint64_t *tmp = R; R = S; S = tmp;
        if (!changed) break;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *x = R + (size_t)v * W;
        for (size_t w = 0; w < W; w++) c += __builtin_popcountll(x[w]);
        badv[v] = n - c;
        tot += n - c;
    }
    return tot / 2;
}

static void remove_vertex(int x) {
    for (int j = 0; j < deg[x]; j++) drop_from(nb[x * d + j], x);
    deg[x] = 0;
    int L = cnt - 1;
    if (x != L) {
        for (int j = 0; j < deg[L]; j++) {
            int u = nb[L * d + j];
            int *M = nb + (size_t)u * d;
            for (int t = 0; t < deg[u]; t++) if (M[t] == L) M[t] = x;
        }
        memcpy(nb + (size_t)x * d, nb + (size_t)L * d, sizeof(int) * (size_t)d);
        deg[x] = deg[L];
        col[x] = col[L];
    }
    deg[L] = 0;
    cnt--;
}

static void repair(void) {
    long bad = eval();
    while (bad > 0 && cnt > 2 && !timeup()) {
        int pick = -1, bb = -1, ties = 0;
        for (int v = 0; v < cnt; v++) {
            if (badv[v] > bb) { bb = badv[v]; pick = v; ties = 1; }
            else if (badv[v] == bb) {
                ties++;
                if (rndint(ties) == 0) pick = v;
            }
        }
        remove_vertex(pick);
        bad = eval();
    }
}

static void extend(void) {
    int fails = 0;
    while (fails < EXT_FAILS && cnt + 1 < CAP && !timeup()) {
        int c[2] = {0, 0};
        for (int v = 0; v < cnt; v++) if (deg[v] < d) c[col[v]]++;
        if (c[0] < d && c[1] < d) break;
        int s = rndint(2);
        if (c[s] < d) s = 1 - s;
        int nc = 0;
        for (int v = 0; v < cnt; v++) if (col[v] == s && deg[v] < d) cl[nc++] = v;
        for (int i = 0; i < d; i++) {
            int j = i + rndint(nc - i);
            int t = cl[i]; cl[i] = cl[j]; cl[j] = t;
        }
        int w = cnt++;
        deg[w] = 0;
        col[w] = 1 - s;
        for (int i = 0; i < d; i++) add_edge(cl[i], w);
        if (eval() == 0) {
            fails = 0;
        } else {
            fails++;
            for (int i = 0; i < d; i++) drop_from(cl[i], w);
            deg[w] = 0;
            cnt--;
        }
    }
}

static void snap_take(void) {
    int m = 0;
    for (int v = 0; v < cnt; v++)
        for (int j = 0; j < deg[v]; j++) if (nb[v * d + j] > v) m++;
    free(best_eu);
    free(best_ev);
    best_eu = malloc(sizeof(int) * (size_t)(m + 1));
    best_ev = malloc(sizeof(int) * (size_t)(m + 1));
    int k = 0;
    for (int v = 0; v < cnt; v++)
        for (int j = 0; j < deg[v]; j++) {
            int u = nb[v * d + j];
            if (u > v) { best_eu[k] = v; best_ev[k] = u; k++; }
        }
    best_n = cnt;
    best_m = m;
}

static void restore(void) {
    cnt = best_n;
    for (int v = 0; v < cnt; v++) deg[v] = 0;
    for (int i = 0; i < best_m; i++) add_edge(best_eu[i], best_ev[i]);
    color_graph();
}

static int is_regular(void) {
    for (int v = 0; v < cnt; v++) if (deg[v] != d) return 0;
    return 1;
}

/* Insert two vertices w (side 0) and w2 (side 1) by splitting d edges (a_i, b_i)
   with distinct a_i. Requires a d-regular bipartite graph. Returns 1 on success. */
static int pair_insert(void) {
    int n = cnt;
    if (n + 2 > CAP) return 0;
    int nside1 = 0;
    for (int v = 0; v < n; v++) if (col[v] == 1) pb_perm[nside1++] = v;
    for (int i = nside1 - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = pb_perm[i]; pb_perm[i] = pb_perm[j]; pb_perm[j] = t;
    }
    memset(usedA, 0, (size_t)n);
    int picked = 0;
    for (int idx = 0; idx < nside1 && picked < d; idx++) {
        int b = pb_perm[idx];
        int c = 0, pick = -1;
        for (int j = 0; j < deg[b]; j++) {
            int a = nb[b * d + j];
            if (usedA[a]) continue;
            c++;
            if (rndint(c) == 0) pick = a;
        }
        if (pick < 0) continue;
        usedA[pick] = 1;
        pb_pa[picked] = pick;
        pb_pb[picked] = b;
        picked++;
    }
    if (picked < d) return 0;
    int w = n, w2 = n + 1;
    deg[w] = 0; deg[w2] = 0;
    col[w] = 0; col[w2] = 1;
    for (int i = 0; i < d; i++) {
        int a = pb_pa[i], b = pb_pb[i];
        replace_nb(a, b, w2);
        replace_nb(b, a, w);
        nb[w * d + deg[w]++] = b;
        nb[w2 * d + deg[w2]++] = a;
    }
    cnt = n + 2;
    return 1;
}

static void pick_edge(int *x, int *y) {
    int v = rndint(cnt);
    while (deg[v] == 0) v = rndint(cnt);
    int u = nb[v * d + rndint(deg[v])];
    if (col[v] == 0) { *x = v; *y = u; }
    else { *x = u; *y = v; }
}

/* Degree-preserving 2-switches minimising bad pairs. Returns the final bad count. */
static long anneal_pairs(int iters) {
    long cur = eval();
    if (cur == 0) return 0;
    double T0 = 1.0 + 0.05 * (double)cur;
    for (int t = 0; t < iters && cur > 0; t++) {
        if (timeup()) break;
        int x1, y1, x2, y2;
        pick_edge(&x1, &y1);
        pick_edge(&x2, &y2);
        if (x1 == x2 || y1 == y2) continue;
        if (has_edge(x1, y2) || has_edge(x2, y1)) continue;
        replace_nb(x1, y1, y2);
        replace_nb(y2, x2, x1);
        replace_nb(x2, y2, y1);
        replace_nb(y1, x1, x2);
        long nw = eval();
        double T = T0 * (1.0 - (double)t / iters);
        if (T < 0.05) T = 0.05;
        double u = (double)(rnd() % 1000000ULL) / 1000000.0;
        if (nw <= cur || u < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            replace_nb(x1, y2, y1);
            replace_nb(y2, x1, x2);
            replace_nb(x2, y1, y2);
            replace_nb(y1, x2, x1);
        }
    }
    return cur;
}

static void backup_state(void) {
    bk_cnt = cnt;
    memcpy(bk_nb, nb, sizeof(int) * (size_t)cnt * (size_t)d);
    memcpy(bk_deg, deg, sizeof(int) * (size_t)cnt);
    memcpy(bk_col, col, sizeof(int) * (size_t)cnt);
}

static void restore_state(void) {
    cnt = bk_cnt;
    memcpy(nb, bk_nb, sizeof(int) * (size_t)cnt * (size_t)d);
    memcpy(deg, bk_deg, sizeof(int) * (size_t)cnt);
    memcpy(col, bk_col, sizeof(int) * (size_t)cnt);
}

static void pair_grow(void) {
    if (!is_regular() || eval() != 0) return;
    snap_take();
    while (!timeup()) {
        backup_state();
        if (!pair_insert()) {
            if (cnt + 2 > CAP) break;
            continue;
        }
        long c = anneal_pairs(PAIR_ITERS);
        if (c == 0) snap_take();
        else restore_state();
    }
}

static void die(const char *msg) {
    fprintf(stderr, "%s\n", msg);
    exit(2);
}

int main(int argc, char **argv) {
    if (argc < 5) die("usage: prog d D seed seconds [mode]");
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    if (d < 1) d = 1;
    if (D < 1) D = 1;
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x12345678ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    int mode = (argc >= 6) ? atoi(argv[5]) : 0;
    t0 = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 1) n = 1;
    if (m < 0) m = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    int me = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        eu[me] = u;
        ev[me] = v;
        me++;
    }

    CAP = n + EXTRA;
    WCAP = (CAP + 63) / 64;
    nb = malloc(sizeof(int) * (size_t)CAP * (size_t)d);
    deg = calloc((size_t)CAP, sizeof(int));
    col = calloc((size_t)CAP, sizeof(int));
    badv = calloc((size_t)CAP, sizeof(int));
    cl = malloc(sizeof(int) * (size_t)CAP);
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * (size_t)WCAP);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * (size_t)WCAP);
    bk_nb = malloc(sizeof(int) * (size_t)CAP * (size_t)d);
    bk_deg = calloc((size_t)CAP, sizeof(int));
    bk_col = calloc((size_t)CAP, sizeof(int));
    pb_perm = malloc(sizeof(int) * (size_t)CAP);
    pb_pa = malloc(sizeof(int) * (size_t)(d + 1));
    pb_pb = malloc(sizeof(int) * (size_t)(d + 1));
    usedA = malloc((size_t)CAP);
    if (!nb || !deg || !col || !badv || !cl || !RA || !RB ||
        !bk_nb || !bk_deg || !bk_col || !pb_perm || !pb_pa || !pb_pb || !usedA)
        die("out of memory");

    cnt = n;
    for (int i = 0; i < me; i++) {
        int u = eu[i], v = ev[i];
        if (deg[u] < d && deg[v] < d && !has_edge(u, v)) add_edge(u, v);
    }
    if (!color_graph()) {
        printf("1 0\n");
        return 0;
    }

    repair();
    if (eval() == 0) {
        if (mode == 1) {
            pair_grow();
        } else {
            extend();
            snap_take();
        }
    }

    if (mode == 0) {
        while (!timeup()) {
            restore();
            int kicks = 1 + rndint(4);
            for (int k = 0; k < kicks && cnt > 2; k++) remove_vertex(rndint(cnt));
            repair();
            if (eval() != 0) continue;
            extend();
            if (cnt >= best_n) snap_take();
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
    return 0;
}
"""


def _c_run(n, edges, d, D, seed, budget, mode):
    """Run the C engine (mode 0 = repair/extend ILS, mode 1 = pair growth) and return (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mode],
                    stdin_graph=(n, edges), timeout=budget + 8.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = max(2.0, time_limit - 7.0)
    end = start + T
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

    # Exact constructions: return immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley search with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    cand = None  # best oversized near-valid graph: (n, edges, cost)

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    search_end = start + 0.5 * T
    while time.monotonic() < search_end:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        N, E, cost = _search(d, D, k, G, Ts, Invs, rng, search_end, 4000, 1200)
        if cost == 0:
            wins[k] += 1
            consider(N, E)
        elif N > best_n and (cand is None or cost < cand[2]):
            cand = (N, E, cost)

    # C phase 1: pair growth on the best d-regular valid graph.
    remaining = end - time.monotonic()
    if remaining >= 4.0 and _is_regular(best, d):
        share = 0.4 * remaining
        try:
            n2, e2 = _c_run(best[0], best[1], d, D, seed, share - 1.0, 1)
            consider(n2, e2)
        except Exception:
            pass

    # C phase 2: repair and extend the oversized candidate and the best valid graph.
    remaining = end - time.monotonic()
    if remaining >= 3.0:
        starts = []
        if cand is not None:
            starts.append((cand[0], cand[1]))
        starts.append(best)
        share = remaining / len(starts)
        for idx, (n0, e0) in enumerate(starts):
            c_budget = share - 1.0
            if c_budget < 1.0:
                continue
            try:
                n2, e2 = _c_run(n0, e0, d, D, seed + idx, c_budget, 0)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
