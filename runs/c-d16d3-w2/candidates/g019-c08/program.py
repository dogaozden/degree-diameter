import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing with vertex insertion ("grow and repair").
#
# State is always a valid bipartite graph with max degree DEG and diameter <=
# DIA. A growth step adds one vertex on a random side, attached to up to DEG
# vertices of the other side (saturated ones give up one edge). Cost is the
# number of unordered pairs at distance > DIA, computed with bitset balls.
# Repair moves are degree-preserving edge rewires and free edge additions
# (which never increase cost). If cost returns to 0 the larger graph is kept;
# otherwise the snapshot is restored.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIA, CAP, N, W;
static int *adjv, *dg, *col, *sn_u, *sn_v, *sn_col;
static unsigned char *mat;
static uint64_t *bufA, *bufB, *cur, *nxt;
static uint64_t rs = 88172645463325252ULL;
static int sn_N, sn_m;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void add_edge(int a, int b) {
    adjv[a * DEG + dg[a]] = b; dg[a]++;
    adjv[b * DEG + dg[b]] = a; dg[b]++;
    mat[a * CAP + b] = 1; mat[b * CAP + a] = 1;
}

static void del_one(int a, int b) {
    int k;
    for (k = 0; k < dg[a]; k++) {
        if (adjv[a * DEG + k] == b) {
            adjv[a * DEG + k] = adjv[a * DEG + dg[a] - 1];
            dg[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
    mat[a * CAP + b] = 0; mat[b * CAP + a] = 0;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,w) with dist > DIA, divided by 2. */
static long long cost(void) {
    int n = N, v, k, r, i;
    long long tot = 0;
    uint64_t *t;
    W = (n + 63) / 64;
    for (v = 0; v < n; v++) {
        uint64_t *c = cur + (size_t)v * W;
        for (i = 0; i < W; i++) c[i] = 0;
        c[v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DIA; r++) {
        for (v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *cv = cur + (size_t)v * W;
            for (i = 0; i < W; i++) o[i] = cv[i];
            for (k = 0; k < dg[v]; k++) {
                uint64_t *cu = cur + (size_t)adjv[v * DEG + k] * W;
                for (i = 0; i < W; i++) o[i] |= cu[i];
            }
        }
        t = cur; cur = nxt; nxt = t;
    }
    for (v = 0; v < n; v++) {
        uint64_t *c = cur + (size_t)v * W;
        for (i = 0; i < W; i++) tot += popc64(c[i]);
    }
    return ((long long)n * n - tot) / 2;
}

static void snapshot(void) {
    int v, k, m = 0;
    sn_N = N;
    for (v = 0; v < N; v++) {
        for (k = 0; k < dg[v]; k++) {
            int u = adjv[v * DEG + k];
            if (v < u) { sn_u[m] = v; sn_v[m] = u; m++; }
        }
    }
    sn_m = m;
    memcpy(sn_col, col, sizeof(int) * (size_t)N);
}

static void restore(void) {
    int v, k, i;
    for (v = 0; v < N; v++) {
        for (k = 0; k < dg[v]; k++) mat[v * CAP + adjv[v * DEG + k]] = 0;
        dg[v] = 0;
    }
    N = sn_N;
    memcpy(col, sn_col, sizeof(int) * (size_t)N);
    for (i = 0; i < sn_m; i++) add_edge(sn_u[i], sn_v[i]);
}

/* Add one vertex on a random side; attach to up to k opposite vertices. */
static int grow(void) {
    int c, x, cnt = 0, i, pass, added = 0, k, y, z;
    int *list;
    if (N >= CAP) return 0;
    c = rint_(2);
    x = N;
    N++;
    col[x] = c;
    dg[x] = 0;
    k = DEG - rint_(3);
    if (k < 1) k = 1;
    if (k > DEG) k = DEG;
    list = (int *)malloc(sizeof(int) * (size_t)(N + 1));
    for (i = 0; i < x; i++) if (col[i] != c) list[cnt++] = i;
    for (i = cnt - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = list[i]; list[i] = list[j]; list[j] = t;
    }
    for (pass = 0; pass < 2 && added < k; pass++) {
        for (i = 0; i < cnt && added < k; i++) {
            int full;
            y = list[i];
            full = dg[y] >= DEG;
            if ((pass == 0) == full) continue;   /* pass 0: non-full, pass 1: full */
            if (full) {
                z = adjv[y * DEG + rint_(dg[y])];
                remove_edge(y, z);
            }
            add_edge(x, y);
            added++;
        }
    }
    free(list);
    if (added == 0) { N--; return 0; }
    return 1;
}

/* Random vertex opposite to a, not b, not adjacent to a, with spare degree. */
static int pick_partner(int a, int b) {
    int t, c;
    for (t = 0; t < 80; t++) {
        c = rint_(N);
        if (c == a || c == b) continue;
        if (col[c] == col[a]) continue;
        if (dg[c] >= DEG) continue;
        if (mat[a * CAP + c]) continue;
        return c;
    }
    return -1;
}

static void move_rewire(double T, long long *cc) {
    int a = rint_(N), b, c;
    long long nc, delta;
    if (dg[a] == 0) return;
    b = adjv[a * DEG + rint_(dg[a])];
    c = pick_partner(a, b);
    if (c < 0) return;
    remove_edge(a, b);
    add_edge(a, c);
    nc = cost();
    delta = nc - *cc;
    if (delta <= 0 || rdbl() < exp(-(double)delta / T)) { *cc = nc; return; }
    remove_edge(a, c);
    add_edge(a, b);
}

static void move_add(long long *cc) {
    int t, a, c;
    for (t = 0; t < 80; t++) {
        a = rint_(N);
        if (dg[a] >= DEG) continue;
        c = pick_partner(a, -1);
        if (c < 0) continue;
        add_edge(a, c);
        *cc = cost();
        return;
    }
}

int main(int argc, char **argv) {
    int n0 = 0, m0 = 0, i, u, v, k, ok = 1;
    int *eu, *ev;
    double budget;
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (DEG < 1 || n0 < 0 || m0 < 0 || n0 > 3000 || m0 > 300000) { printf("0 0\n"); return 0; }

    if (n0 == 0) {
        n0 = 2 * DEG;
        m0 = DEG * DEG;
        eu = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
        ev = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
        k = 0;
        for (i = 0; i < DEG; i++)
            for (u = 0; u < DEG; u++) { eu[k] = i; ev[k] = DEG + u; k++; }
    } else {
        eu = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
        ev = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
        for (i = 0; i < m0; i++) {
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
        }
    }

    CAP = n0 + 1000;
    if (CAP > 4000) CAP = 4000;
    adjv = (int *)malloc(sizeof(int) * (size_t)CAP * (size_t)DEG);
    dg = (int *)calloc((size_t)CAP, sizeof(int));
    col = (int *)calloc((size_t)CAP, sizeof(int));
    sn_col = (int *)calloc((size_t)CAP, sizeof(int));
    sn_u = (int *)malloc(sizeof(int) * ((size_t)CAP * DEG + 1));
    sn_v = (int *)malloc(sizeof(int) * ((size_t)CAP * DEG + 1));
    mat = (unsigned char *)calloc((size_t)CAP * CAP, 1);
    bufA = (uint64_t *)calloc((size_t)CAP * ((CAP + 63) / 64), sizeof(uint64_t));
    bufB = (uint64_t *)calloc((size_t)CAP * ((CAP + 63) / 64), sizeof(uint64_t));
    cur = bufA; nxt = bufB;

    /* Load the start graph, checking degree bound and simplicity. */
    N = n0;
    for (i = 0; i < m0 && ok; i++) {
        u = eu[i]; v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
        if (mat[u * CAP + v] || dg[u] >= DEG || dg[v] >= DEG) { ok = 0; break; }
        add_edge(u, v);
    }
    if (ok) {
        int *stk = (int *)malloc(sizeof(int) * (size_t)(N + 1));
        int sp, x, y, s;
        for (i = 0; i < N; i++) col[i] = -1;
        for (s = 0; s < N && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0; sp = 0; stk[sp++] = s;
            while (sp > 0 && ok) {
                x = stk[--sp];
                for (k = 0; k < dg[x]; k++) {
                    y = adjv[x * DEG + k];
                    if (col[y] < 0) { col[y] = 1 - col[x]; stk[sp++] = y; }
                    else if (col[y] == col[x]) { ok = 0; break; }
                }
            }
        }
        free(stk);
    }
    if (!ok || cost() != 0) { printf("0 0\n"); return 0; }

    if (DEG >= 3 && DIA >= 3) {
        while (now() < budget && N < CAP) {
            double T = 0.3 + 0.4 * rdbl();
            long long c2;
            int it, maxit = 1500;
            snapshot();
            if (!grow()) { restore(); continue; }
            c2 = cost();
            for (it = 0; c2 > 0 && it < maxit; it++) {
                if (rint_(10) < 2) move_add(&c2);
                else move_rewire(T, &c2);
                if ((it & 31) == 0 && now() >= budget) break;
            }
            if (c2 != 0) restore();
        }
    }

    {
        int m = 0, vv, kk;
        for (vv = 0; vv < N; vv++)
            for (kk = 0; kk < dg[vv]; kk++)
                if (vv < adjv[vv * DEG + kk]) m++;
        printf("%d %d\n", N, m);
        for (vv = 0; vv < N; vv++)
            for (kk = 0; kk < dg[vv]; kk++) {
                int w = adjv[vv * DEG + kk];
                if (vv < w) printf("%d %d\n", vv, w);
            }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, s, nbr, S, rng, deadline, iters):
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build: best algebraic start, then the C grow-and-repair search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    if D >= 3 and d >= 3:
        rng = random.Random(seed * 7919 + d)
        arc_deadline = t0 + 0.2 * time_limit
        try:
            cands = _arc_extensions(d, arc_deadline, rng)
        except Exception:
            cands = []
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            if n_c > best[0]:
                consider((n_c, e_c))

    if D >= 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # C engine: grow and repair from the best start found so far.
    moore = lib.moore_bound(d, D)
    elapsed = time.monotonic() - t0
    remaining = 0.80 * time_limit - elapsed - 2.0
    if d >= 3 and D >= 3 and best[0] < moore and remaining >= 3.0:
        try:
            timeout = max(1.0, min(remaining + 3.0, 0.92 * time_limit - elapsed - 1.0))
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            stdin_graph=best, timeout=timeout)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
