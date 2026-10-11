import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: grows a valid graph by adding one A-vertex and one B-vertex
# at a time, then anneals over degree-preserving moves to restore diameter D.
#
# Moves: rewire an edge endpoint onto a spare vertex, 2-switch between edges,
# or add an edge between spare vertices. Cost = number of ordered-by-vertex
# pairs not within distance D, computed with bitsets. Snapshots of every valid
# state are kept, and the best (largest valid) graph is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

typedef uint64_t u64;

static int DEG, DIAM, NMAX, W, n, E;
static int *dg, *nbl, *sd, *tA, *tB, *su, *sv;
static unsigned char *adj;
static u64 *B1, *PA, *PB;
static int snap_n, snap_m;
static uint64_t rs = 88172645463325252ULL;

#define ADJ(u, v) adj[(size_t)(u) * NMAX + (v)]

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double runif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    nbl[u * DEG + dg[u]++] = v;
    nbl[v * DEG + dg[v]++] = u;
    ADJ(u, v) = 1;
    ADJ(v, u) = 1;
    E++;
}

static void rm_one(int u, int v) {
    int *L = nbl + u * DEG;
    for (int k = 0; k < dg[u]; k++) {
        if (L[k] == v) { L[k] = L[dg[u] - 1]; dg[u]--; return; }
    }
}

static void del_edge(int u, int v) {
    rm_one(u, v);
    rm_one(v, u);
    ADJ(u, v) = 0;
    ADJ(v, u) = 0;
    E--;
}

/* Number of (vertex, vertex) ordered pairs not within distance DIAM. Zero means valid. */
static long eval_cost(void) {
    int v, k, u, t, step;
    for (v = 0; v < n; v++) {
        u64 *r = B1 + (size_t)v * W;
        memset(r, 0, sizeof(u64) * W);
        r[v >> 6] |= 1ULL << (v & 63);
        for (k = 0; k < dg[v]; k++) {
            u = nbl[v * DEG + k];
            r[u >> 6] |= 1ULL << (u & 63);
        }
    }
    u64 *cur = PA, *nxt = PB;
    memcpy(cur, B1, sizeof(u64) * (size_t)n * W);
    for (step = 2; step <= DIAM; step++) {
        for (v = 0; v < n; v++) {
            u64 *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(u64) * W);
            for (k = 0; k < dg[v]; k++) {
                u = nbl[v * DEG + k];
                const u64 *s = cur + (size_t)u * W;
                for (t = 0; t < W; t++) o[t] |= s[t];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long total = 0;
    for (v = 0; v < n; v++) {
        int c = 0;
        const u64 *r = cur + (size_t)v * W;
        for (t = 0; t < W; t++) c += pc64(r[t]);
        total += n - c;
    }
    return total;
}

static void shuffle(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static int pick_nonisolated(void) {
    for (int t = 0; t < 64; t++) {
        int v = rint_(n);
        if (dg[v] > 0) return v;
    }
    return -1;
}

static int pick_spare_side(int s, int avoid) {
    for (int t = 0; t < 60; t++) {
        int v = rint_(n);
        if (sd[v] == s && dg[v] < DEG && v != avoid) return v;
    }
    return -1;
}

/* Greedily add edges between spare vertices on opposite sides. Never raises the cost. */
static void fill_all(void) {
    int na = 0, nbb = 0;
    for (int v = 0; v < n; v++) {
        if (dg[v] < DEG) {
            if (sd[v] == 0) tA[na++] = v;
            else tB[nbb++] = v;
        }
    }
    shuffle(tA, na);
    shuffle(tB, nbb);
    for (int i = 0; i < na; i++) {
        int a = tA[i];
        for (int j = 0; j < nbb && dg[a] < DEG; j++) {
            int b = tB[j];
            if (dg[b] < DEG && !ADJ(a, b)) add_edge(a, b);
        }
    }
}

static void take_snapshot(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int k = 0; k < dg[u]; k++) {
            int v = nbl[u * DEG + k];
            if (u < v) { su[m] = u; sv[m] = v; m++; }
        }
    }
    snap_m = m;
    snap_n = n;
}

static void restore_snapshot(void) {
    memset(dg, 0, sizeof(int) * NMAX);
    memset(adj, 0, (size_t)NMAX * NMAX);
    E = 0;
    n = snap_n;
    for (int i = 0; i < snap_m; i++) add_edge(su[i], sv[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed time\n"); return 1; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tl = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (m0 + 1));
    int *ev = malloc(sizeof(int) * (m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    int bad = 0;
    int *dd = calloc(n0, sizeof(int));
    for (int i = 0; i < m0; i++) {
        if (eu[i] < 0 || eu[i] >= n0 || ev[i] < 0 || ev[i] >= n0 || eu[i] == ev[i]) bad = 1;
        else { dd[eu[i]]++; dd[ev[i]]++; }
    }
    for (int v = 0; v < n0; v++) if (dd[v] > DEG) bad = 1;

    int *off = malloc(sizeof(int) * (n0 + 1));
    int *pos = malloc(sizeof(int) * n0);
    int *to = malloc(sizeof(int) * (2 * m0 + 1));
    int *col = malloc(sizeof(int) * n0);
    int *qu = malloc(sizeof(int) * n0);
    off[0] = 0;
    for (int v = 0; v < n0; v++) { off[v + 1] = off[v] + dd[v]; pos[v] = off[v]; col[v] = -1; }
    if (!bad) {
        for (int i = 0; i < m0; i++) {
            to[pos[eu[i]]++] = ev[i];
            to[pos[ev[i]]++] = eu[i];
        }
        for (int s = 0; s < n0; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int head = 0, tail = 0;
            qu[tail++] = s;
            while (head < tail) {
                int u = qu[head++];
                for (int k = off[u]; k < off[u + 1]; k++) {
                    int w = to[k];
                    if (col[w] < 0) { col[w] = 1 - col[u]; qu[tail++] = w; }
                    else if (col[w] == col[u]) bad = 1;
                }
            }
        }
    }
    if (bad) {
        printf("%d %d\n", n0, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    int maxadd = (1100 - n0) / 2;
    if (maxadd < 1) maxadd = 0;
    NMAX = n0 + 2 * maxadd + 2;
    W = (NMAX + 63) / 64;
    dg = calloc(NMAX, sizeof(int));
    nbl = malloc(sizeof(int) * (size_t)NMAX * DEG);
    sd = calloc(NMAX, sizeof(int));
    tA = malloc(sizeof(int) * NMAX);
    tB = malloc(sizeof(int) * NMAX);
    su = malloc(sizeof(int) * (size_t)NMAX * DEG);
    sv = malloc(sizeof(int) * (size_t)NMAX * DEG);
    adj = calloc((size_t)NMAX * NMAX, 1);
    B1 = malloc(sizeof(u64) * (size_t)NMAX * W);
    PA = malloc(sizeof(u64) * (size_t)NMAX * W);
    PB = malloc(sizeof(u64) * (size_t)NMAX * W);

    for (int v = 0; v < n0; v++) sd[v] = col[v];
    n = n0;
    E = 0;
    for (int i = 0; i < m0; i++) add_edge(eu[i], ev[i]);
    if (eval_cost() != 0) {
        printf("%d %d\n", n0, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    take_snapshot();
    const int ITERS = 8000;

    while (now_s() < tl && snap_n + 2 <= NMAX) {
        restore_snapshot();
        sd[n] = 0;
        sd[n + 1] = 1;
        n += 2;
        fill_all();
        long cost = eval_cost();

        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 127) == 0 && now_s() > tl) break;
            double T = 0.05 + 1.0 * (1.0 - (double)it / ITERS);
            double r = runif();

            if (r < 0.1) {
                /* add an edge between spare vertices on opposite sides; never raises cost */
                int a = pick_spare_side(0, -1);
                int b = pick_spare_side(1, -1);
                if (a < 0 || b < 0 || ADJ(a, b)) continue;
                add_edge(a, b);
                cost = eval_cost();
                continue;
            }

            if (r < 0.5) {
                /* rewire: move edge (x,y) to (x,z) where z is spare on y's side */
                int x = pick_nonisolated();
                if (x < 0) continue;
                int y = nbl[x * DEG + rint_(dg[x])];
                int z = pick_spare_side(sd[y], y);
                if (z < 0 || ADJ(x, z)) continue;
                del_edge(x, y);
                add_edge(x, z);
                long c2 = eval_cost();
                if (c2 <= cost || runif() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    del_edge(x, z);
                    add_edge(x, y);
                }
                continue;
            }

            /* 2-switch: (a,b),(c,d) -> (a,d),(c,b), keeps all degrees and bipartiteness */
            int x1 = pick_nonisolated();
            if (x1 < 0) continue;
            int y1 = nbl[x1 * DEG + rint_(dg[x1])];
            int x2 = pick_nonisolated();
            if (x2 < 0) continue;
            int y2 = nbl[x2 * DEG + rint_(dg[x2])];
            int a, b, c, d;
            if (sd[x1] == 0) { a = x1; b = y1; } else { a = y1; b = x1; }
            if (sd[x2] == 0) { c = x2; d = y2; } else { c = y2; d = x2; }
            if (a == c || b == d || ADJ(a, d) || ADJ(c, b)) continue;
            del_edge(a, b);
            del_edge(c, d);
            add_edge(a, d);
            add_edge(c, b);
            long c2 = eval_cost();
            if (c2 <= cost || runif() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                del_edge(a, d);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, d);
            }
        }

        if (cost == 0) take_snapshot();
    }

    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++) printf("%d %d\n", su[i], sv[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective planes and annealed voltage
# lifts. These give the starting graph for the C growth search.
# ----------------------------------------------------------------------------

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


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets so every target is hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
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
    out = []
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
        SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


_BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Stage 1: construction (short). Arc-extended PG(2,q) for D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.12 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Voltage lift annealing, a second start source.
    build_deadline = t0 + 0.22 * time_limit
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < build_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, build_deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Stage 2: C growth search from the best valid graph found so far.
    # Its budget leaves a margin for compilation and output.
    remaining = t0 + 0.85 * time_limit - time.monotonic() - 2.0
    if D >= 2 and best_n >= 2 and remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.0, 2)],
                             stdin_graph=best, timeout=remaining)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
