import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine. Two modes, selected by a fifth argument:
#
#  * default (4 args): simulated annealing on a bipartite graph with a fixed
#    vertex set. Cost = number of unordered pairs at distance > D. Whenever the
#    cost reaches 0 the engine saves the graph and appends an isolated vertex.
#
#  * "arc" mode (5 args, stdin = incidence graph of PG(2,q), points 0..m-1,
#    lines m..2m-1): NEW routine. It searches for a large arc-like set S of
#    point indices with loads <= s = d - maxdeg, where
#        (points of S on each line) <= s   and   (lines indexed by S through
#        each point) <= s.
#    The search is penalty simulated annealing on  -|S| + W * excess, with
#    toggle moves on single indices. It then prints the augmented graph
#    (A vertex per S point, B vertex per S index) directly.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXW 25
#define DCAP 64
#define MAXE (MAXN * DCAP)
#define MAXM 600

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0;
static uint64_t rs = 1;
static int vis[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

static int bad_pairs(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (nb[u][i] > u && m < MAXE) {
                bestU[m] = u; bestV[m] = nb[u][i]; m++;
            }
        }
    }
    best_n = n; best_m = m;
}

static int color_graph(void) {
    static int queue[MAXN];
    int iso = 0;
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        if (deg[s] == 0) { vis[s] = 1; side[s] = (iso++) & 1; continue; }
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; queue[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

/* a -- b  becomes  a -- w, where w is on the same side as b. */
static int move_rewire(int *ua, int *ub, int *uw) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    int w = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != b && side[c] == side[b] && deg[c] < d && !adjm[a][c]) { w = c; break; }
    }
    if (w < 0) return 0;
    del_edge(a, b);
    add_edge(a, w);
    *ua = a; *ub = b; *uw = w;
    return 1;
}

static int move_add(int *ua, int *ub) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (deg[c] < d) { x = c; break; }
    }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *ua = x; *ub = y;
    return 1;
}

static int move_remove(int *ua, int *ub) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    *ua = a; *ub = b;
    return 1;
}

/* ---------------- arc search on PG(2,q) incidence graph (NEW) ---------------- */

static int am_, as_, exc_, ssz_;
static int lo_[MAXM][DCAP], lo_n[MAXM];   /* lines through point i */
static int po_[MAXM][DCAP], po_n[MAXM];   /* points on line j */
static int inS_[MAXM], rc_[MAXM], cc_[MAXM], bestS_[MAXM], Sarr_[MAXM];

/* Adding index X: each point Q on line X gets rc[Q]++, each line L through point X gets cc[L]++. */
static void arc_add(int X) {
    inS_[X] = 1; ssz_++;
    for (int k = 0; k < po_n[X]; k++) { int Q = po_[X][k]; if (rc_[Q] >= as_) exc_++; rc_[Q]++; }
    for (int k = 0; k < lo_n[X]; k++) { int L = lo_[X][k]; if (cc_[L] >= as_) exc_++; cc_[L]++; }
}
static void arc_del(int X) {
    inS_[X] = 0; ssz_--;
    for (int k = 0; k < po_n[X]; k++) { int Q = po_[X][k]; rc_[Q]--; if (rc_[Q] >= as_) exc_--; }
    for (int k = 0; k < lo_n[X]; k++) { int L = lo_[X][k]; cc_[L]--; if (cc_[L] >= as_) exc_--; }
}
/* Change in excess when adding X (non-negative). */
static int arc_pen_add(int X) {
    int c = 0;
    for (int k = 0; k < po_n[X]; k++) if (rc_[po_[X][k]] >= as_) c++;
    for (int k = 0; k < lo_n[X]; k++) if (cc_[lo_[X][k]] >= as_) c++;
    return c;
}
/* Change in excess when removing X (non-positive). */
static int arc_pen_del(int X) {
    int c = 0;
    for (int k = 0; k < po_n[X]; k++) if (rc_[po_[X][k]] > as_) c++;
    for (int k = 0; k < lo_n[X]; k++) if (cc_[lo_[X][k]] > as_) c++;
    return -c;
}

static void arc_run(int *iu, int *iv, int ne, int d_, double tl) {
    int m = n / 2;
    if (n % 2 || m < 1 || m > MAXM) { printf("0 0\n"); return; }
    am_ = m;
    for (int i = 0; i < ne; i++) {
        int u = iu[i], v = iv[i], p = -1, l = -1;
        if (u >= 0 && u < m && v >= m && v < 2 * m) { p = u; l = v - m; }
        else if (v >= 0 && v < m && u >= m && u < 2 * m) { p = v; l = u - m; }
        if (p < 0) continue;
        if (lo_n[p] >= DCAP || po_n[l] >= DCAP) continue;
        lo_[p][lo_n[p]++] = l;
        po_[l][po_n[l]++] = p;
    }
    int maxdeg = 0;
    for (int i = 0; i < m; i++) {
        if (lo_n[i] > maxdeg) maxdeg = lo_n[i];
        if (po_n[i] > maxdeg) maxdeg = po_n[i];
    }
    as_ = d_ - maxdeg;
    if (as_ < 1) {
        printf("%d %d\n", n, ne);
        for (int i = 0; i < ne; i++) printf("%d %d\n", iu[i], iv[i]);
        return;
    }

    const double W = 1.5;
    const long CY = 300000;
    long it = 0;
    int bestsz = 0;
    clock_t c0 = clock();
    for (;;) {
        if ((it & 4095) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;
        double T = pow(0.08, (double)(it % CY) / (double)CY);
        int X = rint_(m);
        if (!inS_[X]) {
            int de = arc_pen_add(X);
            double dE = -1.0 + W * (double)de;
            if (dE <= 0.0 || rdbl() < exp(-dE / T)) arc_add(X);
        } else {
            int de = arc_pen_del(X);
            double dE = 1.0 + W * (double)de;
            if (dE <= 0.0 || rdbl() < exp(-dE / T)) arc_del(X);
        }
        if (exc_ == 0 && ssz_ > bestsz) {
            bestsz = ssz_;
            memcpy(bestS_, inS_, sizeof(int) * (size_t)m);
        }
    }

    int k = 0;
    for (int X = 0; X < m; X++) if (bestS_[X]) Sarr_[k++] = X;
    long total = ne;
    for (int t = 0; t < k; t++) total += lo_n[Sarr_[t]] + po_n[Sarr_[t]];
    printf("%d %ld\n", 2 * m + 2 * k, total);
    for (int i = 0; i < ne; i++) printf("%d %d\n", iu[i], iv[i]);
    for (int t = 0; t < k; t++) {
        int P = Sarr_[t], A = 2 * m + t;
        for (int j = 0; j < lo_n[P]; j++) printf("%d %d\n", A, m + lo_[P][j]);
    }
    for (int t = 0; t < k; t++) {
        int X = Sarr_[t], B = 2 * m + k + t;
        for (int j = 0; j < po_n[X]; j++) printf("%d %d\n", po_[X][j], B);
    }
}

/* ------------------------------------------------------------------------ */

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || n < 0 || m0 < 0) { printf("0 0\n"); return 0; }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) return 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { m0 = i; break; }
    }

    int arc = (argc >= 6 && strcmp(argv[5], "arc") == 0);
    if (arc) {
        arc_run(iu, iv, m0, d, tl);
        return 0;
    }

    int ok = (n >= 2 && n <= MAXN - 256 && d >= 1 && d <= DCAP && D >= 1);
    if (ok) {
        for (int i = 0; i < m0 && ok; i++) {
            int u = iu[i], v = iv[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
                deg[u] >= d || deg[v] >= d) {
                ok = 0;
            } else {
                add_edge(u, v);
            }
        }
    }
    if (ok) ok = color_graph();
    if (!ok) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }

    int cur_bad = bad_pairs();
    int have_best = 0;
    if (cur_bad == 0) { save_best(); have_best = 1; }

    long it = 0;
    for (;;) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur_bad == 0) {
            save_best();
            have_best = 1;
            if (n >= MAXN - 2) break;
            side[n] = n & 1;
            deg[n] = 0;
            n++;
            cur_bad = bad_pairs();
            continue;
        }

        double phase = (double)(it % 60000) / 60000.0;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);

        int kind = 0, ua = 0, ub = 0, uw = 0, applied = 0;
        int r = rint_(100);
        if (r < 55) { kind = 0; applied = move_rewire(&ua, &ub, &uw); }
        else if (r < 90) { kind = 1; applied = move_add(&ua, &ub); }
        else { kind = 2; applied = move_remove(&ua, &ub); }
        if (!applied) continue;

        int nbad = bad_pairs();
        int delta = nbad - cur_bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur_bad = nbad;
        } else {
            if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
            else if (kind == 1) { del_edge(ua, ub); }
            else { add_edge(ua, ub); }
        }
    }

    if (!have_best) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane arc candidates (diameter 3).
# The arc search itself runs in C ("arc" mode). Python chooses the plane order.
# ----------------------------------------------------------------------------

def _pg_arc_candidates(d):
    """Prime powers q with q+1 <= d, sorted by the counting bound of the arc-extended graph."""
    scored = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        m = q * q + q + 1
        s = d - q - 1
        bound = 2 * m + 2 * ((m * s) // (q + 1)) if s >= 1 else 2 * m
        scored.append((bound, q))
    scored.sort(reverse=True)
    return [q for _, q in scored]


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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
    """Simulated annealing over voltages and per-layer B-assignments."""
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    if D == 3:
        qs = _pg_arc_candidates(d)[:2]
        # Plain incidence graphs of PG(2,q) are valid for D = 3 whenever q + 1 <= d.
        for q in qs:
            if time.monotonic() > end:
                break
            consider(lib.projective_plane_incidence(q))

        # NEW: C arc search (simulated annealing over the spare-capacity constraints).
        arc_qs = [q for q in qs if d - q - 1 >= 1]
        cb = end - time.monotonic()
        arc_total = 0.55 * cb
        fracs = [0.7, 0.3] if len(arc_qs) > 1 else [1.0]
        for idx, q in enumerate(arc_qs):
            budget = round(fracs[idx] * arc_total, 2)
            if budget < 1.0 or time.monotonic() > end:
                continue
            n2, E = lib.projective_plane_incidence(q)
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed + 101 * idx, budget, "arc"],
                                stdin_graph=(n2, E), timeout=budget + 10)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

        # Annealing growth from the best valid graph. The engine starts valid, so it
        # saves the graph and then keeps appending vertices while it can repair them.
        bound = lib.moore_bound(d, D)
        cbudget = end - time.monotonic()
        if best[0] < bound and cbudget > 3.0:
            try:
                start_graph = (best[0], list(best[1]))
                out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget - 1.5, 2)],
                                stdin_graph=start_graph, timeout=cbudget + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Voltage-lift annealing for D >= 4.
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
