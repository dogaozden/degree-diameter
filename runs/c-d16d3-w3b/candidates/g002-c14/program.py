import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine (one file, three modes):
#   mode 0: simulated annealing on bad-pair count (fixed sides, degree <= d).
#           When the cost reaches 0 it saves the graph and appends an isolated vertex.
#   mode 1: greedy vertex insertion with ball-cover certificates (radius D-1).
#           A new vertex joins a covering set of opposite-side spare-degree vertices.
#   mode 2: insertion (short), then annealing, then the best graph is reloaded
#           and insertion runs again until the budget ends.
# Every state the engine prints is a valid graph (Python re-checks it anyway).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1280
#define MAXW 20
#define DCAP 64
#define MAXE (MAXN * 32)

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RT[MAXN][MAXW];
static int badv[MAXN], nbadv;
static int curbadv[MAXN], ncurbadv;
static int bestU[MAXE], bestV[MAXE];
static int best_n, best_m;
static uint64_t rs = 1;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

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

/* out[v] = bitset of vertices within distance R of v. */
static void balls(int R, uint64_t (*out)[MAXW]) {
    int Wd = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(out[v], 0, sizeof(uint64_t) * (size_t)Wd);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(RT[v], out[v], sizeof(uint64_t) * (size_t)Wd);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = out[nb[v][i]];
                for (int w = 0; w < Wd; w++) RT[v][w] |= s[w];
            }
        }
        for (int v = 0; v < n; v++)
            memcpy(out[v], RT[v], sizeof(uint64_t) * (size_t)Wd);
    }
}

/* Number of unordered pairs at distance > D; fills badv with vertices in bad pairs. */
static int bad_count(void) {
    int Wd = (n + 63) >> 6;
    balls(D, RA);
    long bad = 0;
    nbadv = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < Wd; w++) c += popc(RA[v][w]);
        int miss = n - c;
        bad += miss;
        if (miss > 0) badv[nbadv++] = v;
    }
    return (int)(bad / 2);
}

static void adopt(void) {
    memcpy(curbadv, badv, sizeof(int) * (size_t)nbadv);
    ncurbadv = nbadv;
}

static int color_graph(void) {
    static int vis[MAXN], queue[MAXN];
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

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u && m < MAXE) { bestU[m] = u; bestV[m] = nb[u][i]; m++; }
    best_n = n; best_m = m;
}

static void load_best(void) {
    for (int u = 0; u < n; u++) {
        deg[u] = 0;
        for (int v = 0; v < n; v++) adjm[u][v] = 0;
    }
    n = best_n;
    for (int i = 0; i < best_m; i++) add_edge(bestU[i], bestV[i]);
}

static void out_current(void) {
    int m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u) m++;
    printf("%d %d\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u) printf("%d %d\n", u, nb[u][i]);
}

static void out_best(void) {
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
}

/* ---------------- annealing moves ---------------- */

static int pick_vertex(void) {
    if (ncurbadv > 0 && rdbl() < 0.6) return curbadv[rint_(ncurbadv)];
    return rint_(n);
}

static int move_rewire(int *ua, int *ub, int *uw) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = pick_vertex();
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
        int c = pick_vertex();
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

/* Returns 1 if a valid graph was ever reached (best_* then holds it). */
static int sa_phase(double tl, clock_t t0) {
    int cur = bad_count();
    adopt();
    int have = 0;
    best_n = 0; best_m = 0;
    if (cur == 0) { save_best(); have = 1; }
    long it = 0;
    for (;;) {
        if ((it & 127) == 0 && elapsed(t0) > tl) break;
        it++;
        if (cur == 0) {
            save_best(); have = 1;
            if (n >= MAXN - 2) break;
            side[n] = n & 1;
            deg[n] = 0;
            n++;
            cur = bad_count();
            adopt();
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
        int nbad = bad_count();
        int delta = nbad - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nbad;
            adopt();
        } else {
            if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
            else if (kind == 1) { del_edge(ua, ub); }
            else { add_edge(ua, ub); }
        }
    }
    if (cur == 0) { save_best(); have = 1; }
    return have;
}

/* ---------------- insertion ---------------- */

static int covers_all(const uint64_t *cov, int Wd) {
    for (int w = 0; w < Wd; w++) {
        uint64_t want;
        if (w < Wd - 1) want = ~0ULL;
        else {
            int r = n - 64 * (Wd - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

/* RA must hold radius-(D-1) balls for the current graph. */
static int try_insert(int sd) {
    static int cand[MAXN], used[MAXN];
    int Wd = (n + 63) >> 6;
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (side[u] == 1 - sd && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < nc; i++) used[cand[i]] = 0;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(cov));
    int chosen[DCAP];
    int nch = 0;
    while (nch < d && !covers_all(cov, Wd)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < Wd; w++) g += popc(RA[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < Wd; w++) cov[w] |= RA[best][w];
    }
    if (!covers_all(cov, Wd)) return 0;
    int w = n;
    n++;
    side[w] = sd;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static void ins_phase(double tl, clock_t t0) {
    int R = D - 1;
    int fails = 0;
    while (fails < 400 && n < MAXN - 1) {
        if (elapsed(t0) > tl) break;
        balls(R, RA);
        int first = (int)(rnd64() & 1ULL);
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(first ^ k);
        if (ok) { fails = 0; continue; }
        fails++;
        /* Spare cross edges only shrink distances, so validity is kept. */
        for (int t = 0; t < 50; t++) {
            int u = rint_(n), v = rint_(n);
            if (u == v || side[u] == side[v] || deg[u] >= d || deg[v] >= d || adjm[u][v]) continue;
            add_edge(u, v);
            break;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int mode = (argc > 5) ? atoi(argv[5]) : 2;
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    clock_t t0 = clock();

    int N0 = 0, M0 = 0;
    static int iu[MAXE], iv[MAXE];
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || M0 < 0) { printf("0 0\n"); return 0; }
    if (d < 1 || d > DCAP || D < 2 || N0 > MAXN - 64 || M0 > MAXE) { printf("0 0\n"); return 0; }
    for (int i = 0; i < M0; i++)
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { printf("0 0\n"); return 0; }

    n = N0;
    int ok = 1;
    for (int i = 0; i < M0 && ok; i++) {
        int u = iu[i], v = iv[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] || deg[u] >= d || deg[v] >= d)
            ok = 0;
        else
            add_edge(u, v);
    }
    if (!ok || !color_graph()) { printf("0 0\n"); return 0; }

    if (mode == 0) {
        if (sa_phase(tl, t0)) out_best();
        else printf("0 0\n");
        return 0;
    }
    if (mode == 1) {
        ins_phase(tl, t0);
        out_current();
        return 0;
    }
    /* mode 2: insertion, annealing, then insertion from the best annealed graph. */
    ins_phase(0.12 * tl, t0);
    if (!sa_phase(0.85 * tl, t0)) { printf("0 0\n"); return 0; }
    load_best();
    ins_phase(tl, t0);
    out_current();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare capacity is s = d - q - 1.
#   SA: a set of points; each gets a new vertex joined to its q+1 lines.
#       Each line may contain at most s points of SA.
#   SB: a set of lines; each gets a new vertex joined to its q+1 points.
#       Each point may lie on at most s lines of SB.
# Diameter stays 3 for any SA, SB satisfying these loads.
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
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements keeping every target load <= s."""
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
    """Plateau/improvement search for the load-constrained set problem."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """PG incidence plus one A-vertex per SA point and one B-vertex per SB line."""
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
    """Return a list of (n, edges) for each prime power q with q + 1 <= d."""
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
        if _loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points):
            out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d (small q only, for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Voltage-lift annealing over semidirect groups (used for D >= 4).
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
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
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
# C runner
# ----------------------------------------------------------------------------

def _run_c(mode, graph, d, D, seed, budget):
    """Run the C engine in the given mode on graph; return (n, edges) or None."""
    if graph is None or budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mode],
                        stdin_graph=(graph[0], list(graph[1])), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Build
# Time plan (fractions of the time limit, with a safety margin):
#   0.00-0.25  arc-extended PG graphs (D = 3), or GQ and voltage lifts (D >= 4)
#   0.25-0.95  one C run: insertion, annealing, insertion from the best state
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit - 1.0
    end = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    if D == 2 or best[0] >= lib.moore_bound(d, D):
        return best[0], list(best[1])

    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * total, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0])[:3]:
            consider(g)

    if D >= 4:
        consider(_best_gq(d))
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        anneal_end = start + 0.45 * total
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

    # Single C run: insertion, annealing and final insertion on the best graph.
    if best[0] <= 1200 and best[0] < lib.moore_bound(d, D):
        consider(_run_c(2, best, d, D, seed, end - time.monotonic()))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
