"""Bold variant: a bipartite Cayley-Haar search in C replaces the voltage-lift search.

Construction: for a group G of order n/2 (cyclic or Z_m x| Z_k) and a connection set
S of size d containing the identity, the bipartite graph on A = G and B = G has edges
a_x ~ b_{x s} for s in S. Left translations are automorphisms, so the diameter is decided
by two BFS runs (from a_e and b_e). C hill-climbs S to minimise the number of pairs
farther than D apart, then grows G one step at a time. Python builds the Gen. Quadrangle
W(q) (or PG(2,q)) start, grows it, and keeps the largest graph that passes lib.is_valid.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite Cayley-Haar search.
 * usage: prog d D seed time_limit Gstart
 * Vertices: a_x = x, b_y = G + y, x,y in Z-group of order G.
 * Edge a_x -- b_{x*s} for s in S (|S| = d, identity in S).
 * Cost = (#vertices not within D of a_e) + (#vertices not within D of b_e).
 * Zero cost <=> diameter <= D (by left-translation transitivity on each side).
 * Output: "n m" and edges, or "0 0" if nothing was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define GMAX 1200
#define DMAX 32

static int d, D;
static int G;          /* order of the currently built group */
static int TG;         /* target group order */
static double t_end;
static int MT[GMAX * GMAX];
static int INV[GMAX];
static int RP[GMAX];
static int S[DMAX];
static int distv[2 * GMAX], stampv[2 * GMAX], queue_[2 * GMAX];
static int stamp = 0;
static int divs[GMAX], ndiv = 0;

static int bG = 0, bm = 0, bk = 0, br = 0;
static int bS[DMAX];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect group Z_m x| Z_k, element x = a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static void build_group(int m, int k, int r) {
    G = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            MT[x * G + y] = (int)(((a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
}

static void make_divs(int n) {
    ndiv = 0;
    for (int k = 1; k <= n; k++)
        if (n % k == 0) divs[ndiv++] = k;
}

/* Number of vertices within distance D of src. */
static int reach_count(int src) {
    stamp++;
    int head = 0, tail = 0, cnt = 0;
    queue_[tail++] = src;
    stampv[src] = stamp;
    distv[src] = 0;
    while (head < tail) {
        int v = queue_[head++];
        cnt++;
        int dv = distv[v];
        if (dv >= D) continue;
        if (v < G) {
            for (int j = 0; j < d; j++) {
                int u = G + MT[v * G + S[j]];
                if (stampv[u] != stamp) {
                    stampv[u] = stamp;
                    distv[u] = dv + 1;
                    queue_[tail++] = u;
                }
            }
        } else {
            int y = v - G;
            for (int j = 0; j < d; j++) {
                int u = MT[y * G + INV[S[j]]];
                if (stampv[u] != stamp) {
                    stampv[u] = stamp;
                    distv[u] = dv + 1;
                    queue_[tail++] = u;
                }
            }
        }
    }
    return cnt;
}

static int cost(void) {
    return (2 * G - reach_count(0)) + (2 * G - reach_count(G));
}

static void sample_group(void) {
    int k = divs[rndint(ndiv)];
    int m = TG / k;
    int r = 1;
    if (m == 1) {
        r = 0;
    } else if (k > 1) {
        for (int t = 0; t < 300; t++) {
            int c = 1 + rndint(m - 1);
            if (gcd(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = c; break; }
        }
    }
    build_group(m, k, r);
    bm = m; bk = k; br = r;
}

/* Hill-climb S; returns 1 on zero cost. */
static int attempt(int iters, double deadline) {
    S[0] = 0;
    for (int j = 1; j < d; j++) {
        for (;;) {
            int t = rndint(G), dup = 0;
            for (int q = 0; q < j; q++) if (S[q] == t) { dup = 1; break; }
            if (!dup) { S[j] = t; break; }
        }
    }
    int cur = cost();
    for (int it = 0; it < iters; it++) {
        if (cur == 0) return 1;
        if ((it & 255) == 0 && now() > deadline) return 0;
        int i = 1 + rndint(d - 1);
        int t;
        for (;;) {
            t = rndint(G);
            int dup = 0;
            for (int q = 0; q < d; q++) if (S[q] == t) { dup = 1; break; }
            if (!dup) break;
        }
        int old = S[i];
        S[i] = t;
        int nc = cost();
        double T = 0.5 * (1.0 - (double)it / iters) + 0.03;
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
        else S[i] = old;
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit Gstart\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int Gstart = atoi(argv[5]);
    if (d < 2 || D < 2 || d > DMAX) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Per-side Moore bound for bipartite diameter D: sum_{i<D} (d-1)^i. */
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > GMAX) break;
    }
    int Gmax = s < GMAX ? (int)s : GMAX;

    TG = Gstart > d ? Gstart : d;
    while (TG <= Gmax && now() < t_end) {
        double remain = t_end - now();
        double deadline = now() + (remain * 0.35 > 1.0 ? remain * 0.35 : 1.0);
        if (deadline > t_end) deadline = t_end;
        make_divs(TG);
        int ok = 0;
        while (!ok && now() < deadline) {
            sample_group();
            if (attempt(6000, deadline)) {
                ok = 1;
                bG = G;
                memcpy(bS, S, sizeof(S));
            }
        }
        if (!ok) break;
        TG++;
    }

    if (bG == 0) { printf("0 0\n"); return 0; }
    build_group(bm, bk, br);
    memcpy(S, bS, sizeof(S));
    printf("%d %d\n", 2 * G, G * d);
    for (int x = 0; x < G; x++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", x, G + MT[x * G + S[j]]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective plane and generalized quadrangle starts.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q + 1, diameter 4."""
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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (grows a valid start).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Algebraic starts, grown by the cover heuristic while there is spare degree.
    try:
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                n2, e2 = _grow(gq[0], gq[1], d, D, t0 + 0.30 * time_limit, rng)
                consider(n2, e2)
        elif D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, t0 + 0.25 * time_limit, rng)
                consider(n2, e2)
    except Exception:
        pass

    # Bipartite Cayley-Haar search in C, starting just below the current best size.
    elapsed = time.monotonic() - t0
    budget = 0.86 * time_limit - elapsed - 2.0
    if d >= 2 and D >= 2 and budget > 3.0 and best[0] < lib.moore_bound(d, D):
        gstart = max(d, best[0] // 2 + 1)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), gstart],
                             stdin_graph=None, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
