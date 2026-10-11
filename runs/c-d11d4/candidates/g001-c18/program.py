import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of bipartite base graphs
# with d layers of permutations, voltages in semidirect products Z_m x| Z_k2.
# Lift vertices: fiber f (0..2K-1) times group element x, id = f*G + x.
# Left fibers 0..K-1, right fibers K..2K-1. Dart (u -> v, g) joins (u,x) to (v,x*g).
# Left multiplication is an automorphism, so checking one source per fiber is
# enough to certify diameter <= D.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int D, dd, K, G, N;
static int *DU, *DV, *DG, *LL, *RR, *MUL, *INV;
static int *stampv, *queuev, *distv, *nb;
static int curstamp = 0;
static uint64_t rs = 88172645463325252ULL;
static int opt_k2[4096], opt_r[4096];
static int *bestE = NULL;
static int bestN = 0, bestM = 0;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static void alloc_all(void) {
    int nd = K * dd;
    DU = malloc(sizeof(int) * nd);
    DV = malloc(sizeof(int) * nd);
    DG = malloc(sizeof(int) * nd);
    LL = malloc(sizeof(int) * nd);
    RR = malloc(sizeof(int) * nd);
    MUL = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * G);
    stampv = calloc(N, sizeof(int));
    queuev = malloc(sizeof(int) * N);
    distv = malloc(sizeof(int) * N);
    nb = malloc(sizeof(int) * dd);
}

static void free_all(void) {
    free(DU); free(DV); free(DG); free(LL); free(RR);
    free(MUL); free(INV); free(stampv); free(queuev); free(distv); free(nb);
}

/* Enumerate semidirect products Z_m x| Z_k2 of order G (k2 <= 16, m >= 2). */
static int build_opts(int G_) {
    int c = 0;
    for (int k2 = 1; k2 <= 16 && k2 <= G_; k2++) {
        if (G_ % k2) continue;
        int m = G_ / k2;
        if (m < 2) continue;
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            long long p = 1 % m;
            for (int e = 0; e < k2; e++) p = p * r % m;
            if (p == 1 % m && c < 4096) { opt_k2[c] = k2; opt_r[c] = r; c++; }
        }
    }
    return c;
}

static void build_group(int m, int k2, int r) {
    int pw[64];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int ra = (int)((a + (long long)pw[b] * c) % m);
            int rb = (b + e) % k2;
            MUL[x * G + y] = ra * k2 + rb;
        }
    }
    for (int x = 0; x < G; x++) {
        INV[x] = 0;
        for (int y = 0; y < G; y++) if (MUL[x * G + y] == 0) { INV[x] = y; break; }
    }
}

/* Neighbours of vertex v (fiber f = v / G, element x = v % G). Returns count (= dd). */
static int neighbours(int v, int *out) {
    int f = v / G, x = v % G, c = 0;
    if (f < K) {
        for (int t = 0; t < dd; t++) {
            int j = LL[f * dd + t];
            out[c++] = (K + DV[j]) * G + MUL[x * G + DG[j]];
        }
    } else {
        int vv = f - K;
        for (int t = 0; t < dd; t++) {
            int j = RR[vv * dd + t];
            out[c++] = DU[j] * G + MUL[x * G + INV[DG[j]]];
        }
    }
    return c;
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    curstamp++;
    int head = 0, tail = 0;
    queuev[tail++] = src;
    distv[src] = 0;
    stampv[src] = curstamp;
    while (head < tail) {
        int v = queuev[head++];
        int dv = distv[v];
        if (dv >= D) continue;
        int c = neighbours(v, nb);
        for (int i = 0; i < c; i++) {
            int w = nb[i];
            if (stampv[w] != curstamp) {
                stampv[w] = curstamp;
                distv[w] = dv + 1;
                queuev[tail++] = w;
            }
        }
    }
    return tail;
}

static long eval_cost(void) {
    long c = 0;
    for (int f = 0; f < 2 * K; f++) c += N - bfs_reach(f * G);
    return c;
}

/* True if dart j with voltage g would duplicate an edge (same pair, same voltage). */
static int conflict(int j, int g) {
    int u = DU[j], v = DV[j];
    for (int t = 0; t < dd; t++) {
        int k = LL[u * dd + t];
        if (k != j && DV[k] == v && DG[k] == g) return 1;
    }
    return 0;
}

static int init_darts(void) {
    int nd = K * dd;
    for (int j = 0; j < nd; j++) DG[j] = rndint(G);
    for (int iter = 0; iter < 200; iter++) {
        int bad = 0;
        for (int j = 0; j < nd; j++) {
            if (conflict(j, DG[j])) { bad = 1; DG[j] = rndint(G); }
        }
        if (!bad) return 1;
    }
    return 0;
}

static int attempt(double stop_at, double slice) {
    if (!init_darts()) return 0;
    long cur = eval_cost();
    double t0 = now();
    double end = t0 + slice;
    if (end > stop_at) end = stop_at;
    double span = end - t0;
    if (span <= 0) span = 1e-3;
    const double T0 = 3.0, T1 = 0.02;
    double T = T0;
    long it = 0;
    int nd = K * dd;
    while (cur > 0) {
        if ((it & 127) == 0) {
            double t = now();
            if (t >= end) break;
            double f = (t - t0) / span;
            if (f < 0) f = 0;
            if (f > 1) f = 1;
            T = T0 * pow(T1 / T0, f);
        }
        it++;
        int j = rndint(nd);
        int g = rndint(G);
        int old = DG[j];
        if (g == old) continue;
        if (conflict(j, g)) continue;
        DG[j] = g;
        long nc = eval_cost();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nc;
        else DG[j] = old;
    }
    return cur == 0;
}

static int verify(void) {
    for (int v = 0; v < N; v++) if (bfs_reach(v) != N) return 0;
    return 1;
}

static void store_best(void) {
    int M = K * dd * G;
    int *E = malloc(sizeof(int) * 2 * (size_t)M);
    int c = 0;
    for (int u = 0; u < K; u++) {
        for (int t = 0; t < dd; t++) {
            int j = LL[u * dd + t];
            int v = DV[j];
            for (int x = 0; x < G; x++) {
                E[2 * c] = u * G + x;
                E[2 * c + 1] = (K + v) * G + MUL[x * G + DG[j]];
                c++;
            }
        }
    }
    free(bestE);
    bestE = E;
    bestN = N;
    bestM = M;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int tgt = (argc > 5) ? atoi(argv[5]) : 1;
    if (tgt < 1) tgt = 1;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) == 2) {
        for (int i = 0; i < m0; i++) {
            int a, b;
            if (scanf("%d %d", &a, &b) != 2) break;
        }
    }

    double stop = now() + budget;
    int curTgt = tgt;
    while (now() < stop - 0.3) {
        int Kc = 1 + rndint(6);
        int Gmin = (curTgt + 2 * Kc - 1) / (2 * Kc);
        if (Gmin < 2) Gmin = 2;
        int Gc = Gmin + rndint(Gmin / 8 + 3);
        int nopt = build_opts(Gc);
        if (nopt == 0) continue;
        int pick = rndint(nopt);
        K = Kc;
        G = Gc;
        N = 2 * K * G;
        alloc_all();
        build_group(G / opt_k2[pick], opt_k2[pick], opt_r[pick]);

        int *pm = malloc(sizeof(int) * K);
        for (int p = 0; p < dd; p++) {
            for (int i = 0; i < K; i++) pm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int k = rndint(i + 1);
                int t = pm[i]; pm[i] = pm[k]; pm[k] = t;
            }
            for (int i = 0; i < K; i++) {
                int j = p * K + i;
                DU[j] = i;
                DV[j] = pm[i];
                LL[i * dd + p] = j;
                RR[pm[i] * dd + p] = j;
            }
        }
        free(pm);

        double remain = stop - now();
        double slice = remain * 0.12;
        if (slice < 1.0) slice = 1.0;
        if (attempt(stop, slice) && N > bestN && verify()) {
            store_best();
            curTgt = N + 1;
        }
        free_all();
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions and fallbacks.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedy set cover of `full` by at most d candidate vertices. Returns the list or None."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the set."""
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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
    """Extend by cover vertices first, then saturate edges with the remaining spare degree."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D >= 3: projective plane of the largest prime power q with q + 1 <= d, grown.
    if D >= 3:
        qs = [q for q in range(2, d) if lib.is_prime_power(q)]
        if qs:
            pn, pe = lib.projective_plane_incidence(qs[-1])
            consider(pn, pe)
            n2, e2 = _grow(pn, pe, d, D, start + 0.1 * time_limit, rng)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), grown. This is the strong baseline.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.3 * time_limit, rng)
            consider(n2, e2)

    # Bold search: C annealing over group voltage lifts, aimed above the current best.
    budget = end - time.monotonic() - 1.0
    if budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n + 1],
                            stdin_graph=None, timeout=time_limit * 0.92)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
