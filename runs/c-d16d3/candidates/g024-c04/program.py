import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over bi-Cayley voltage lifts.
#
# A lift has K base vertices per side (A_i, B_j), a group G = Z_M x| Z_K2 with
# element code a*K2+b, and DG layers. Layer L joins A_i to B_{P[L][i]} with
# voltage S[L]: (i,g) ~ (P[L][i], g*s). Every vertex then has degree DG, and
# G acts regularly on each class, so checking one representative per class
# suffices. The cost counts (representative, vertex) pairs at distance > DP.
# The engine starts from the stdin graph and only prints a larger valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 8192
#define MAXD 64
#define MAXK 4
#define MAXE 262144
#define BIG 1000000L

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double ru(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}
static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int M = 1, K2 = 1, G = 1, K = 1, DG, DP;
static int pw[64];
static int P[MAXD][MAXK];
static int S[MAXD];
static int NV;
static int adjv[MAXN][MAXD];
static int degc[MAXN];
static int vis[MAXN], qu[MAXN];
static int stamp = 0;
static int bestN = 0, bestM = 0;
static int bestEU[MAXE], bestEV[MAXE];
static double deadline;

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M) * K2 + (b + e) % K2;
}

static void build(void) {
    NV = 2 * K * G;
    for (int v = 0; v < NV; v++) degc[v] = 0;
    for (int L = 0; L < DG; L++)
        for (int i = 0; i < K; i++) {
            int j = P[L][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, S[L]);
                adjv[a][degc[a]++] = b;
                adjv[b][degc[b]++] = a;
            }
        }
}

static long cost_fn(void) {
    for (int i = 0; i < K; i++)
        for (int L1 = 0; L1 < DG; L1++)
            for (int L2 = L1 + 1; L2 < DG; L2++)
                if (P[L1][i] == P[L2][i] && S[L1] == S[L2]) return BIG;
    build();
    long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        int head = 0, tail = 0;
        qu[tail++] = src;
        vis[src] = stamp;
        for (int dep = 0; dep < DP; dep++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < degc[u]; t++) {
                    int v = adjv[u][t];
                    if (vis[v] != stamp) { vis[v] = stamp; qu[tail++] = v; }
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

static void store(void) {
    int m = 0;
    for (int a = 0; a < K * G; a++)
        for (int t = 0; t < degc[a]; t++) {
            bestEU[m] = a;
            bestEV[m] = adjv[a][t];
            m++;
        }
    bestN = NV;
    bestM = m;
}

static int anneal(int iters) {
    long cur = cost_fn();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now() > deadline) return 0;
        double T = 2.0 * pow(0.025, (double)it / (double)iters);
        if (K > 1 && ru() < 0.4) {
            int L = rint_(DG), i1 = rint_(K), i2 = rint_(K);
            if (i1 == i2) continue;
            int t = P[L][i1]; P[L][i1] = P[L][i2]; P[L][i2] = t;
            long nc = cost_fn();
            if (nc <= cur || ru() < exp((double)(cur - nc) / T)) cur = nc;
            else { t = P[L][i1]; P[L][i1] = P[L][i2]; P[L][i2] = t; }
        } else {
            int L = rint_(DG), old = S[L], nv = rint_(G);
            if (nv == old) continue;
            S[L] = nv;
            long nc = cost_fn();
            if (nc <= cur || ru() < exp((double)(cur - nc) / T)) cur = nc;
            else S[L] = old;
        }
    }
    if (cur != 0) return 0;
    build();
    return 1;
}

static void emit(void) {
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEU[i], bestEV[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DG = atoi(argv[1]);
    DP = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    deadline = now() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) == 2 && n > 0 && m > 0 && m <= MAXE) {
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { m = 0; break; }
            bestEU[i] = u;
            bestEV[i] = v;
        }
        if (m > 0) { bestN = n; bestM = m; }
    }

    if (DG < 3 || DG > MAXD - 1 || DP < 2) { emit(); return 0; }

    long mb = 0, pwr = 1;
    for (int i = 0; i < DP; i++) {
        mb += pwr;
        pwr *= (DG - 1);
        if (pwr > 1000000) break;
    }
    mb *= 2;
    long cap = mb < MAXN ? mb : MAXN;

    static const int Kc[6] = {1, 1, 2, 2, 3, 4};
    while (now() < deadline && bestN < cap) {
        K = Kc[rint_(6)];
        int minG = bestN / (2 * K) + 1;
        if (2L * K * minG > cap) {
            K = 1;
            minG = bestN / 2 + 1;
            if (2L * minG > cap) break;
        }
        G = minG + rint_(3);
        if (2L * K * G > cap) G = minG;

        K2 = 1 + rint_(12);
        if (G % K2 != 0 || G / K2 < 2) K2 = 1;
        if (K2 > 1) {
            M = G / K2;
            int found = 0;
            for (int t = 0; t < 300 && !found; t++) {
                int r = 1 + rint_(M - 1);
                if (gcd_(r, M) != 1) continue;
                long p = 1 % M;
                for (int e = 0; e < K2; e++) p = (p * r) % M;
                if (p == 1 % M) {
                    found = 1;
                    pw[0] = 1 % M;
                    for (int b = 1; b < K2; b++) pw[b] = (pw[b - 1] * r) % M;
                }
            }
            if (!found) { K2 = 1; }
        }
        if (K2 == 1) { M = G; pw[0] = 1 % M; }

        for (int L = 0; L < DG; L++) {
            for (int i = 0; i < K; i++) P[L][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = P[L][i]; P[L][i] = P[L][j]; P[L][j] = t;
            }
            S[L] = rint_(G);
        }

        if (anneal(40000)) {
            int nn = 2 * K * G;
            if (nn > bestN && (long)K * G * DG <= MAXE) store();
        }
    }
    emit();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
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


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Greedy vertex insertion with ball-cover certificates.
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
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


def _ball_masks(n, adj, R):
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


# ----------------------------------------------------------------------------
# Driver: Python builds the safe starting graph, C searches for larger lifts.
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
            best, best_n = (n, e), n

    if D >= 3:
        arcs = _arc_extensions(d, t0 + 0.12 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            consider(*_augment(n_a, e_a, d, D, rng, t0 + 0.25 * time_limit))

    # C annealing for group voltage lifts, seeded with the best graph so far.
    end_c = t0 + 0.92 * time_limit
    budget = end_c - time.monotonic() - 2.0
    if budget >= 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], stdin_graph=best,
                            timeout=max(1.0, end_c - time.monotonic()))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
