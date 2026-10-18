"""Bi-Cayley search over nonabelian groups with fast two-source evaluation.

Construction change: instead of multi-base voltage lifts with bitset reachability, the
engine builds a vertex-transitive-per-side bipartite graph. Vertices are A_g and B_g for g in a
group G = Z_m x| Z_k (order G), and A_g ~ B_{g s} for d distinct generators s in S. Left
multiplication is an automorphism, so the diameter is at most D iff BFS from A_e and from B_e
reaches every vertex within D steps. Each evaluation is then two bounded BFS runs over 2|G|
vertices, with no bitsets, and the search can sweep much larger orders.

The C engine searches for groups of order just above the current best (order > best_n / 2)
with successive halving over random candidate groups and generator sets, then keeps raising
the order bar after each success. Python keeps the algebraic baselines (PG(2,q), W(q)) and
K_{d,d} as safe fallbacks, validates every graph with lib.is_valid, and adds slack vertices when
spare degree exists.
"""
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

#define MAXD 64
#define POOLN 8

typedef uint64_t u64;

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * n); return v >= n ? n - 1 : v; }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int DEG, DIAM;
static int GM, GK, G;          /* group Z_GM x| Z_GK, order G = GM*GK */
static long long GR;
static int PW[64];
static int S[MAXD], SI[MAXD];  /* generators and their inverses */
static int *RT = NULL, *RIT = NULL, *stamp = NULL, *queue = NULL;
static int curstamp = 0;
static int capG = 0;

static void ensure_cap(void) {
    if (G <= capG) return;
    capG = G + G / 4 + 16;
    free(RT); free(RIT); free(stamp); free(queue);
    RT = malloc(sizeof(int) * (size_t)DEG * (size_t)capG);
    RIT = malloc(sizeof(int) * (size_t)DEG * (size_t)capG);
    stamp = calloc((size_t)2 * (size_t)capG, sizeof(int));
    queue = malloc(sizeof(int) * (size_t)2 * (size_t)capG);
    curstamp = 0;
    if (!RT || !RIT || !stamp || !queue) { printf("0 0\n"); exit(0); }
}

static void set_group(int m, int k2, long long r) {
    GM = m; GK = k2; G = m * k2; GR = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        PW[b] = (int)p;
        p = p * r % m;
    }
    ensure_cap();
}

/* (a,b)(c,e) = (a + r^b c, b + e), element coded as a*GK + b */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long long t = ((long long)a + (long long)PW[b] * c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

/* inverse of (a,b) is (-r^(-b) a, -b) */
static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long long t = ((long long)PW[nb] * a) % GM;
    long long na = (GM - t) % GM;
    return (int)(na * GK + nb);
}

/* Refresh right-multiplication tables for generator j. */
static void set_gen(int j) {
    int s = S[j];
    SI[j] = ginv(s);
    int *rt = RT + (size_t)j * (size_t)G;
    int *rit = RIT + (size_t)j * (size_t)G;
    for (int g = 0; g < G; g++) {
        rt[g] = gmul(g, s);
        rit[g] = gmul(g, SI[j]);
    }
}

/* Vertices: A_g = g (0..G-1), B_h = G + h. A_g ~ B_{g s_j}; B_h ~ A_{h s_j^{-1}}.
   Returns the number of vertices NOT within DIAM of the source. */
static int bfs_unreached(int src) {
    curstamp++;
    int head = 0, tail = 0;
    queue[tail++] = src;
    stamp[src] = curstamp;
    for (int lev = 0; lev < DIAM && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int v = queue[head++];
            if (v < G) {
                for (int j = 0; j < DEG; j++) {
                    int w = G + RT[(size_t)j * (size_t)G + v];
                    if (stamp[w] != curstamp) { stamp[w] = curstamp; queue[tail++] = w; }
                }
            } else {
                int h = v - G;
                for (int j = 0; j < DEG; j++) {
                    int w = RIT[(size_t)j * (size_t)G + h];
                    if (stamp[w] != curstamp) { stamp[w] = curstamp; queue[tail++] = w; }
                }
            }
        }
    }
    return 2 * G - tail;
}

/* Left translations are automorphisms, so these two sources cover all pairs. */
static int eval_cost(void) {
    return bfs_unreached(0) + bfs_unreached(G);
}

static int in_S(int x, int upto) {
    for (int j = 0; j < upto; j++) if (S[j] == x) return 1;
    return 0;
}

static void rand_gens(void) {
    for (int j = 0; j < DEG; j++) {
        int x;
        do { x = rndint(G); } while (in_S(x, j));
        S[j] = x;
        set_gen(j);
    }
}

/* Simulated annealing over the generator set. Returns the best cost; S ends at the best state. */
static int anneal(long steps, double deadline) {
    int cost = eval_cost();
    int best = cost;
    int bestS[MAXD];
    memcpy(bestS, S, sizeof(int) * DEG);
    double T0 = 1.0 + 0.05 * (double)cost;
    for (long t = 0; t < steps && cost > 0; t++) {
        if ((t & 127) == 0 && now() > deadline) break;
        double temp = T0 * (1.0 - (double)t / (double)steps);
        if (temp < 0.3) temp = 0.3;
        int j = rndint(DEG);
        int old = S[j];
        int nw;
        do { nw = rndint(G); } while (in_S(nw, DEG));
        S[j] = nw;
        set_gen(j);
        int c2 = eval_cost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                memcpy(bestS, S, sizeof(int) * DEG);
            }
        } else {
            S[j] = old;
            set_gen(j);
        }
    }
    memcpy(S, bestS, sizeof(int) * DEG);
    for (int j = 0; j < DEG; j++) set_gen(j);
    return best;
}

/* Random semidirect product Z_m x| Z_k2 of order Gt; r = 1 gives a direct product. */
static int sample_group(int Gt, int *pm, int *pk2, long long *pr) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = 1 + rndint(12);
        if (rndu() < 0.3) k2 = 1 + rndint(40);
        if (Gt % k2) continue;
        int m = Gt / k2;
        if (m < 2) continue;
        long long r = 1;
        if (k2 >= 2 && m >= 3) {
            for (int t = 0; t < 200; t++) {
                long long c = 2 + rndint(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        *pm = m; *pk2 = k2; *pr = r;
        return 1;
    }
    return 0;
}

typedef struct {
    int m, k2, G;
    long long r;
    int S[MAXD];
    int cost;
} Cand;

static Cand pool[POOLN];

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long minN = argc > 5 ? atol(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    DIAM = D;
    rs = 0x9E3779B97F4A7C15ULL ^ ((u64)seed * 2654435761ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    double deadline = now() + tl;
    long minG = minN / 2 + 1;           /* need 2G > minN */
    if (minG < DEG + 1) minG = DEG + 1;

    int have = 0;
    int bestGM = 0, bestGK = 0, bestG = 0;
    long long bestGR = 1;
    int bestS[MAXD];

    while (now() < deadline) {
        long window = 1 + minG / 30;
        int np = 0;
        for (int a = 0; a < 60 && np < POOLN; a++) {
            int Gt = (int)(minG + rndint((int)window));
            int m, k2;
            long long r;
            if (!sample_group(Gt, &m, &k2, &r)) continue;
            pool[np].m = m;
            pool[np].k2 = k2;
            pool[np].r = r;
            pool[np].G = m * k2;
            np++;
        }
        if (np == 0) continue;

        for (int i = 0; i < np; i++) {
            set_group(pool[i].m, pool[i].k2, pool[i].r);
            rand_gens();
            memcpy(pool[i].S, S, sizeof(int) * DEG);
            pool[i].cost = 1 << 30;
        }

        long B = 1500, B0 = 1500;
        int alive = np, success = 0;
        while (alive > 0 && !success && now() < deadline) {
            for (int i = 0; i < alive && now() < deadline; i++) {
                set_group(pool[i].m, pool[i].k2, pool[i].r);
                memcpy(S, pool[i].S, sizeof(int) * DEG);
                for (int j = 0; j < DEG; j++) set_gen(j);
                int c = anneal(B, deadline);
                memcpy(pool[i].S, S, sizeof(int) * DEG);
                pool[i].cost = c;
                if (c == 0) {
                    have = 1;
                    bestGM = pool[i].m;
                    bestGK = pool[i].k2;
                    bestGR = pool[i].r;
                    bestG = G;
                    memcpy(bestS, S, sizeof(int) * DEG);
                    minG = (long)G + 1;  /* raise the bar and keep searching */
                    success = 1;
                    break;
                }
            }
            if (success) break;

            for (int i = 1; i < alive; i++) {
                Cand tmp = pool[i];
                int j = i - 1;
                while (j >= 0 && pool[j].cost > tmp.cost) {
                    pool[j + 1] = pool[j];
                    j--;
                }
                pool[j + 1] = tmp;
            }
            if (alive > 1) alive = (alive + 1) / 2;
            else if (B > 40 * B0) break;
            B *= 2;
        }
    }

    if (!have) { printf("0 0\n"); return 0; }

    set_group(bestGM, bestGK, bestGR);
    memcpy(S, bestS, sizeof(int) * DEG);
    int n = 2 * bestG, m = bestG * DEG;
    printf("%d %d\n", n, m);
    for (int g = 0; g < bestG; g++)
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", g, bestG + gmul(g, S[j]));
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Algebraic baselines (safe, always valid for the stated diameter).
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


# ----------------------------------------------------------------------------
# Slack extension: add vertices using spare degree; every kept graph is valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    final_deadline = start + max(1.0, time_limit - 4.0)
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main engine: C search over bi-Cayley graphs on nonabelian groups.
    if d >= 2 and time.monotonic() < deadline - 2.0:
        remaining = deadline - time.monotonic()
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.0, 2), best_n],
                            stdin_graph=None, timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Use spare degree in the best graph to add vertices, if any exists.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
