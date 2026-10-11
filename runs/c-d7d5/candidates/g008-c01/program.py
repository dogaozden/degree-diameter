import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley lift
# over a finite group G (given by a multiplication table).
#
# Two group families:
#   type 0: semidirect Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#   type 1: affine-type group GF(p^2) x| Z_h, where Z_h acts on GF(p^2)
#           by multiplication with a subgroup of order h of GF(p^2)*.
#           Element (b, i) with b in GF(p^2), i in Z_h, coded as b*h + i,
#           product (b1, i1)(b2, i2) = (b1 + z^i1 * b2, i1 + i2).
#           Its normal subgroup GF(p^2)+ = Z_p x Z_p is not cyclic, so these
#           lifts are a different family from the cyclic-normal-part lifts.
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1 (so every vertex has degree DEG). Dart e = l*K + i joins A_i to
# B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j,g*s} for all g.
# Left multiplication is an automorphism, so the BFS from the 2K
# representatives decides the diameter exactly.
#
# Moves: change a voltage, or swap the targets of two darts in one layer
# (keeps degrees). Cost = unreached (rep, vertex) pairs + duplicate penalty.
#
# Usage: prog d D K type p1 p2 p3 seed slice_seconds
#   type 0: p1 = m, p2 = k2, p3 = r
#   type 1: p1 = p (prime), p2 = h (divides p^2 - 1), p3 unused
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define MAXG 2500

static int DEG, DIAM, K, G, N, NE;
static int *MT;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static int FP, FC0, FC1;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ---- group type 0: semidirect Z_m x|_r Z_k2 ---- */
static int build_semidirect(int m, int k2, int r) {
    if (m < 1 || k2 < 1 || k2 > 60) return 0;
    if (m * k2 > MAXG) return 0;
    r %= m;
    if (gcd_int(r, m) != 1) return 0;
    int powr[64];
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    if (((long long)powr[k2 - 1] * r) % m != 1 % m) return 0;
    G = m * k2;
    MT = malloc(sizeof(int) * (size_t)G * G);
    if (!MT) return 0;
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, dd = y % k2;
            long long t = (a + (long long)powr[b] * c) % m;
            MT[(size_t)x * G + y] = (int)(t * k2 + (b + dd) % k2);
        }
    }
    return 1;
}

/* ---- group type 1: GF(p^2) x| Z_h ---- */
static int fmul(int a, int b) {
    int u1 = a % FP, v1 = a / FP, u2 = b % FP, v2 = b / FP;
    int ru = (u1 * u2 + v1 * v2 * FC0) % FP;
    int rv = (u1 * v2 + u2 * v1 + v1 * v2 * FC1) % FP;
    return ru + rv * FP;
}
static int fadd(int a, int b) {
    int u1 = a % FP, v1 = a / FP, u2 = b % FP, v2 = b / FP;
    return ((u1 + u2) % FP) + ((v1 + v2) % FP) * FP;
}

static int build_affine(int p, int h) {
    if (p < 2 || p > 61 || h < 1) return 0;
    int q = p * p;
    if ((q - 1) % h != 0) return 0;
    G = q * h;
    if (G > MAXG) return 0;
    FP = p;
    if (p == 2) { FC1 = 1; FC0 = 1; }   /* x^2 = x + 1 */
    else {
        char sq[64];
        memset(sq, 0, sizeof sq);
        for (int x = 0; x < p; x++) sq[(x * x) % p] = 1;
        FC1 = 0; FC0 = -1;
        for (int c = 1; c < p; c++) if (!sq[c]) { FC0 = c; break; }   /* x^2 = c */
        if (FC0 < 0) return 0;
    }
    int *pw = malloc(sizeof(int) * h);
    char *seen = malloc(q);
    if (!pw || !seen) return 0;
    int zf = -1;
    for (int z = 1; z < q && zf < 0; z++) {
        memset(seen, 0, q);
        int x = 1, ok = 1;
        for (int i = 0; i < h; i++) {
            if (seen[x]) { ok = 0; break; }
            seen[x] = 1;
            pw[i] = x;
            x = fmul(x, z);
        }
        if (ok && x == 1) zf = z;
    }
    if (zf < 0) { free(pw); free(seen); return 0; }
    MT = malloc(sizeof(int) * (size_t)G * G);
    if (!MT) { free(pw); free(seen); return 0; }
    for (int x = 0; x < G; x++) {
        int b1 = x / h, i1 = x % h;
        for (int y = 0; y < G; y++) {
            int b2 = y / h, i2 = y % h;
            int b = fadd(b1, fmul(pw[i1], b2));
            int i = (i1 + i2) % h;
            MT[(size_t)x * G + y] = b * h + i;
        }
    }
    free(pw);
    free(seen);
    return 1;
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = MT[(size_t)g * G + s];
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 10) {
        fprintf(stderr, "usage: prog d D K type p1 p2 p3 seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    int type = atoi(argv[4]);
    int p1 = atoi(argv[5]);
    int p2 = atoi(argv[6]);
    int p3 = atoi(argv[7]);
    uint64_t seed = strtoull(argv[8], NULL, 10);
    double slice = atof(argv[9]);

    if (DEG < 1 || DIAM < 1 || K < 1) {
        printf("0 0\n");
        return 0;
    }
    int ok = 0;
    if (type == 0) ok = build_semidirect(p1, p2, p3);
    else if (type == 1) ok = build_affine(p1, p2);
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    N = 2 * K * G;
    NE = DEG * K;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            /* Fresh random lift. */
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) {
                dS[e] = rndint(G);
                set_perm(e);
            }
            T0 = 2.0;
        } else {
            /* Reheat from the best state found so far, with a random kick. */
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions.
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
# Greedy spare-degree extension.
# A valid bipartite graph whose vertices do not all reach degree d can grow:
# add a fresh pair (a, b) with edge a-b, join a to spare B-side vertices and b
# to spare A-side vertices, and keep the result only if lib.is_valid accepts it.
# Regular lifts have no spare degree, so this is a no-op for them.
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    """Return a 0/1 side label per vertex (bipartition), or None if not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _extend_spare(n, edges, d, D, deadline):
    """Greedily add fresh vertex pairs while the graph stays valid. Returns (n, edges)."""
    if d < 2:
        return n, edges
    col = _two_colour(n, edges)
    if col is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A_sp = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B_sp = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A_sp or not B_sp:
            break
        grown = False
        for k in range(d - 1, 0, -1):
            if time.monotonic() >= deadline:
                break
            if k > len(A_sp) or k > len(B_sp):
                continue
            a, b = n, n + 1
            cand_new = [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
            cand = edges + cand_new
            if lib.is_valid(n + 2, cand, d, D):
                edges = cand
                n += 2
                col += [0, 1]
                deg += [0, 0]
                deg[a] = k + 1
                deg[b] = k + 1
                for x in B_sp[:k]:
                    deg[x] += 1
                for y in A_sp[:k]:
                    deg[y] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Group families for the search.
# ----------------------------------------------------------------------------

def _primes(n):
    return [x for x in range(2, n + 1) if all(x % y for y in range(2, int(x ** 0.5) + 1))]


_AFF = None


def _affine_list():
    """All (G, p, h) with G = p^2 * h <= 2500, h | p^2 - 1: the GF(p^2) x| Z_h family, sorted by G."""
    global _AFF
    if _AFF is None:
        out = []
        for p in _primes(61):
            q = p * p
            for h in range(1, q):
                if (q - 1) % h == 0 and q * h <= 2500:
                    out.append((q * h, p, h))
        out.sort()
        _AFF = out
    return _AFF


def _sample_affine(lo, rng):
    """Return (G, p, h) with G >= lo, preferring orders just above lo, or None."""
    cands = [c for c in _affine_list() if c[0] >= lo]
    if not cands:
        return None
    window = [c for c in cands if c[0] <= 1.3 * lo + 12] or cands[:1]
    return rng.choice(window[:6])


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target."""
    k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
    m = max(2, -(-target // k2))
    r = 1  # r = 1 is the direct product, always valid
    if k2 > 1 and m > 2:
        cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
    return m, k2, r


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.9 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    # Main search: C anneals voltages of bi-Cayley lifts. Most calls use the
    # GF(p^2) x| Z_h family (a different group family from the parent's
    # cyclic-normal-part lifts); the rest use the semidirect family.
    # Each target group order is just above best / (2k), so successes improve.
    failures = 0
    while failures < 3:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 9.0)
        k = rng.choice([1, 1, 2, 2, 3])
        base = best[0] // (2 * k)
        target = base + 1 + rng.randrange(0, max(2, base // 10 + 1))

        args = None
        if rng.random() < 0.8:
            g = _sample_affine(target, rng)
            if g is not None:
                G, p, h = g
                args = [d, D, k, 1, p, h, 0, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"]
        if args is None:
            m, k2, r = _sample_group(target, rng)
            args = [d, D, k, 0, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"]

        try:
            out = lib.run_c(C_SOURCE, args, timeout=slice_s + 10.0)
        except RuntimeError:
            failures += 1
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension on the best graph, with the remaining time.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
