import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: tabu search over single-base-vertex bi-Cayley graphs
# (Haar-type lifts) over a semidirect product G = Z_m x|_r Z_k.
#
# Graph: vertices A_g and B_g for g in G (2|G| vertices). Connection set S of
# DEG distinct group elements; A_g is joined to B_{g s} for every s in S.
# Left multiplication by h is an automorphism, so the BFS from A_e and B_e
# decides the diameter exactly: cost = unreached (rep, vertex) pairs.
#
# Search: for each candidate group, tabu search over S. A step samples random
# single-element replacements, takes the best non-tabu one (aspiration if it
# beats the restart's best), and restarts after STAG steps without progress.
#
# Schedule: the groups come in ascending order of |G|. Each round gives every
# live group a time slice; the slice doubles per round. A success at order n
# removes every candidate with order <= n, so the search only climbs.
#
# Usage: prog d D seed total_seconds (m k r)*
# Prints the largest valid graph found ("n m" + edges), or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXG 2600
#define MAXT 1500
#define MAXDEG 60
#define NSAMP 150
#define STAG 2500

static int DEG, DIAM;
static int G, MM, K2;
static int *MUL = NULL;
static int *INV = NULL;
static int *POWR = NULL;
static uint32_t *vis = NULL;
static uint32_t stamp = 0;
static int *qbuf = NULL;
static int *tabu_until = NULL;
static int S[MAXDEG];
static int iS[MAXDEG];
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void free_group(void) {
    free(MUL); MUL = NULL;
    free(INV); INV = NULL;
    free(POWR); POWR = NULL;
    free(vis); vis = NULL;
    free(qbuf); qbuf = NULL;
    free(tabu_until); tabu_until = NULL;
}

/* Element (a, b) is coded a*K2 + b; (a,b)(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static int setup_group(int m, int k, int r) {
    free_group();
    if (m < 1 || k < 1) return 0;
    MM = m; K2 = k;
    G = m * k;
    if (G < DEG || G > MAXG) return 0;
    POWR = malloc(sizeof(int) * (size_t)k);
    if (!POWR) { free_group(); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < k; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if ((((long long)POWR[k - 1]) * r) % MM != 1 % MM) { free_group(); return 0; }
    MUL = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    vis = calloc((size_t)2 * G, sizeof(uint32_t));
    qbuf = malloc(sizeof(int) * (size_t)2 * G);
    tabu_until = calloc((size_t)G, sizeof(int));
    if (!MUL || !INV || !vis || !qbuf || !tabu_until) { free_group(); return 0; }
    stamp = 0;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MUL[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++)
            if (MUL[(size_t)x * G + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) { free_group(); return 0; }
    }
    return 1;
}

static int cost_fn(void) {
    for (int t = 0; t < DEG; t++) iS[t] = INV[S[t]];
    int total = 0;
    for (int rep = 0; rep < 2; rep++) {
        int src = (rep == 0) ? 0 : G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)2 * G);
            stamp = 0;
        }
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qbuf[tail++] = src;
        for (int lv = 0; lv < DIAM && head < tail; lv++) {
            int end = tail;
            while (head < end) {
                int u = qbuf[head++];
                if (u < G) {
                    const int *row = MUL + (size_t)u * G;
                    for (int t = 0; t < DEG; t++) {
                        int v = G + row[S[t]];
                        if (vis[v] != stamp) { vis[v] = stamp; qbuf[tail++] = v; }
                    }
                } else {
                    const int *row = MUL + (size_t)(u - G) * G;
                    for (int t = 0; t < DEG; t++) {
                        int v = row[iS[t]];
                        if (vis[v] != stamp) { vis[v] = stamp; qbuf[tail++] = v; }
                    }
                }
            }
        }
        total += 2 * G - tail;
    }
    return total;
}

static int in_set_upto(int x, int cnt) {
    for (int t = 0; t < cnt; t++) if (S[t] == x) return 1;
    return 0;
}

/* Returns 1 with a zero-cost S[] in place, or 0 when the slice runs out. */
static int tabu_slice(double secs) {
    double tend = now_s() + secs;
    int it = 0;
    memset(tabu_until, 0, sizeof(int) * (size_t)G);
    while (now_s() < tend) {
        for (int t = 0; t < DEG; t++) {
            int x;
            do { x = rndint(G); } while (in_set_upto(x, t));
            S[t] = x;
        }
        int cur = cost_fn();
        if (cur == 0) return 1;
        int rbest = cur, since = 0;
        while (since < STAG && now_s() < tend) {
            it++;
            int bc = 0x7fffffff, bp = -1, bx = -1, ties = 0;
            for (int s = 0; s < NSAMP; s++) {
                int p = rndint(DEG), x = rndint(G);
                if (in_set_upto(x, DEG)) continue;
                int old = S[p];
                S[p] = x;
                int c = cost_fn();
                S[p] = old;
                if (tabu_until[x] > it && c >= rbest) continue;
                if (c < bc) { bc = c; bp = p; bx = x; ties = 1; }
                else if (c == bc) {
                    ties++;
                    if (rndint(ties) == 0) { bp = p; bx = x; }
                }
            }
            if (bp < 0) continue;
            int old = S[bp];
            S[bp] = bx;
            tabu_until[old] = it + 3 + rndint(8);
            cur = bc;
            if (cur == 0) return 1;
            if (cur < rbest) { rbest = cur; since = 0; }
            else since++;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5 || (argc - 5) % 3 != 0) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double total = atof(argv[4]);
    int nt = (argc - 5) / 3;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || nt < 1 || nt > MAXT) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;

    int *tm = malloc(sizeof(int) * (size_t)nt);
    int *tk = malloc(sizeof(int) * (size_t)nt);
    int *tr = malloc(sizeof(int) * (size_t)nt);
    int *tg = malloc(sizeof(int) * (size_t)nt);
    char *alive = malloc((size_t)nt);
    if (!tm || !tk || !tr || !tg || !alive) { printf("0 0\n"); return 0; }
    for (int i = 0; i < nt; i++) {
        tm[i] = atoi(argv[5 + 3 * i]);
        tk[i] = atoi(argv[6 + 3 * i]);
        tr[i] = atoi(argv[7 + 3 * i]);
        tg[i] = tm[i] * tk[i];
        alive[i] = 1;
    }

    double t0 = now_s();
    int bestG = 0, bestIdx = -1;
    int bestS[MAXDEG];
    double slice = 0.08;
    while (1) {
        double remaining = total - (now_s() - t0);
        if (remaining <= 0.02) break;
        int any = 0;
        for (int i = 0; i < nt; i++) {
            if (!alive[i]) continue;
            any = 1;
            remaining = total - (now_s() - t0);
            if (remaining <= 0.02) break;
            if (!setup_group(tm[i], tk[i], tr[i])) { alive[i] = 0; continue; }
            double sl = slice < remaining ? slice : remaining;
            if (tabu_slice(sl)) {
                if (G > bestG) {
                    bestG = G;
                    bestIdx = i;
                    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
                }
                for (int j = 0; j < nt; j++)
                    if (tg[j] <= tg[i]) alive[j] = 0;
            }
        }
        if (!any) break;
        slice *= 2.0;
    }
    free_group();

    if (bestIdx < 0) { printf("0 0\n"); return 0; }
    if (!setup_group(tm[bestIdx], tk[bestIdx], tr[bestIdx])) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * G, DEG * G);
    for (int g = 0; g < G; g++)
        for (int t = 0; t < DEG; t++)
            printf("%d %d\n", g, G + MUL[(size_t)g * G + bestS[t]]);
    fflush(stdout);
    free_group();
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
# Group candidates for the C search.
# ----------------------------------------------------------------------------

MAX_GROUP = 2500   # keep in sync with MAXG in the C source
WINDOW = 450       # candidate group orders scanned per search call


def _group_options(n, rng):
    """Return one (m, k, r) with m*k = n: Z_m x|_r Z_k, preferring non-abelian choices."""
    nonab, direct = [], []
    for m in range(1, n + 1):
        if n % m:
            continue
        k = n // m
        direct.append((m, k, 1))
        if m >= 3 and k >= 2:
            for c in range(2, m):
                if math.gcd(c, m) == 1 and pow(c, k, m) == 1:
                    nonab.append((m, k, c))
    if nonab and rng.random() < 0.8:
        return rng.choice(nonab)
    return rng.choice(direct)


def _group_search(d, D, seed, budget, lo, rng):
    """One C call: tabu search over groups with orders lo .. lo+WINDOW-1. Returns (n, edges)."""
    tuples = []
    for n in range(max(lo, d), lo + WINDOW):
        if n > MAX_GROUP:
            break
        tuples.append(_group_options(n, rng))
    if not tuples:
        return None
    args = [d, D, seed, f"{budget:.2f}"]
    for m, k, r in tuples:
        args += [m, k, r]
    out = lib.run_c(C_SOURCE, args, timeout=budget + 8.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Greedy spare-degree extension (no-op for regular graphs).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
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

    # Bold search: tabu over single-vertex bi-Cayley lifts of semidirect groups,
    # climbing through group orders above half the current best order.
    if D >= 3 and d >= 2:
        remaining = deadline - time.monotonic() - 2.0
        if remaining > 2.0:
            lo = best[0] // 2 + 1
            try:
                res = _group_search(d, D, seed % (10 ** 9) + 1, remaining, lo, rng)
            except (RuntimeError, ValueError):
                res = None
            if res is not None and res[0] > 0:
                consider(res[0], res[1])

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
