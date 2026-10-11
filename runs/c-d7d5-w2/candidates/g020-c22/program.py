import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A (lift search): simulated annealing over the voltages of a bi-Cayley
# lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Excess-distance
# cost, zero iff the lift has diameter <= DIAM.
#
# Usage: prog d D K m k2 r seed slice_seconds
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
#define STAG 8000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

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

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
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

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
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
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
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
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
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

        int runBest = cur;
        int since = 0;
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
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
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
# Engine B (repair search, new in this version): works on a general bipartite
# graph with max degree DEG, not a lift. Moves are degree-preserving edge
# switches (a1-b1, a2-b2) -> (a1-b2, a2-b1), which keep bipartiteness and
# never create duplicate edges. Cost = number of ordered (source, target)
# pairs at distance > D. Simulated annealing runs until cost 0 or the slice
# ends. Only a cost-0 graph is printed; otherwise "0 0".
#
# Usage: prog DEG D seed slice_seconds   (graph on stdin, "n m" + edges)
# ----------------------------------------------------------------------------

C_REPAIR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int D, DEG, N, M;
static int *eu, *ev, *adj, *cnt, *fr, *nx;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static void fail(void) {
    printf("0 0\n");
    fflush(stdout);
    exit(0);
}

static int cost_fn(void) {
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < M; e++) {
        int a = eu[e], b = ev[e];
        adj[(size_t)a * DEG + cnt[a]++] = b;
        adj[(size_t)b * DEG + cnt[b]++] = a;
    }
    int total = 0;
    for (int s = 0; s < N; s++) {
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        vis[s] = stamp;
        cur[0] = s;
        for (int lv = 0; lv < D && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                int cu = cnt[u];
                for (int t = 0; t < cu; t++) {
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
    return total;
}

static int has_edge(int a, int b) {
    for (int e = 0; e < M; e++)
        if (eu[e] == a && ev[e] == b) return 1;
    return 0;
}

static void output_graph(void) {
    printf("%d %d\n", N, M);
    for (int e = 0; e < M; e++) printf("%d %d\n", eu[e], ev[e]);
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;
    if (DEG < 1 || D < 1) fail();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) fail();
    if (n < 2 || m < 2) fail();
    N = n;
    M = m;
    int *iu = malloc(sizeof(int) * (size_t)M);
    int *iv = malloc(sizeof(int) * (size_t)M);
    if (!iu || !iv) fail();
    for (int e = 0; e < M; e++) {
        if (scanf("%d %d", &iu[e], &iv[e]) != 2) fail();
        if (iu[e] < 0 || iu[e] >= N || iv[e] < 0 || iv[e] >= N || iu[e] == iv[e]) fail();
    }

    int *ideg = calloc((size_t)N, sizeof(int));
    if (!ideg) fail();
    for (int e = 0; e < M; e++) { ideg[iu[e]]++; ideg[iv[e]]++; }
    for (int v = 0; v < N; v++) if (ideg[v] > DEG) fail();

    int *off = malloc(sizeof(int) * (size_t)(N + 1));
    int *pos = malloc(sizeof(int) * (size_t)N);
    int *nb = malloc(sizeof(int) * (size_t)(2 * M));
    if (!off || !pos || !nb) fail();
    off[0] = 0;
    for (int v = 0; v < N; v++) off[v + 1] = off[v] + ideg[v];
    for (int v = 0; v < N; v++) pos[v] = off[v];
    for (int e = 0; e < M; e++) {
        nb[pos[iu[e]]++] = iv[e];
        nb[pos[iv[e]]++] = iu[e];
    }
    for (int v = 0; v < N; v++)
        for (int i = off[v]; i < off[v + 1]; i++)
            for (int j = i + 1; j < off[v + 1]; j++)
                if (nb[i] == nb[j]) fail();

    int *side = malloc(sizeof(int) * (size_t)N);
    int *q = malloc(sizeof(int) * (size_t)N);
    if (!side || !q) fail();
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = off[u]; i < off[u + 1]; i++) {
                int v = nb[i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                } else if (side[v] == side[u]) {
                    fail();
                }
            }
        }
    }

    eu = malloc(sizeof(int) * (size_t)M);
    ev = malloc(sizeof(int) * (size_t)M);
    if (!eu || !ev) fail();
    for (int e = 0; e < M; e++) {
        if (side[iu[e]] == 0) { eu[e] = iu[e]; ev[e] = iv[e]; }
        else                  { eu[e] = iv[e]; ev[e] = iu[e]; }
    }

    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(uint32_t));
    if (!adj || !cnt || !fr || !nx || !vis) fail();

    int cur = cost_fn();
    if (cur == 0) { output_graph(); return 0; }

    clock_t t0 = clock();
    const double T0 = 3.0;
    while (1) {
        double el = (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
        if (el >= slice) break;
        double frac = el / slice;
        double T = T0 * (1.0 - frac) + 0.05;

        int e1 = rndint(M), e2 = rndint(M);
        if (e1 == e2) continue;
        int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;

        ev[e1] = b2;
        ev[e2] = b1;
        int nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) { output_graph(); return 0; }
        } else {
            ev[e1] = b1;
            ev[e2] = b2;
        }
    }
    printf("0 0\n");
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (unchanged in behaviour from the parent).
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


def _adopt(best, cand, d, D):
    """Return cand if it is larger than best and valid, else best."""
    n, e = cand
    if n > best[0] and lib.is_valid(n, e, d, D):
        return cand
    return best


# ----------------------------------------------------------------------------
# Lift-search phase (engine A), driven by a time deadline.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m = max(2, -(-target // k2))
        r = 1
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def _lift_phase(d, D, rng, best, deadline):
    """Anneal bi-Cayley lifts; adopt any larger valid lift. Returns the best graph."""
    step = 0.08
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        k = rng.choice([1, 1, 2, 2, 3])
        want = best[0] * (1.0 + step)
        target = max(2, math.ceil(want / (2 * k)))
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            step = max(0.005, step * 0.7)
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            step = min(0.4, step * 1.25)
        else:
            step = max(0.005, step * 0.7)
    return best


# ----------------------------------------------------------------------------
# Growth-and-repair phase (engine B). Each round removes k*(d-1) edges with
# distinct endpoints and adds k new pairs (x, y): x joins the freed B-side
# vertices, y joins the freed A-side vertices, and x-y is an edge. Degrees stay
# <= d and the graph stays bipartite. The C repair search then tries to restore
# diameter <= D by degree-preserving switches.
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


def _grow_round(n, edges, d, k_pairs, rng):
    """Return (n2, edges2) with k_pairs new vertex pairs, degrees <= d, or None."""
    col = _two_colour(n, edges)
    if col is None:
        return None
    need = k_pairs * (d - 1)
    order = list(range(len(edges)))
    rng.shuffle(order)
    used_a, used_b, removed = set(), set(), []
    for idx in order:
        if len(removed) == need:
            break
        u, v = edges[idx]
        a, b = (u, v) if col[u] == 0 else (v, u)
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        removed.append(idx)
    if len(removed) < need:
        return None
    rem = set(removed)
    new_edges = [e for i, e in enumerate(edges) if i not in rem]
    nn = n
    for j in range(k_pairs):
        x, y = nn, nn + 1
        nn += 2
        new_edges.append((x, y))
        for idx in removed[j * (d - 1):(j + 1) * (d - 1)]:
            u, v = edges[idx]
            a, b = (u, v) if col[u] == 0 else (v, u)
            new_edges.append((x, b))
            new_edges.append((y, a))
    return nn, new_edges


def _grow_phase(best, d, D, rng, deadline):
    """Repeatedly grow the graph and repair it. Adopts only valid, larger results."""
    if d < 3:
        return best
    pairs = 1
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining - 1.0, 8.0)
        grown = _grow_round(best[0], best[1], d, pairs, rng)
        if grown is None:
            if pairs == 1:
                break
            pairs = 1
            continue
        try:
            out = lib.run_c(
                C_REPAIR,
                [d, D, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=grown,
                timeout=slice_s + 10.0,
            )
            n3, e3 = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            pairs = max(1, pairs // 2)
            continue
        if n3 > best[0] and lib.is_valid(n3, e3, d, D):
            best = (n3, e3)
            pairs = min(pairs + 1, 4)
        else:
            pairs = max(1, pairs // 2)
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _adopt(best, pg, d, D)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            best = _adopt(best, gq, d, D)
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: lift search (reliable baseline).
    lift_deadline = start + 0.5 * budget
    try:
        best = _lift_phase(d, D, rng, best, lift_deadline)
    except Exception:
        pass

    # Phase 2: grow the best graph by vertex pairs and repair with switches.
    try:
        best = _grow_phase(best, d, D, rng, deadline)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
