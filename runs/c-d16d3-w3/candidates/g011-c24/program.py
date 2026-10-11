import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: multiset packing for arc-extended projective plane graphs.
#
# Input (stdin): graph "n m" with n = 2M. Items are vertices u < M, targets are
# v - M for edges (u, v) with v >= M. Each item hits its target list. Capacity S
# per target. Choose a multiset of items (repeats allowed) maximising its size
# with every target hit at most S times. Simulated annealing on a fixed size K
# with violation V = sum max(0, load - S); K grows whenever V = 0.
# Output: K, then K lines with one item index each.
# ----------------------------------------------------------------------------

C_PACK = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXT 64

static int M, S;
static int tn[MAXM];
static int tg[MAXM][MAXT];
static int load[MAXM];
static int x[MAXM], bestx[MAXM];
static int K, bestK;
static long V;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void bump(int p, int dl) {
    for (int k = 0; k < tn[p]; k++) {
        int L = tg[p][k];
        if (dl > 0) {
            if (load[L] >= S) V++;
            load[L]++;
        } else {
            load[L]--;
            if (load[L] >= S) V--;
        }
    }
    x[p] += dl;
    K += dl;
}

static int added_viol(int p) {
    int c = 0;
    for (int k = 0; k < tn[p]; k++)
        if (load[tg[p][k]] >= S) c++;
    return c;
}

static int pick_unit(void) {
    for (;;) {
        int p = rndint(M);
        if (x[p] > 0) return p;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    S = atoi(argv[1]);
    double budget = atof(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();

    int n = 0, mm = 0;
    if (scanf("%d %d", &n, &mm) != 2) n = 0;
    M = n / 2;
    if (S <= 0 || M <= 0 || M > MAXM) {
        printf("0\n");
        return 0;
    }
    for (int e = 0; e < mm; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || u >= M || v < M || v >= n) continue;
        if (tn[u] < MAXT) tg[u][tn[u]++] = v - M;
    }

    double t_end = now() + budget;
    double T = 0.3;
    long stall = 0;
    bestK = 0;
    while (now() < t_end) {
        if (V == 0) {
            if (K > bestK) {
                bestK = K;
                memcpy(bestx, x, sizeof(int) * M);
            }
            int bp = 0, bv = 1 << 30;
            for (int k = 0; k < 20; k++) {
                int p = rndint(M);
                int v = added_viol(p);
                if (v < bv) { bv = v; bp = p; }
            }
            bump(bp, 1);
            T = 0.2 + 0.4 * rnd01();
            stall = 0;
            continue;
        }
        int p = pick_unit();
        int r = rndint(M);
        if (r == p) continue;
        long Vb = V;
        bump(p, -1);
        bump(r, 1);
        long dV = V - Vb;
        if (dV > 0 && rnd01() >= exp(-(double)dV / T)) {
            bump(r, -1);
            bump(p, 1);
        }
        if (++stall > 300000) {
            bump(pick_unit(), -1);
            stall = 0;
            T = 0.2 + 0.4 * rnd01();
        }
    }

    printf("%d\n", bestK);
    for (int p = 0; p < M; p++)
        for (int c = 0; c < bestx[p]; c++)
            printf("%d\n", p);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: vertex addition with a greedy set cover (from the earlier engine).
# A new vertex joins a set of spare vertices on the other side that covers
# everything within distance D-1, so no distance grows past D.
# ----------------------------------------------------------------------------

C_ADD = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2 && fails < 4000) {
        int X = rndint(2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
#
# Arc-extended PG(2,q) with q + 1 + s = d, s = d - q - 1:
#   A-vertex per entry P of a multiset SA of points, joined to the q+1 lines through P;
#   B-vertex per entry j of a multiset SB of lines, joined to the q+1 points on j.
# Every line carries at most s A-neighbours and every point at most s B-neighbours,
# so degrees stay <= d. Diameter stays 3 for any such multisets (checked by lib.is_valid).
# Order: 2(q^2+q+1) + |SA| + |SB|, with |SA|, |SB| <= s(q^2+q+1)/(q+1).
# ----------------------------------------------------------------------------

def _incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); lines are indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _pack(m, s, edges, budget, seed):
    """Run C_PACK on the bipartite (item, target) graph with targets m..2m-1; return item list."""
    text = lib.run_c(C_PACK, [s, f"{budget:.2f}", seed],
                     stdin_graph=(2 * m, edges), timeout=budget + 10.0)
    nums = [int(v) for v in text.split()]
    if not nums:
        return []
    k = nums[0]
    items = nums[1:1 + k]
    if len(items) != k:
        return []
    return items


def _arc_graph(m, edges, pl, lp, SA, SB):
    """Old PG incidence plus A-vertices (per SA entry) and B-vertices (per SB entry)."""
    na, nb = len(SA), len(SB)
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        y = 2 * m + na + t
        for Q in lp[j]:
            E.append((Q, y))
    return 2 * m + na + nb, E


def _gq_w(q):
    """Incidence graph of the generalized quadrangle W(q) (diameter 4)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found, using about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = (1, [])
    fb = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, always valid for D >= 2
    if lib.is_valid(fb[0], fb[1], d, D):
        best = fb

    def consider(thunk):
        nonlocal best
        try:
            n, e = thunk()
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, list(e))
        except Exception:
            pass

    # Known constructions.
    if D == 3:
        if lib.is_prime_power(d - 1):
            consider(lambda: lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            consider(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 4 and d - 1 <= 9:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                consider(lambda q=q: _gq_w(q))
                break

    # Multiset arc-extensions of PG(2,q), best two q by estimated order.
    if D >= 3:
        qs = [q for q in range(2, min(d - 1, 23) + 1)
              if lib.is_prime_power(q) and d - q - 1 >= 1]
        qs.sort(key=lambda q: -(q * q + q + 1) / (q + 1))
        qs = qs[:2]
        window = 0.5 * max(0.0, hard_end - time.monotonic())
        shares = [0.7, 0.3]
        for idx, q in enumerate(qs):
            try:
                m, edges, pl, lp = _incidence(q)
                s = d - q - 1
                budget = max(0.3, window * shares[idx] / 2.0)
                # A side: items are points, targets are lines (load <= s).
                SA = _pack(m, s, edges, budget, seed * 17 + 2 * idx)
                # B side: items are lines, targets are points (load <= s).
                edgesB = [(j, m + Q) for j in range(m) for Q in lp[j]]
                SB = _pack(m, s, edgesB, budget, seed * 17 + 2 * idx + 1)
                consider(lambda SA=SA, SB=SB: _arc_graph(m, edges, pl, lp, SA, SB))
            except Exception:
                pass

    # Vertex-addition engine on the best graph found so far.
    if best[0] < lib.moore_bound(d, D):
        rem = hard_end - time.monotonic() - 0.5
        if rem > 1.0:
            try:
                text = lib.run_c(C_ADD, [d, D, seed * 31 + 1, f"{rem:.2f}"],
                                 stdin_graph=best, timeout=rem + 5.0)
                consider(lambda: lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return fb if lib.is_valid(fb[0], fb[1], d, D) else (1, [])
    return best
