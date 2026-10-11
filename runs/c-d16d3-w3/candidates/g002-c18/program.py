"""Diameter-3 search by difference covers, with the structured starts as fallback.

New construction: the bipartite Haar graph H(G, S) on two copies of a finite group G of order m.
Vertices a_x and b_y (x, y in G) are joined when y = x*s for some s in S, |S| = d. The graph is
d-regular and bipartite. It has diameter <= 3 exactly when S*S^-1 = G and S^-1*S = G, a "difference
cover" of G by d elements. Counting gives m <= d(d-1)+1, so the order 2m is bounded by the Moore
bound 2(d^2-d+1). A C annealer searches for covers of groups of order m = lo, lo+1, ... and the
search stops at the first order it cannot cover. Groups are cyclic or Z_m x| Z_k.

Safety: every candidate goes through lib.is_valid. The parent's structured starts (projective
planes, Araujo-Pardo/Lopez, conic blow-ups, arc-extended PG(2,q), W(q)) and K_{d,d} remain as
fallbacks, so the output is always valid. A vertex-addition engine grows non-regular starts.
"""
import itertools
import math
import random
import time

import lib

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

C_COVER = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 512
#define MAXK 64
#define FLATCAP (MAXM * MAXM + 2 * MAXM + 16)

/* Input (stdin, via a graph-format wrapper): flat ints = M, inv[0..M-1], mul[i][j] row-major.
   Argument: K seed budget. Element 0 is the identity.
   Searches a K-subset S of the group with S*S^-1 = G and S^-1*S = G (difference cover).
   Prints "OK" and the subset, or "FAIL". */

static int M, K;
static int mt[MAXM][MAXM];
static int iv[MAXM];
static int S[MAXK];
static int inS[MAXM];
static int cnt1[MAXM], cnt2[MAXM];
static int zeros;
static int flat[FLATCAP];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void bump1(int g, int sg) {
    if (sg > 0) { if (cnt1[g]++ == 0) zeros--; }
    else { if (--cnt1[g] == 0) zeros++; }
}

static void bump2(int g, int sg) {
    if (sg > 0) { if (cnt2[g]++ == 0) zeros--; }
    else { if (--cnt2[g] == 0) zeros++; }
}

/* Add (sg = +1) or remove (sg = -1) all ordered pairs involving x and the other members
   S[j] for j != skip, plus the pair (x, x). */
static void contrib(int x, int skip, int sg) {
    int ix = iv[x];
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        int y = S[j];
        bump1(mt[x][iv[y]], sg);
        bump2(mt[ix][y], sg);
        bump1(mt[y][ix], sg);
        bump2(mt[iv[y]][x], sg);
    }
    bump1(mt[x][ix], sg);
    bump2(mt[ix][x], sg);
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    K = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("FAIL\n"); return 0; }
    int cnt = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (cnt + 2 > FLATCAP) break;
        flat[cnt++] = u;
        flat[cnt++] = v;
    }
    if (cnt < 1) { printf("FAIL\n"); return 0; }
    M = flat[0];
    if (M < 2 || M > MAXM || K < 1 || K > MAXK || K > M || cnt < 1 + M + M * M) {
        printf("FAIL\n");
        return 0;
    }
    for (int i = 0; i < M; i++) {
        iv[i] = flat[1 + i];
        if (iv[i] < 0 || iv[i] >= M) { printf("FAIL\n"); return 0; }
    }
    for (int i = 0; i < M; i++)
        for (int j = 0; j < M; j++) {
            int x = flat[1 + M + i * M + j];
            if (x < 0 || x >= M) { printf("FAIL\n"); return 0; }
            mt[i][j] = x;
        }

    double t_end = now() + budget;
    for (int g = 0; g < M; g++) { inS[g] = 0; cnt1[g] = 0; cnt2[g] = 0; }
    for (int i = 0; i < K; i++) {
        int g;
        do g = rndint(M); while (inS[g]);
        S[i] = g;
        inS[g] = 1;
    }
    zeros = 2 * M;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) {
            bump1(mt[S[i]][iv[S[j]]], +1);
            bump2(mt[iv[S[i]]][S[j]], +1);
        }

    double T = 1.5;
    long it = 0;
    while (zeros > 0) {
        if ((it & 1023) == 0 && now() > t_end) break;
        it++;
        int i = rndint(K);
        int old = S[i];
        int t = S[rndint(K)];
        int mode = rndint(3);
        int g;
        if (mode == 0) {
            int u0 = rndint(M), u = -1;
            for (int q = 0; q < M; q++) {
                int c = (u0 + q) % M;
                if (cnt1[c] == 0) { u = c; break; }
            }
            g = (u >= 0) ? mt[u][t] : rndint(M);
        } else if (mode == 1) {
            int u0 = rndint(M), u = -1;
            for (int q = 0; q < M; q++) {
                int c = (u0 + q) % M;
                if (cnt2[c] == 0) { u = c; break; }
            }
            g = (u >= 0) ? mt[t][iv[u]] : rndint(M);
        } else {
            g = rndint(M);
        }
        if (inS[g]) continue;

        int before = zeros;
        contrib(old, i, -1);
        S[i] = g;
        inS[old] = 0;
        inS[g] = 1;
        contrib(g, i, +1);
        int delta = zeros - before;
        if (!(delta <= 0 || rnd01() < exp(-(double)delta / T))) {
            contrib(g, i, -1);
            S[i] = old;
            inS[g] = 0;
            inS[old] = 1;
            contrib(old, i, +1);
        }
        T *= 0.99998;
        if (T < 0.1) T = 1.5;
    }

    if (zeros == 0) {
        printf("OK\n");
        for (int i = 0; i < K; i++) printf("%d ", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    (void)n;
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (parent constructions, kept as fallbacks).
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Best directly constructible graph for D = 3: Moore graph or Araujo-Pardo/Lopez."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


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


def _local_arc(m, s, point_lines, line_points, rng, init, deadline, iters):
    """Plateau local search for a large set S where every line and every point carries at most s members of S."""
    inS = [False] * m
    cl = [0] * m
    cp = [0] * m
    S = []

    def fits(P):
        return all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P])

    def put(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def take(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    for P in init:
        if not inS[P] and fits(P):
            put(P)
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            put(P)
        else:
            fullL = {L for L in point_lines[P] if cl[L] >= s}
            fullQ = {Q for Q in line_points[P] if cp[Q] >= s}
            blockers = [Q for Q in S
                        if any(L in fullL for L in point_lines[Q])
                        or any(R in fullQ for R in line_points[Q])]
            if len(blockers) != 1:
                continue
            b = blockers[0]
            take(b)
            if fits(P):
                put(P)
            else:
                put(b)
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[], _greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2 and q >= 3:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        init = max(cands, key=len)
        loc = _local_arc(m, s, pl, lp, rng, init,
                         min(deadline, time.monotonic() + 0.5), 4000)
        cands.append(loc)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def _gq_w(q):
    """Incidence graph of W(q), the generalized quadrangle (diameter 4)."""
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


def starts(d, D, deadline, rng):
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    if D >= 3:
        out.extend(_arc_extensions(d, deadline, rng))
    if D >= 4 and d - 1 <= 6:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# Difference-cover Haar graphs.
# ----------------------------------------------------------------------------

def _group_options(N, rng):
    """Candidate groups of order N: the cyclic group, plus up to two Z_m x| Z_k."""
    opts = [("cyc",)]
    divs = [(m, N // m) for m in range(2, N) if N % m == 0 and N // m >= 2]
    rng.shuffle(divs)
    for m, k in divs[:6]:
        rs_ = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs_:
            opts.append(("sd", m, k, rng.choice(rs_)))
        if len(opts) >= 3:
            break
    return opts


def _group_tables(opt, N):
    """Return (mt, iv): full multiplication table and inverses, identity = 0."""
    if opt[0] == "cyc":
        order, mul, inv = lib.cyclic_group(N)
    else:
        order, mul, inv = lib.semidirect_group(opt[1], opt[2], opt[3])
    iv = [inv(x) for x in range(order)]
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    return mt, iv


def _encode(mt, iv):
    """Pack the tables as a dummy graph edge list (run_c only transports graph text)."""
    M = len(mt)
    flat = [M] + list(iv) + [x for row in mt for x in row]
    if len(flat) % 2:
        flat.append(0)
    return [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


def _cover_attempt(N, d, budget, rng):
    """Try to find a d-element difference cover of some group of order N. Return (mt, S) or None."""
    opts = _group_options(N, rng)
    share = budget / len(opts)
    for opt in opts:
        try:
            mt, iv = _group_tables(opt, N)
        except Exception:
            continue
        edges = _encode(mt, iv)
        try:
            out = lib.run_c(C_COVER, [d, rng.randrange(10 ** 9), f"{share:.2f}"],
                            stdin_graph=(1, edges), timeout=share + 5.0)
        except Exception:
            continue
        toks = out.split()
        if len(toks) >= 1 + d and toks[0] == "OK":
            S = [int(x) for x in toks[1:1 + d]]
            if len(set(S)) == d and all(0 <= s < N for s in S):
                return mt, S
    return None


def _haar_search(d, lo, deadline, rng):
    """Ascend over group orders m = lo, lo+1, ...; stop at the first m with no cover found."""
    hi = d * (d - 1) + 1
    best = None
    m = lo
    while m <= hi:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        budget = min(10.0, max(1.0, 0.35 * remaining))
        res = _cover_attempt(m, d, budget, rng)
        if res is None:
            break
        best = res
        m += 1
    return best


def _haar_graph(mt, S):
    """Bipartite Haar graph: a_x ~ b_{x*s} for s in S; returns (2m, edges)."""
    M = len(mt)
    return 2 * M, [(x, M + mt[x][s]) for x in range(M) for s in S]


# ----------------------------------------------------------------------------
# C engine driver (vertex addition, used for non-regular starts).
# ----------------------------------------------------------------------------

def _run_add(n0, e0, d, D, seed, budget):
    text = lib.run_c(C_ADD, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    if lib.is_valid(fallback[0], fallback[1], d, D):
        cands.append(fallback)
    try:
        starts_list = starts(d, D, t0 + 0.15 * time_limit, rng)
    except Exception:
        starts_list = []
    for g in starts_list:
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    # New construction: difference-cover Haar graphs, searched above the current best order.
    if D == 3 and d >= 3:
        lo = best[0] // 2 + 1
        if lo <= d * (d - 1) + 1:
            try:
                hit = _haar_search(d, lo, t0 + 0.70 * time_limit, rng)
            except Exception:
                hit = None
            if hit is not None:
                g = _haar_graph(*hit)
                if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                    best = g

    # Vertex-addition engine, only useful when the start has spare degree.
    regular = 2 * len(best[1]) == best[0] * d
    remaining = hard_end - time.monotonic()
    if not regular and remaining > 3.0:
        try:
            n1, e1 = _run_add(best[0], best[1], d, D, seed * 31 + 1,
                              max(0.5, remaining - 1.0))
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
