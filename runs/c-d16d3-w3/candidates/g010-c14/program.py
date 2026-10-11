import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: arc-extended projective plane incidence graphs (diameter 3).
# Used only as a valid start graph. Old PG(2,q) vertices have degree q+1, so
# with d >= q+1 they have spare s = d-q-1. An A-vertex is added for each point
# of SA, joined to the q+1 lines through it, and a B-vertex for each line of
# SB, joined to the q+1 points on it, with each line loaded <= s by SA and each
# point loaded <= s by SB.
# ----------------------------------------------------------------------------

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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy selection with load cap s."""
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


def _local_side(m, s, nbr, S0, rng, deadline, iters=6000):
    """Plateau local search keeping the load cap s."""
    if s < 1:
        return list(S0)
    inS = [False] * m
    load = [0] * m
    S = list(S0)
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            load[t] += 1
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        over = {t for t in nbr[x] if load[t] >= s}
        if not over:
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
            if len(S) > len(best):
                best = list(S)
            continue
        cand = [y for y in S if any(t in over for t in nbr[y])]
        if not cand:
            continue
        y = rng.choice(cand)
        for t in nbr[y]:
            load[t] -= 1
        if all(load[t] < s for t in nbr[x]):
            S.remove(y)
            inS[y] = False
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
        else:
            for t in nbr[y]:
                load[t] += 1
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus new A-vertices (SA) and B-vertices (SB)."""
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
    """Return valid (n, edges) arc-extended graphs for prime powers q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
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

        SA = _local_side(m, s, point_lines, SA, rng, deadline)
        SB = _local_side(m, s, line_points, SB, rng, deadline)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# New main search (C): simulated annealing over the edge set of a bipartite
# graph that is grown one A-vertex and one B-vertex at a time. Cost is
# 4 * (number of vertex pairs at distance > D) + (total unused degree).
# Moves: add edge, remove edge, rewire one endpoint, degree-preserving 2-switch.
# Every accepted state with zero bad pairs is a valid graph and is recorded.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXN 3000

static int DEG, DIAM, N;
static int *adj, *dg, *side;
static int *badj, *bdg, *bside;
static int bestN = 0;
static u64 *RA, *RB;
static unsigned long long rs;
static int mkind, ma, mb, mc, md;

static unsigned long long rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (unsigned long long)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) / 9007199254740992.0; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < dg[a]; k++)
        if (adj[a * DEG + k] == b) return 1;
    return 0;
}
static void del_from(int a, int b) {
    for (int k = 0; k < dg[a]; k++) {
        if (adj[a * DEG + k] == b) {
            adj[a * DEG + k] = adj[a * DEG + dg[a] - 1];
            dg[a]--;
            return;
        }
    }
}
static void add_edge(int a, int b) {
    adj[a * DEG + dg[a]] = b;
    dg[a]++;
    adj[b * DEG + dg[b]] = a;
    dg[b]++;
}
static void rem_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
}

/* bad = number of unordered pairs at distance > DIAM; def = total unused degree */
static void evaluate(long long *bad, long long *def) {
    int n = N;
    int w = (n + 63) / 64;
    memset(RA, 0, sizeof(u64) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) RA[(size_t)v * w + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = RB + (size_t)v * w;
            memcpy(dst, RA + (size_t)v * w, sizeof(u64) * (size_t)w);
            for (int k = 0; k < dg[v]; k++) {
                const u64 *s2 = RA + (size_t)adj[v * DEG + k] * w;
                for (int j = 0; j < w; j++) dst[j] |= s2[j];
            }
        }
        u64 *t = RA;
        RA = RB;
        RB = t;
    }
    long long tot = 0, dsum = 0;
    for (int v = 0; v < n; v++) {
        const u64 *row = RA + (size_t)v * w;
        int c = 0;
        for (int j = 0; j < w; j++) c += pc64(row[j]);
        tot += n - c;
        dsum += DEG - dg[v];
    }
    *bad = tot / 2;
    *def = dsum;
}

static int try_move(void) {
    int n = N;
    int k = rndint(4);
    if (k == 0) { /* add edge across sides */
        int x = rndint(n), y = rndint(n);
        if (x == y || side[x] == side[y] || dg[x] >= DEG || dg[y] >= DEG || has_edge(x, y))
            return 0;
        add_edge(x, y);
        mkind = 0; ma = x; mb = y;
        return 1;
    }
    if (k == 1) { /* remove edge */
        int x = rndint(n);
        if (dg[x] == 0) return 0;
        int y = adj[x * DEG + rndint(dg[x])];
        rem_edge(x, y);
        mkind = 1; ma = x; mb = y;
        return 1;
    }
    if (k == 2) { /* rewire endpoint y of (x,y) to z on the same side as y */
        int x = rndint(n);
        if (dg[x] == 0) return 0;
        int y = adj[x * DEG + rndint(dg[x])];
        int z = rndint(n);
        if (z == y || side[z] != side[y] || dg[z] >= DEG || has_edge(x, z)) return 0;
        rem_edge(x, y);
        add_edge(x, z);
        mkind = 2; ma = x; mb = y; mc = z;
        return 1;
    }
    /* 2-switch: (x,y),(z,t) -> (x,t),(z,y), with x,z on the same side */
    int x = rndint(n);
    if (dg[x] == 0) return 0;
    int y = adj[x * DEG + rndint(dg[x])];
    int z = rndint(n);
    if (z == x || side[z] != side[x] || dg[z] == 0) return 0;
    int t = adj[z * DEG + rndint(dg[z])];
    if (t == y || has_edge(x, t) || has_edge(z, y)) return 0;
    rem_edge(x, y);
    rem_edge(z, t);
    add_edge(x, t);
    add_edge(z, y);
    mkind = 3; ma = x; mb = y; mc = z; md = t;
    return 1;
}

static void undo_move(void) {
    switch (mkind) {
    case 0:
        rem_edge(ma, mb);
        break;
    case 1:
        add_edge(ma, mb);
        break;
    case 2:
        rem_edge(ma, mc);
        add_edge(ma, mb);
        break;
    default:
        rem_edge(ma, md);
        rem_edge(mc, mb);
        add_edge(ma, mb);
        add_edge(mc, md);
        break;
    }
}

static void record(void) {
    memcpy(badj, adj, sizeof(int) * (size_t)N * (size_t)DEG);
    memcpy(bdg, dg, sizeof(int) * (size_t)N);
    memcpy(bside, side, sizeof(int) * (size_t)N);
    bestN = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    clock_t deadline = clock() + (clock_t)(budget * CLOCKS_PER_SEC);
    if (DEG < 1 || DEG > 200 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    adj = malloc(sizeof(int) * MAXN * DEG);
    badj = malloc(sizeof(int) * MAXN * DEG);
    dg = calloc(MAXN, sizeof(int));
    bdg = calloc(MAXN, sizeof(int));
    side = calloc(MAXN, sizeof(int));
    bside = calloc(MAXN, sizeof(int));
    RA = malloc(sizeof(u64) * MAXN * ((MAXN + 63) / 64));
    RB = malloc(sizeof(u64) * MAXN * ((MAXN + 63) / 64));

    /* read start graph */
    int n0 = 0, m0 = 0, ok = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && n0 <= MAXN - 2 && m0 >= 0) {
        ok = 1;
        N = n0;
        for (int i = 0; i < m0 && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
            if (dg[u] >= DEG || dg[v] >= DEG || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
    }
    if (ok) {
        int *q = malloc(sizeof(int) * MAXN);
        for (int i = 0; i < N; i++) side[i] = -1;
        for (int s = 0; s < N && ok; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int h = 0, t = 0;
            q[t++] = s;
            while (h < t && ok) {
                int x = q[h++];
                for (int k = 0; k < dg[x]; k++) {
                    int y = adj[x * DEG + k];
                    if (side[y] == -1) {
                        side[y] = 1 - side[x];
                        q[t++] = y;
                    } else if (side[y] == side[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        free(q);
    }
    long long bb = 0, bd = 0;
    if (ok) {
        evaluate(&bb, &bd);
        if (bb != 0) ok = 0;
    }
    if (!ok) {
        /* fallback start: K_{DEG,DEG}, valid for DIAM >= 2 */
        N = 2 * DEG;
        for (int i = 0; i < N; i++) { dg[i] = 0; side[i] = (i < DEG) ? 0 : 1; }
        for (int i = 0; i < DEG; i++)
            for (int j = 0; j < DEG; j++)
                add_edge(i, DEG + j);
        evaluate(&bb, &bd);
    }
    if (bb == 0) record();

    const long long CYC = 20000;
    const double T0 = 2.0, T1 = 0.05;
    while (N + 2 <= MAXN && clock() < deadline) {
        side[N] = 0; dg[N] = 0; N++;
        side[N] = 1; dg[N] = 0; N++;
        long long cb = 0, cd = 0;
        evaluate(&cb, &cd);
        long long cur = 4 * cb + cd;
        long long it = 0;
        int success = 0;
        while (clock() < deadline) {
            double frac = (double)(it % CYC) / (double)CYC;
            double T = T0 * pow(T1 / T0, frac);
            it++;
            if (!try_move()) continue;
            long long nb = 0, nd = 0;
            evaluate(&nb, &nd);
            long long nc = 4 * nb + nd;
            long long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nc;
                if (nb == 0) {
                    success = 1;
                    break;
                }
            } else {
                undo_move();
            }
        }
        if (!success) break;
        record();
    }

    int n = bestN, m = 0;
    for (int v = 0; v < n; v++)
        if (bside[v] == 0) m += bdg[v];
    printf("%d %d\n", n, m);
    for (int v = 0; v < n; v++) {
        if (bside[v] != 0) continue;
        for (int k = 0; k < bdg[v]; k++)
            printf("%d %d\n", v, badj[v * DEG + k]);
    }
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    # Start graph: best valid arc-extended PG(2,q) graph (diameter 3, so valid for D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                break

    # Bold change: C annealing grows the graph from the start by vertex pairs.
    elapsed = time.monotonic() - t0
    c_budget = 0.78 * time_limit - elapsed
    if c_budget >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                            stdin_graph=best, timeout=0.9 * time_limit - elapsed)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
