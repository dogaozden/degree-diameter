import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP 2048
#define WCAP ((NCAP + 63) / 64)
#define ITERS 15000
#define MI(a, b) M[(size_t)(a) * NCAP + (size_t)(b)]

typedef uint64_t u64;

static int DEG, DIST, N, W, bestN = -1;
static int side[NCAP], degv[NCAP], bside[NCAP], bdeg[NCAP];
static int *adjv, *badj;
static unsigned char *M;
static u64 *RA, *RB;
static u64 rs;
static double budget;

static u64 rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndint(int k) { return (int)(rnd() % (u64)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v, w) with dist(v, w) > DIST. Zero means valid. */
static long long cost_eval(void) {
    int n = N, w = W;
    u64 *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(u64) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < DIST; it++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * w;
            const u64 *src = cur + (size_t)v * w;
            for (int j = 0; j < w; j++) dst[j] = src[j];
            for (int k = 0; k < degv[v]; k++) {
                const u64 *s2 = cur + (size_t)adjv[v * DEG + k] * w;
                for (int j = 0; j < w; j++) dst[j] |= s2[j];
            }
        }
        u64 *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const u64 *s = cur + (size_t)v * w;
        int c = 0;
        for (int j = 0; j < w; j++) c += popc(s[j]);
        bad += n - c;
    }
    return bad;
}

static void add_edge(int a, int b) {
    adjv[a * DEG + degv[a]++] = b;
    adjv[b * DEG + degv[b]++] = a;
    MI(a, b) = 1;
    MI(b, a) = 1;
}

static void del_one(int v, int u) {
    int dv = degv[v];
    for (int k = 0; k < dv; k++) {
        if (adjv[v * DEG + k] == u) {
            adjv[v * DEG + k] = adjv[v * DEG + dv - 1];
            degv[v] = dv - 1;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
    MI(a, b) = 0;
    MI(b, a) = 0;
}

static void save_best(void) {
    bestN = N;
    memcpy(bside, side, sizeof(int) * (size_t)N);
    memcpy(bdeg, degv, sizeof(int) * (size_t)N);
    memcpy(badj, adjv, sizeof(int) * (size_t)N * DEG);
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++)
        for (int k = 0; k < degv[v]; k++) MI(v, adjv[v * DEG + k]) = 0;
}

static void restore_best(void) {
    clear_graph();
    N = bestN;
    W = (N + 63) / 64;
    memcpy(side, bside, sizeof(int) * (size_t)N);
    memcpy(degv, bdeg, sizeof(int) * (size_t)N);
    memcpy(adjv, badj, sizeof(int) * (size_t)N * DEG);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < degv[v]; k++) MI(v, adjv[v * DEG + k]) = 1;
}

static int grow_one(void) {
    if (N >= NCAP - 1) return 0;
    side[N] = rndint(2);
    degv[N] = 0;
    N++;
    W = (N + 63) / 64;
    return 1;
}

static int accept(long long nc, long long c, double T) {
    if (nc <= c) return 1;
    return rnd01() < exp(-(double)(nc - c) / T);
}

/* One proposed move; keeps the move if accepted, otherwise undoes it. */
static void sa_move(long long *cost, double T) {
    int r = rndint(100);
    long long nc;
    if (r < 55) {
        int a1 = rndint(N), a2 = rndint(N);
        if (side[a1] != 0 || side[a2] != 0 || degv[a1] == 0 || degv[a2] == 0) return;
        int b1 = adjv[a1 * DEG + rndint(degv[a1])];
        int b2 = adjv[a2 * DEG + rndint(degv[a2])];
        if (a1 == a2 || b1 == b2 || MI(a1, b2) || MI(a2, b1)) return;
        del_edge(a1, b1);
        del_edge(a2, b2);
        add_edge(a1, b2);
        add_edge(a2, b1);
        nc = cost_eval();
        if (accept(nc, *cost, T)) {
            *cost = nc;
        } else {
            del_edge(a1, b2);
            del_edge(a2, b1);
            add_edge(a1, b1);
            add_edge(a2, b2);
        }
    } else if (r < 85) {
        int a = (rnd01() < 0.5) ? N - 1 : rndint(N);
        int b = rndint(N);
        if (side[a] == side[b] || degv[a] >= DEG || degv[b] >= DEG || MI(a, b)) return;
        add_edge(a, b);
        nc = cost_eval();
        if (accept(nc, *cost, T)) *cost = nc;
        else del_edge(a, b);
    } else {
        int a = rndint(N);
        if (degv[a] == 0) return;
        int b = adjv[a * DEG + rndint(degv[a])];
        del_edge(a, b);
        nc = cost_eval();
        if (accept(nc, *cost, T)) *cost = nc;
        else add_edge(a, b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIST = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    if (d < 1 || DIST < 1) {
        printf("0 0\n");
        return 0;
    }
    DEG = d;
    adjv = malloc(sizeof(int) * (size_t)NCAP * DEG);
    badj = malloc(sizeof(int) * (size_t)NCAP * DEG);
    M = calloc((size_t)NCAP * NCAP, 1);
    RA = malloc(sizeof(u64) * (size_t)NCAP * WCAP);
    RB = malloc(sizeof(u64) * (size_t)NCAP * WCAP);
    if (!adjv || !badj || !M || !RA || !RB) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    int bad = 0;
    if (n0 == 0) {
        if (2 * d > NCAP - 64) {
            printf("0 0\n");
            return 0;
        }
        N = 2 * d;
        for (int v = 0; v < N; v++) side[v] = (v >= d);
        for (int a = 0; a < d; a++)
            for (int b = d; b < N; b++) add_edge(a, b);
    } else {
        if (n0 > NCAP - 64 || m0 < 0) {
            printf("0 0\n");
            return 0;
        }
        N = n0;
        for (int k = 0; k < m0 && !bad; k++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                bad = 1;
                break;
            }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) {
                bad = 1;
                break;
            }
            if (MI(u, v) || degv[u] >= DEG || degv[v] >= DEG) {
                bad = 1;
                break;
            }
            add_edge(u, v);
        }
        if (bad) {
            printf("0 0\n");
            return 0;
        }
        int *stack = malloc(sizeof(int) * (size_t)N);
        if (!stack) {
            printf("0 0\n");
            return 0;
        }
        for (int v = 0; v < N; v++) side[v] = -1;
        for (int s = 0; s < N; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int sp = 0;
            stack[sp++] = s;
            while (sp > 0) {
                int x = stack[--sp];
                for (int k = 0; k < degv[x]; k++) {
                    int y = adjv[x * DEG + k];
                    if (side[y] < 0) {
                        side[y] = 1 - side[x];
                        stack[sp++] = y;
                    } else if (side[y] == side[x]) {
                        bad = 1;
                    }
                }
            }
        }
        free(stack);
        if (bad) {
            printf("0 0\n");
            return 0;
        }
    }

    W = (N + 63) / 64;
    long long cost = cost_eval();
    if (cost == 0) save_best();

    while (now() < budget) {
        if (bestN >= 0) {
            restore_best();
            if (!grow_one()) break;
        }
        cost = cost_eval();
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 255) == 0 && now() >= budget) break;
            double T = 3.0 * pow(0.01, (double)it / ITERS) + 0.05;
            sa_move(&cost, T);
        }
        if (cost == 0) save_best();
    }

    if (bestN < 0) {
        printf("0 0\n");
        return 0;
    }
    long long m = 0;
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bdeg[v]; k++)
            if (badj[v * DEG + k] > v) m++;
    printf("%d %lld\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[v * DEG + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


_LS_ITERS = 30000


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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
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
    """Arc-extended projective plane graphs (diameter 3); each candidate is (n, edges)."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Diameter-3 starts: projective planes and arc extensions (valid for all D >= 3).
    if D >= 3:
        qs = sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)
        for q in qs[:2]:
            consider(*lib.projective_plane_incidence(q))
        cands = _arc_extensions(d, t0 + 0.3 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in cands:
            consider(n_c, e_c)

    # Growth search in C: repeatedly add one vertex and repair by edge swaps
    # and simulated annealing on the number of pairs at distance > D.
    if best_n < lib.moore_bound(d, D):
        elapsed = time.monotonic() - t0
        budget = 0.72 * time_limit - elapsed - 2.0
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=budget + 0.12 * time_limit)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
