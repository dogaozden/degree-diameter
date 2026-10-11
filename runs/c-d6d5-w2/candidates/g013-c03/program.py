"""Haar graphs over finite groups, searched by simulated annealing.

A Haar graph over a group G with connection set S (|S| = d, identity in S) has
vertices (g,0) and (g,1) for g in G. Edge (g,0)-(g*s,1) for s in S. Left
multiplication is an automorphism, so diameter <= D iff BFS of depth D from
(e,0) and from (e,1) covers the graph. The C engine receives group
multiplication tables (permutation groups PSL(2,q) and S6, plus a few cyclic
groups) and searches connection sets for a zero-uncovered configuration, with
simulated annealing and random restarts across groups.

Safe fallbacks: K_{d,d} and the projective-plane incidence graph. Every returned
graph is checked with lib.is_valid.
"""
import time

import numpy as np

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 32
#define ITERS 20000

static uint64_t rs0, rs1;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs0;
    const uint64_t s0 = rs1;
    rs0 = s0;
    s1 ^= s1 << 23;
    rs1 = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs1 + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static struct timespec T0;

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM, NG, maxN2, curN, curE, curst;
static int gN[MAXG], gE[MAXG];
static int *gmul[MAXG], *ginv[MAXG];
static int *Mu, *Inv;
static int *stamp, *fr, *nx, *sel, *sinv;

static int has_sel(int x, int m) {
    for (int k = 0; k < m; k++)
        if (sel[k] == x) return 1;
    return 0;
}

/* Uncovered vertices (both block representatives, within DIAM). */
static int cost_of(void) {
    const int N = curN;
    int tot = 0;
    if (curst > 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)maxN2);
        curst = 0;
    }
    for (int r = 0; r < 2; r++) {
        int src = (r == 0) ? curE : N + curE;
        curst++;
        int *f = fr, *h = nx;
        int fs = 1, count = 1;
        f[0] = src;
        stamp[src] = curst;
        for (int lvl = 0; lvl < DIAM && fs > 0; lvl++) {
            int ns = 0;
            for (int q = 0; q < fs; q++) {
                int x = f[q];
                if (x < N) {
                    const int *row = Mu + (size_t)x * N;
                    for (int k = 0; k < DEG; k++) {
                        int v = N + row[sel[k]];
                        if (stamp[v] != curst) {
                            stamp[v] = curst;
                            h[ns++] = v;
                        }
                    }
                } else {
                    const int *row = Mu + (size_t)(x - N) * N;
                    for (int k = 0; k < DEG; k++) {
                        int v = row[sinv[k]];
                        if (stamp[v] != curst) {
                            stamp[v] = curst;
                            h[ns++] = v;
                        }
                    }
                }
            }
            count += ns;
            int *t = f;
            f = h;
            h = t;
            fs = ns;
        }
        tot += 2 * N - count;
    }
    return tot;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs0 = splitmix(&sm);
    rs1 = splitmix(&sm);

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) { hn = 0; hm = 0; }
    if (hn < 0) hn = 0;
    if (hn > MAXG) hn = MAXG;
    if (hm < 0) hm = 0;
    size_t cnt = (size_t)hm * 2;
    int *A = malloc(sizeof(int) * (cnt + 1));
    for (size_t i = 0; i < cnt; i++) {
        if (scanf("%d", &A[i]) != 1) {
            cnt = i;
            break;
        }
    }

    NG = 0;
    int maxN = 0;
    size_t p = 0;
    for (int g = 0; g < hn; g++) {
        if (p + 2 > cnt) break;
        int N = A[p], e = A[p + 1];
        if (N < 1 || N > 4000 || e < 0 || e >= N) break;
        if (p + 2 + (size_t)N * N > cnt) break;
        p += 2;
        gN[NG] = N;
        gE[NG] = e;
        gmul[NG] = malloc(sizeof(int) * (size_t)N * N);
        memcpy(gmul[NG], A + p, sizeof(int) * (size_t)N * N);
        p += (size_t)N * N;
        ginv[NG] = malloc(sizeof(int) * (size_t)N);
        for (int a = 0; a < N; a++) ginv[NG][a] = -1;
        for (int a = 0; a < N; a++)
            for (int b = 0; b < N; b++)
                if (gmul[NG][(size_t)a * N + b] == e) ginv[NG][a] = b;
        NG++;
        if (N > maxN) maxN = N;
    }
    free(A);

    if (NG == 0 || DEG < 2 || DIAM < 1 || maxN < DEG) {
        printf("0 0\n");
        return 0;
    }

    maxN2 = 2 * maxN;
    stamp = calloc((size_t)maxN2, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)maxN2);
    nx = malloc(sizeof(int) * (size_t)maxN2);
    sel = malloc(sizeof(int) * (size_t)DEG);
    sinv = malloc(sizeof(int) * (size_t)DEG);
    int *bestsel = malloc(sizeof(int) * (size_t)DEG);
    int bestg = -1;
    int best_n = start_n;
    int cand[MAXG];
    curst = 0;

    while (elapsed() < limit) {
        int nc = 0;
        for (int g = 0; g < NG; g++)
            if (2 * gN[g] > best_n && gN[g] >= DEG) cand[nc++] = g;
        if (nc == 0) break;
        int ga = cand[rnd_int(nc)];
        curN = gN[ga];
        curE = gE[ga];
        Mu = gmul[ga];
        Inv = ginv[ga];
        int N = curN, e = curE;

        sel[0] = e;
        for (int k = 1; k < DEG; k++) {
            int x;
            do {
                x = rnd_int(N);
            } while (has_sel(x, k));
            sel[k] = x;
        }
        for (int k = 0; k < DEG; k++) sinv[k] = Inv[sel[k]];

        int c = cost_of();
        int ok = (c == 0);
        for (int it = 0; it < ITERS && !ok; it++) {
            if ((it & 127) == 0 && elapsed() > limit) break;
            double T = 4.0 * (1.0 - (double)it / ITERS) + 0.05;
            int k = 1 + rnd_int(DEG - 1);
            int old = sel[k];
            int x;
            do {
                x = rnd_int(N);
            } while (has_sel(x, DEG));
            sel[k] = x;
            sinv[k] = Inv[x];
            int c2 = cost_of();
            int delta = c2 - c;
            if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
                c = c2;
                if (c == 0) ok = 1;
            } else {
                sel[k] = old;
                sinv[k] = Inv[old];
            }
        }
        if (ok) {
            best_n = 2 * N;
            bestg = ga;
            memcpy(bestsel, sel, sizeof(int) * (size_t)DEG);
        }
    }

    if (bestg < 0) {
        printf("0 0\n");
        return 0;
    }
    int N = gN[bestg];
    const int *mt = gmul[bestg];
    printf("%d %d\n", 2 * N, N * DEG);
    for (int g = 0; g < N; g++)
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", g, N + mt[(size_t)g * N + bestsel[k]]);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _perm_group(gens, limit=1500):
    """Closure of permutation generators. Returns (N, table) with table[i][j] = index of a_i then a_j; identity is 0."""
    k = len(gens[0])
    e = tuple(range(k))
    elems = [e]
    idx = {e: 0}
    frontier = [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[i] for i in x)  # apply x first, then g
                if y not in idx:
                    idx[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
                    if len(elems) > limit:
                        return None
        frontier = nxt
    N = len(elems)
    P = np.array(elems, dtype=np.int64)
    w = np.array([k ** i for i in range(k)], dtype=np.int64)
    codes = P @ w
    order = np.argsort(codes)
    sc = codes[order]
    table = np.empty((N, N), dtype=np.int64)
    for i in range(N):
        M = P[:, P[i]]  # row j = a_i then a_j
        table[i] = order[np.searchsorted(sc, M @ w)]
    return N, table


def _psl2_gens(q):
    """Permutation generators of PSL(2,q) acting on the q+1 points of the projective line."""
    F = lib.GF(q)
    w = F.primitive_element()
    winv = F.inv(w)
    mats = [(1, t, 0, 1) for t in range(1, q)]
    mats += [(w, 0, 0, winv), (0, F.neg(1), 1, 0)]
    gens = []
    for a, b, c, dd in mats:
        perm = []
        for p in range(q + 1):
            x, y = (1, 0) if p == q else (p, 1)
            u = F.add(F.mul(a, x), F.mul(b, y))
            v = F.add(F.mul(c, x), F.mul(dd, y))
            perm.append(q if v == 0 else F.mul(u, F.inv(v)))
        gens.append(tuple(perm))
    return gens


def _candidate_tables(d, moore, best_n):
    """Group tables (N, table) whose Haar graph could beat best_n and stay within the Moore bound."""
    lo = best_n // 2 + 1
    hi = min(moore // 2, 1400)
    if lo > hi:
        return []
    specs = [(720, lambda: _perm_group([(1, 0, 2, 3, 4, 5), (1, 2, 3, 4, 5, 0)]))]
    for q in (7, 8, 9, 11, 13):
        if not lib.is_prime_power(q):
            continue
        order = q * (q * q - 1) // (2 if q % 2 else 1)
        specs.append((order, lambda q=q: _perm_group(_psl2_gens(q))))
    out = []
    for N, f in specs:
        if lo <= N <= hi and N >= d and len(out) < 8:
            r = f()
            if r is not None:
                out.append(r)
    for m in list(range(hi, max(lo, d) - 1, -1))[:2]:
        idx = np.arange(m, dtype=np.int64)
        out.append((m, (idx[:, None] + idx[None, :]) % m))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore or d < 2 or D < 2:
        return best

    remaining = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if remaining >= 2.0:
        try:
            tables = _candidate_tables(d, moore, best_n)
            if tables:
                flat = []
                for N, table in tables:
                    flat += [N, 0]
                    flat += table.ravel().tolist()
                if len(flat) % 2:
                    flat.append(0)
                pairs = list(zip(flat[0::2], flat[1::2]))
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                                stdin_graph=(len(tables), pairs),
                                timeout=remaining + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
