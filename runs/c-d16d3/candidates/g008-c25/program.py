"""Bi-Cayley (group-lift) search for D = 3, with the conic blow-up as a safe fallback.

Construction: for a group G of order N and a set S of d elements, the bipartite graph
with parts G x {A} and G x {B}, and (x, A) ~ (x*s, B) for s in S, is d-regular with
2N vertices. It has diameter 3 exactly when S*S^{-1} = G and S^{-1}*S = G. C searches
for such S by annealing over many groups Z_m x| Z_k, with N just above half the record.
Every graph is verified by BFS before it is reported. Python keeps the best valid start
and only accepts a C result that is larger and passes lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXV (2 * MAXN)
#define MAXE (MAXN * MAXD)

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ---------------------------------------------------------- group Z_m x|_r Z_k */

static int N;                 /* group order */
static int MT[MAXN][MAXN];    /* multiplication table, identity is 0 */
static int INV[MAXN];         /* inverses */

static void build_group(int m, int k, int r) {
    int rp[MAXN];
    N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

static int cand_m[4096], cand_k[4096], cand_r[4096];
static int random_group(int n, int *pm, int *pk, int *pr) {
    int nc = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (nc < 4096) { cand_m[nc] = m; cand_k[nc] = k; cand_r[nc] = r; nc++; }
        }
    }
    if (!nc) return 0;
    int i = rndint(nc);
    *pm = cand_m[i]; *pk = cand_k[i]; *pr = cand_r[i];
    return 1;
}

/* ---------------------------------------------------------- covering objective */

static int S[MAXD];
static int cov1[MAXN], cov2[MAXN];

/* Number of group elements missing from S*S^{-1} plus those missing from S^{-1}*S. */
static int uncovered(void) {
    memset(cov1, 0, sizeof(int) * N);
    memset(cov2, 0, sizeof(int) * N);
    cov1[0] = 1;
    cov2[0] = 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            if (i == j) continue;
            cov1[MT[S[i]][INV[S[j]]]] = 1;
            cov2[MT[INV[S[i]]][S[j]]] = 1;
        }
    int u = 0;
    for (int g = 0; g < N; g++) u += (!cov1[g]) + (!cov2[g]);
    return u;
}

static int in_set(int g, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == g) return 1;
    return 0;
}

/* Simulated annealing on S (with S[0] = identity, WLOG). Returns 1 if covered,
 * 0 if steps ran out, -1 on time-out. */
static int anneal(long steps) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int g;
        do { g = rndint(N); } while (in_set(g, i));
        S[i] = g;
    }
    int cur = uncovered();
    double T = 0.6;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 1023) == 0 && now() > t_end) return -1;
        int k = 1 + rndint(d - 1);
        int g = rndint(N);
        if (in_set(g, d)) continue;
        int old = S[k];
        S[k] = g;
        int nv = uncovered();
        if (nv <= cur || rnd01() < exp((cur - nv) / T)) cur = nv;
        else S[k] = old;
    }
    return cur == 0;
}

/* ---------------------------------------------------------- graph + check */

static int eu[MAXE], ev[MAXE], ecount;
static int adj[MAXV][MAXD], deg[MAXV];

static void build_graph(void) {
    for (int v = 0; v < 2 * N; v++) deg[v] = 0;
    ecount = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            int y = N + MT[x][S[i]];
            eu[ecount] = x;
            ev[ecount] = y;
            ecount++;
            adj[x][deg[x]++] = y;
            adj[y][deg[y]++] = x;
        }
}

/* BFS from every vertex: all vertices must be reached within D steps. */
static int diam_ok(int nv) {
    static int dist[MAXV], queue[MAXV];
    for (int v = 0; v < nv; v++)
        if (deg[v] > d) return 0;
    for (int s = 0; s < nv; s++) {
        for (int v = 0; v < nv; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s] = 0;
        queue[t++] = s;
        while (h < t) {
            int v = queue[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    queue[t++] = u;
                }
            }
        }
        if (t != nv) return 0;
    }
    return 1;
}

static int bestEu[MAXE], bestEv[MAXE], bestEc, bestNv;

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit have_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long have = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 3 || d > MAXD) { printf("0 0\n"); return 0; }
    long half = 1 + (long)(d - 1) * d;   /* Moore bound for D = 3 is 2*half */
    if (have >= 2 * half) { printf("0 0\n"); return 0; }

    long nmin = have / 2 + 1;
    if (nmin < d + 1) nmin = d + 1;
    bestNv = 0;
    bestEc = 0;

    while (now() < t_end) {
        if (nmin > half || nmin > MAXN) break;
        long hi = nmin + 6 < half ? nmin + 6 : half;
        if (hi > MAXN) hi = MAXN;
        int n = (int)(nmin + rndint((int)(hi - nmin + 1)));
        int m, k, r;
        if (!random_group(n, &m, &k, &r)) { nmin++; continue; }
        build_group(m, k, r);
        int ok = anneal(200000);
        if (ok < 0) break;
        if (ok == 1) {
            build_graph();
            if (2 * N > have && 2 * N > bestNv && diam_ok(2 * N)) {
                bestNv = 2 * N;
                bestEc = ecount;
                memcpy(bestEu, eu, sizeof(int) * ecount);
                memcpy(bestEv, ev, sizeof(int) * ecount);
            }
            if (N + 1 > nmin) nmin = N + 1;
        }
    }

    if (bestNv > 0) {
        printf("%d %d\n", bestNv, bestEc);
        for (int e = 0; e < bestEc; e++) printf("%d %d\n", bestEu[e], bestEv[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def conic_blowup(d, D):
    """Twin-blow-up of PG(2,q) with q = d-3 odd, using a conic and a dual conic.

    Gives 2(q^2+q+1) + 2(q+1) vertices, which is 394 for q = 13 (d = 16).
    """
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


def starts(d, D):
    """Candidate structured start graphs (validity is checked by the caller)."""
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = None
    for cand in starts(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (start is None or cand[0] > start[0]):
            start = cand
    best = start if start is not None else lib.haar_graph(d, range(d))  # K_{d,d}: always valid

    if D == 3 and d >= 3 and best[0] < lib.moore_bound(d, D):
        remaining = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
        if remaining > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best[0]],
                                 stdin_graph=None, timeout=remaining + 8)
                out = lib.parse_graph_text(text)
                if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                    best = out
            except Exception:
                pass   # keep the valid structured fallback
    return best
