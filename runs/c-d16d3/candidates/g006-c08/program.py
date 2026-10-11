"""Haar-graph difference-covering search for D = 3 bipartite graphs.

Construction: for a cyclic group Z_m and a set S of d residues, the Haar graph H(Z_m, S) has
parts a_i, b_i with a_i ~ b_j iff j - i is in S. It is d-regular and bipartite with 2m vertices.
Its diameter is at most 3 whenever S - S covers every residue of Z_m: same-side pairs share a
neighbour, and a_i to b_j is reached by a path a_i, b_(i+s1), a_(i+s1-s2), b_j with j - i in S - S + S = Z_m.
So the task is to find a d-subset S of Z_m covering Z_m by differences, with m as large as possible.
For d = 16 this is a valid graph with 2m vertices, and m >= 198 would beat the 394 record.

The C search runs simulated annealing on the number of uncovered differences, and grows m by one
each time it succeeds. The previous structured starts (projective plane, conic blow-up) remain as
validated fallbacks, and every result is checked with lib.is_valid before it is returned.
"""
import time

import lib

C_COVER = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 64
#define MAXM 4096

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

static int K, M;               /* set size and modulus */
static int S[MAXK];            /* current set; S[0] is fixed at 0 */
static unsigned char inS[MAXM];
static int cnt[MAXM];          /* cnt[x] = ordered pairs (s, t) in S with s - t = x (x != 0) */
static int uncovered;          /* number of nonzero residues with cnt = 0 */

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void cnt_add(int x, int delta) {
    if (x == 0) return;
    if (delta > 0) {
        if (cnt[x]++ == 0) uncovered--;
    } else {
        if (--cnt[x] == 0) uncovered++;
    }
}

/* Add (delta = +1) or remove (delta = -1) all pairs between element a and the other members S[j], j != skip. */
static void pairs_update(int a, int skip, int delta) {
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        int b = S[j];
        cnt_add(md(a - b), delta);
        cnt_add(md(b - a), delta);
    }
}

static void rebuild(void) {
    memset(cnt, 0, sizeof cnt);
    memset(inS, 0, sizeof inS);
    uncovered = M - 1;
    for (int i = 0; i < K; i++) inS[S[i]] = 1;
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            cnt_add(md(S[i] - S[j]), 1);
            cnt_add(md(S[j] - S[i]), 1);
        }
}

static void random_set(void) {
    memset(inS, 0, sizeof inS);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int b;
        do b = rndint(M); while (inS[b]);
        S[i] = b;
        inS[b] = 1;
    }
    rebuild();
}

/* One annealing run for the current M. Returns 1 if S - S covers Z_M. */
static int anneal(double until, long maxit) {
    random_set();
    const double T0 = 1.0, T1 = 0.08;
    for (long it = 0; it < maxit; it++) {
        if (uncovered == 0) return 1;
        if ((it & 4095) == 0 && now() > until) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);
        int i = 1 + rndint(K - 1);
        int b = rndint(M);
        if (inS[b]) continue;
        int old = S[i];
        int before = uncovered;
        pairs_update(old, i, -1);
        S[i] = b;
        pairs_update(b, i, 1);
        int delta = uncovered - before;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[b] = 1;
        } else {
            pairs_update(b, i, -1);
            S[i] = old;
            pairs_update(old, i, 1);
        }
    }
    return uncovered == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t_end = now() + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 2 || d > MAXK) {
        printf("0 0\n");
        return 0;
    }
    K = d;
    int bestM = 0;
    int bestS[MAXK];
    for (M = 2 * K; M < MAXM && now() < t_end; M++) {
        long maxit = 3000000L + 20000L * M;
        int ok = 0;
        while (!ok && now() < t_end) ok = anneal(t_end, maxit);
        if (!ok) break;
        bestM = M;
        memcpy(bestS, S, sizeof(int) * K);
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    /* Haar graph: a_i = i, b_j = bestM + j, a_i ~ b_{i+s} for s in the cover set. */
    printf("%d %ld\n", 2 * bestM, (long)bestM * K);
    for (int i = 0; i < bestM; i++)
        for (int t = 0; t < K; t++)
            printf("%d %d\n", i, bestM + (i + bestS[t]) % bestM);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, using a conic and a dual conic. Gives 394 for d = 16."""
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
    n0, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
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
    """Structured fallback graphs (each validity-checked before use)."""
    out = []
    for fn in (known_start, conic_blowup):
        try:
            g = fn(d, D)
        except Exception:
            g = None
        if g is not None:
            out.append(g)
    return out


def haar_cover_search(d, D, seed, budget):
    """Run the C difference-covering search; returns (n, edges), possibly (0, [])."""
    text = lib.run_c(C_COVER, [d, D, seed, round(budget, 2)], stdin_graph=None,
                     timeout=budget + 4)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    best = None
    for cand in starts(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (best is None or cand[0] > best[0]):
            best = cand
    if best is None:
        best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2

    if D == 3 and best[0] < lib.moore_bound(d, D):
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.5
        if budget > 1.0:
            try:
                out = haar_cover_search(d, D, seed, budget)
                if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                    best = out
            except Exception:
                pass  # keep the valid structured fallback

    return best
