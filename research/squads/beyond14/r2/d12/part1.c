/* hmeta: Haar graphs H(G,S) of metacyclic groups G = Z_m x|_r Z_k with a bit-parallel BFS, random-S annealing.
 * Job beyond-d13 (2026-11-01, director). Made for odd-order groups at odd D (no involutions, trivial centre when m is
 * prime: research/squads/beyond13/r2/e11/ODD_ORDER.md), at sizes haar_gen3's generic evaluation cannot reach.
 *
 * Group: (a,j)(b,l) = (a + r^j b mod m, j + l mod k), r^k = 1 mod m, gcd(r,m) = 1. Index of (a,j) = a k + j.
 * Graph: vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S, e in S, |S| = d (haar_gen3 convention).
 * Evaluation in inverse coordinates x = g^-1: A-vertex x ~ B-vertex x s^-1. So from (e,A) the B-levels are X S^-1 and
 * the A-levels Y S; from (e,B) the A-levels are Y S and the B-levels X S^-1 (right multiplications only). Right
 * multiplication by t = (ta,tj) maps row j to row j + tj and rotates it: a -> a + r^j ta. So one BFS level is, for each
 * target row J and generator t, one rotated OR of a whole m-bit row (rows are stored twice for window reads).
 * cost: D even: #B-side elements not within D-1 of (e,A) (0 => diameter <= D, as in haar_big);
 *       D odd : #A not within D-1 of (e,A) + #B not within D-1 of (e,B) (0 => diameter <= D).
 * Search: S = {e} + d-1 random elements; a move replaces one generator by the best of K candidates (exact
 * evaluation; TARGP % (70) of them targeted: a random word of length D-1 from e, with the replaced generator at a random
 * position, is forced to end at a random hole of the current S, as in haar_big), Metropolis on cost with T from T0 to T1 (geometric in time); restart from the best after REHEAT moves
 * without gain.
 * Usage: hmeta d D seconds seed K outfile m k r       env THREADS (OpenMP), T0 (2), T1 (0.2), REHEAT (40), START=file
 *        (solution file to start from), EVAL=file (print the cost of a solution file and exit).
 * Output: haar_gen3-format solution "d D meta m k r n 1 N <N>" + d lines "<idx> meta(a=A,j=J) z=0" (first = e), written
 * when cost 0 is reached; <outfile>.best after every improvement. Check with research/frontier/beyond13/metacheck.py
 * (independent numpy BFS) or meta/hmetacheck.c (independent C BFS, different code).
 * Build: gcc -O3 -march=native -fopenmp -o hmeta hmeta.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <omp.h>
typedef uint64_t u64; typedef int64_t i64;
static i64 M, K_, R_, N; static int d, D;
static i64 *RP;               /* RP[j] = r^j mod m */
static i64 W, W2;             /* words per row (m bits), words per doubled row (2m bits + pad) */
static u64 *SA, *SB, *DBL;    /* current set (k rows of W words), next set, doubled source */
static i64 lastA = 0, lastB = 0;
static u64 *HA, *HB;          /* final reached sets of the last evaluation: side A run, side B run (for targeting) */
static u64 rs = 88172645463325252ULL;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
typedef struct { i64 a, j; } el;
static i64 mpow(i64 b, i64 e, i64 m) { i64 x = 1 % m; b %= m; while (e) { if (e & 1) x = (__int128)x * b % m; b = (__int128)b * b % m; e >>= 1; } return x; }
static el inv(el x) { i64 jj = (K_ - x.j) % K_; el y = { (M - (__int128)RP[jj] * x.a % M) % M, jj }; return y; }
static u64 lastmask;
/* doubled copy of row j of src into DBL row j: bits [0,m) and [m,2m) */
static void make_dbl(const u64 *src) {
    #pragma omp parallel for schedule(static)
    for (i64 j = 0; j < K_; j++) {
        const u64 *s = src + j * W; u64 *t = DBL + j * W2;
        memset(t, 0, W2 * 8);
        memcpy(t, s, W * 8);
        i64 off = M; i64 q = off >> 6; int sh = off & 63;
        for (i64 w = 0; w < W; w++) {
            u64 v = s[w]; if (w == W - 1) v &= lastmask;
            t[q + w] |= sh ? (v << sh) : v;
            if (sh) t[q + w + 1] |= v >> (64 - sh);
        }
    }
}
/* dst row |= src row rotated by c: dst bit i = src bit (i - c mod m) = DBL bit (i + m - c) */
static inline void or_rot(u64 *dst, const u64 *dbl, i64 c) {
    i64 o = M - c; if (o <= 0) o += M;  /* o in (0, m] */
    i64 q = o >> 6; int sh = o & 63;
    if (sh == 0) for (i64 w = 0; w < W; w++) dst[w] |= dbl[q + w];
    else for (i64 w = 0; w < W; w++) dst[w] |= (dbl[q + w] >> sh) | (dbl[q + w + 1] << (64 - sh));
}
/* one step: dst = src * T (right multiplication by each generator in T) */
static void step(u64 *dst, const u64 *src, const el *T, int nt) {
    make_dbl(src);
    #pragma omp parallel for schedule(dynamic, 1)
    for (i64 J = 0; J < K_; J++) {
        u64 *t = dst + J * W; memset(t, 0, W * 8);
        for (int g = 0; g < nt; g++) {
            i64 j = ((J - T[g].j) % K_ + K_) % K_;
            i64 c = (__int128)RP[j] * T[g].a % M;
            or_rot(t, DBL + j * W2, c);
        }
        t[W - 1] &= lastmask;
    }
}
static i64 popc(const u64 *x) { i64 c = 0;
    #pragma omp parallel for reduction(+:c)
    for (i64 i = 0; i < K_ * W; i++) c += __builtin_popcountll(x[i]);
    return c; }
static el S[64], SI[64];
/* run D-1 steps from e on side `side` (0 = A: first step uses S^-1; 1 = B: first step uses S); return #reached on the
 * side reached after D-1 steps */
static i64 ball(int side) {
    memset(SA, 0, K_ * W * 8); SA[0] = 1;   /* element (0,0) = bit 0 of row 0 */
    u64 *cur = SA, *nx = SB; int useinv = (side == 0);
    for (int s = 0; s < D - 1; s++) {
        step(nx, cur, useinv ? SI : S, d);
        u64 *t = cur; cur = nx; nx = t; useinv = !useinv;
    }
    memcpy(side == 0 ? HA : HB, cur, K_ * W * 8);
    return popc(cur);
}
static el emul(el x, el y) { el z = { (x.a + (__int128)RP[x.j] * y.a) % M, (x.j + y.j) % K_ }; return z; }
/* a random hole of the last evaluation: side 0 = not reached from (e,A), 1 = from (e,B); returns 0 if none found */
static int hole(int side, el *u) {
    const u64 *H = side == 0 ? HA : HB;
    for (int tries = 0; tries < 64; tries++) {
        i64 j = rnd() % K_, w0 = rnd() % W;
        for (i64 w = w0, c = 0; c < W; c++, w = (w + 1) % W) {
            u64 v = ~H[j * W + w]; if (w == W - 1) v &= lastmask;
            if (v) { int b = __builtin_ctzll(v); u->a = w * 64 + b; u->j = j; return 1; }
        }
    }
    return 0;
}
