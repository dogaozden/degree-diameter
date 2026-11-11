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
    i64 j0 = rnd() % K_, w0 = rnd() % W;   /* f09: scan every row (a random start), so a unique hole is always found */
    for (i64 jj = 0; jj < K_; jj++) { i64 j = (j0 + jj) % K_;
        for (i64 c = 0, w = w0; c < W; c++, w = (w + 1) % W) {
            u64 v = ~H[j * W + w]; if (w == W - 1) v &= lastmask;
            if (v) { int b = __builtin_ctzll(v); u->a = w * 64 + b; u->j = j; return 1; }
        } }
    return 0;
}
/* targeted candidate for slot i: a word of length D-1 from e on `side` ending at hole u, with generator i at a random
 * position and the other letters random from S \ {s_i}; returns the generator value that makes the word end at u */
static el target(int i, int side, el u) {
    int L = D - 1, p = 1 + rnd() % L; el x = {0, 0}, z = {0, 0};
    for (int q = 1; q <= L; q++) {
        if (q == p) continue;
        int g; do g = rnd() % d; while (g == i);
        int useinv = (side == 0) ? (q & 1) : !(q & 1);
        el t = useinv ? SI[g] : S[g];
        if (q < p) x = emul(x, t); else z = emul(z, t);
    }
    el tp = emul(emul(inv(x), u), inv(z));        /* x tp z = u */
    int useinv = (side == 0) ? (p & 1) : !(p & 1);
    return useinv ? inv(tp) : tp;
}
static i64 cost(void) {
    for (int i = 0; i < d; i++) SI[i] = inv(S[i]);
    if (D % 2 == 0) { lastA = N - ball(0); lastB = 0; return lastA; }
    lastA = N - ball(0); lastB = N - ball(1); return lastA + lastB;
}
static void writesol(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d %d meta %lld %lld %lld n 1 N %lld\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N);
    for (int i = 0; i < d; i++) fprintf(f, "%lld meta(a=%lld,j=%lld) z=0\n", (long long)(S[i].a * K_ + S[i].j), (long long)S[i].a, (long long)S[i].j);
    fclose(f);
}
static int readsol(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0; char line[512]; if (!fgets(line, sizeof line, f)) return 0;
    int n = 0; long long a, j;
    while (n < d && fgets(line, sizeof line, f)) { char *p = strstr(line, "meta(a="); if (!p) continue;
        if (sscanf(p, "meta(a=%lld,j=%lld)", &a, &j) == 2) { S[n].a = a % M; S[n].j = j % K_; n++; } }
    fclose(f); return n == d;
}
static el rel(void) { el x; do { x.a = rnd() % M; x.j = rnd() % K_; } while (x.a == 0 && x.j == 0); return x; }
static int distinct(int i) { for (int t = 0; t < d; t++) if (t != i && S[t].a == S[i].a && S[t].j == S[i].j) return 0; return 1; }
int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: hmeta d D seconds seed K outfile m k r\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); double secs = atof(argv[3]); rs ^= (u64)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int Kc = atoi(argv[5]); const char *out = argv[6]; M = atoll(argv[7]); K_ = atoll(argv[8]); R_ = atoll(argv[9]);
    if (mpow(R_, K_, M) != 1 % M) { fprintf(stderr, "r^k != 1 mod m\n"); return 2; }
    N = M * K_; RP = malloc(sizeof(i64) * K_); for (i64 j = 0; j < K_; j++) RP[j] = mpow(R_, j, M);
    W = (M + 63) / 64; W2 = (2 * M + 63) / 64 + 2; lastmask = (M % 64) ? ((1ULL << (M % 64)) - 1) : ~0ULL;
    HA = malloc(K_ * W * 8); HB = malloc(K_ * W * 8);
    SA = aligned_alloc(64, ((K_ * W * 8 + 63) / 64) * 64); SB = aligned_alloc(64, ((K_ * W * 8 + 63) / 64) * 64);
    DBL = aligned_alloc(64, ((K_ * W2 * 8 + 63) / 64) * 64);
    if (!SA || !SB || !DBL) { fprintf(stderr, "out of memory\n"); return 2; }
    int th = getenv("THREADS") ? atoi(getenv("THREADS")) : 1; omp_set_num_threads(th);
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.2;
    int reheat = getenv("REHEAT") ? atoi(getenv("REHEAT")) : 40;
    int targp = getenv("TARGP") ? atoi(getenv("TARGP")) : 70;
    S[0].a = 0; S[0].j = 0;
    if (getenv("EVAL")) { if (!readsol(getenv("EVAL"))) { fprintf(stderr, "bad EVAL file\n"); return 2; }
        double t = now(); i64 c = cost(); printf("EVAL cost=%lld (%.2fs) N=%lld\n", (long long)c, now() - t, (long long)N); return 0; }
    if (getenv("START")) { if (!readsol(getenv("START"))) { fprintf(stderr, "bad START file\n"); return 2; } }
    else for (int i = 1; i < d; i++) do S[i] = rel(); while (!distinct(i));
    if (getenv("FIN")) {   /* f09 targeted finisher: hole-directed candidates per round, sideways moves allowed */
        double tt0 = now(); i64 cur = cost(), gbest = cur; long ev = 1; int rounds = 0;
        fprintf(stderr, "FIN start cost %lld N %lld\n", (long long)cur, (long long)N);
        while (cur > 0 && now() - tt0 < secs) {
            rounds++;
            int i = 1 + rnd() % (d - 1); el old = S[i], u, bc = old; i64 bcost = -1;
            if (!hole(0, &u)) { fprintf(stderr, "no hole found\n"); break; }
            for (int c = 0; c < Kc; c++) {
                S[i] = target(i, 0, u);
                if ((S[i].a == 0 && S[i].j == 0) || !distinct(i)) do S[i] = rel(); while (!distinct(i));
                i64 x = cost(); ev++;
                if (x == 0) { writesol(out); printf("RESULT FIN cost0 d=%d D=%d group=meta %lld %lld %lld N=%lld vertices=%lld evals=%ld time=%.1f\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)(2 * N), ev, now() - tt0); return 0; }
                if (bcost < 0 || x < bcost || (x == bcost && (rnd() & 1))) { bcost = x; bc = S[i]; }
            }
            if (bcost <= cur) { S[i] = bc; cur = bcost; } else S[i] = old;
            cost(); ev++;   /* refresh HA/HB for the (new) current state */
            if (cur < gbest) gbest = cur;
            writesol(out);
            fprintf(stderr, "round %d slot %d: min cand %lld cur %lld best %lld evals %ld t=%.1f\n", rounds, i, (long long)bcost, (long long)cur, (long long)gbest, ev, now() - tt0);
        }
        printf("RESULT FIN open d=%d D=%d group=meta %lld %lld %lld N=%lld cur=%lld best=%lld evals=%ld time=%.1f\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)cur, (long long)gbest, ev, now() - tt0);
        return 0;
    }
    if (getenv("OPT1")) {   /* exhaustive 1-opt from the START S: every slot, every group element */
        i64 c0 = cost(); fprintf(stderr, "OPT1 from cost %lld (N=%lld)\n", (long long)c0, (long long)N);
        for (int i = 1; i < d; i++) { el si = S[i];
            for (i64 x = 1; x < N; x++) { S[i].a = x / K_; S[i].j = x % K_; if (!distinct(i)) continue;
                if (cost() == 0) { writesol(out); printf("RESULT d=%d D=%d group=meta %lld %lld %lld N=%lld vertices=%lld best=0 opt1 slot=%d\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)(2 * N), i); return 0; } }
            S[i] = si; }
        printf("RESULT d=%d D=%d group=meta %lld %lld %lld N=%lld best=%lld opt1 exhausted\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)c0); return 0;
    }
    if (getenv("OPT2")) {   /* exhaustive 2-opt from the START S: every pair of slots (i,j), every (x,y) in G^2 */
        i64 c0 = cost(); fprintf(stderr, "OPT2 from cost %lld (N=%lld)\n", (long long)c0, (long long)N);
        int pi = 0, pj = 0; if (getenv("OPT2PAIR")) sscanf(getenv("OPT2PAIR"), "%d,%d", &pi, &pj);   /* only this pair */
        for (int i = 1; i < d; i++) for (int j = i + 1; j < d; j++) {
            if (pi && (i != pi || j != pj)) continue;
            el si = S[i], sj = S[j]; long ev = 0; double t1 = now();
            for (i64 x = 1; x < N; x++) { S[i].a = x / K_; S[i].j = x % K_; if (!distinct(i)) continue;
                for (i64 y = 1; y < N; y++) { S[j].a = y / K_; S[j].j = y % K_; if (!distinct(j)) continue;
                    i64 c = cost(); ev++;
                    if (c == 0) { writesol(out); printf("RESULT d=%d D=%d group=meta %lld %lld %lld N=%lld vertices=%lld best=0 opt2 slots=%d,%d evals=%ld\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)(2 * N), i, j, ev); return 0; } } }
            fprintf(stderr, "slots %d,%d: %ld evals, no cost 0 (%.0fs)\n", i, j, ev, now() - t1); S[i] = si; S[j] = sj; }
        printf("RESULT d=%d D=%d group=meta %lld %lld %lld N=%lld best=%lld opt2 exhausted\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)c0); return 0;
    }
    double t0 = now(); i64 cur = cost(), best = cur; el BS[64]; memcpy(BS, S, sizeof S);
    fprintf(stderr, "hmeta d=%d D=%d meta %lld %lld %lld N=%lld: start cost=%lld (%.2fs per eval)\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)cur, now() - t0);
    long evals = 1, moves = 0, since = 0; char bf[600]; snprintf(bf, sizeof bf, "%s.best", out);
    while (best > 0 && now() - t0 < secs) {
        double fr = (now() - t0) / secs; double T = T0 * pow(T1 / T0, fr);
        int i = 1 + rnd() % (d - 1); el old = S[i], bc = old; i64 bcost = -1;
        /* holes of the current S (HA/HB hold the last evaluation, which may be a rejected candidate: re-evaluate) */
        int ntarg = 0; el U[64]; int US[64];
        if (targp > 0 && cur > 0) { S[i] = old; cost(); evals++;
            for (int c = 0; c < Kc; c++) { int side = (D % 2 == 0 || (lastA > 0 && (lastB == 0 || rnd() % (lastA + lastB) < (u64)lastA))) ? 0 : 1;
                if ((int)(rnd() % 100) < targp && hole(side, &U[ntarg])) US[ntarg++] = side; } }
        for (int c = 0; c < Kc; c++) {
            if (c < ntarg) { S[i] = target(i, US[c], U[c]); if ((S[i].a == 0 && S[i].j == 0) || !distinct(i)) do S[i] = rel(); while (!distinct(i)); }
            else do S[i] = rel(); while (!distinct(i));
            i64 x = cost(); evals++;
            if (bcost < 0 || x < bcost) { bcost = x; bc = S[i]; } }
        moves++; since++;
        if (bcost <= cur || exp(-(double)(bcost - cur) / (T * (1 + 0.02 * cur))) > (rnd() % 1000000) / 1e6) { S[i] = bc; cur = bcost; } else S[i] = old;
        if (cur < best) { best = cur; memcpy(BS, S, sizeof S); since = 0; el tmp[64]; memcpy(tmp, S, sizeof S); writesol(bf);
            fprintf(stderr, "t=%.0f moves=%ld evals=%ld best=%lld T=%.2f\n", now() - t0, moves, evals, (long long)best, T); }
        if (since > reheat) { memcpy(S, BS, sizeof S); cur = best; since = 0; }
    }
    memcpy(S, BS, sizeof S);
    if (best == 0) { i64 c = cost(); if (c != 0) { fprintf(stderr, "re-evaluation failed (%lld)\n", (long long)c); return 1; } writesol(out); }
    printf("RESULT d=%d D=%d group=meta %lld %lld %lld N=%lld vertices=%lld best=%lld evals=%ld time=%.1f\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)(2 * N), (long long)best, evals, now() - t0);
    return 0;
}
