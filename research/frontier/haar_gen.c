/* haar_gen: annealing search for Haar (bi-Cayley) graphs of diameter D over G = M x Z_n,
 * M one of: meta m k r (Z_m x|_r Z_k), sl p, psl p, pgl p (p prime), or the trivial group (n only: "cyc").
 *
 * Haar graph H(G,S): vertices (g,A), (g,B); edges (g,A) ~ (s g, B), s in S, |S| = d.
 * Right multiplication by G is transitive on each side, so diam = max(ecc(e,A), ecc(e,B)).
 * Cost (BFS on the Haar graph, with left-multiplication tables L_s, L_{s^-1} kept for the current S):
 *   D even: #B-side elements not within D-1 of (e,A)  (side A from (e,B) is the inverse set);
 *   D odd : #A-side elements not within D-1 of (e,A) + #B-side elements not within D-1 of (e,B).
 * The full diameter (all four side pairs within D) is checked before writing a solution.
 * Moves: replace one s_i (i >= 1; s_0 = e WLOG) by the best of K random elements; Metropolis on the best.
 *
 * Usage: haar_gen d D seconds seed K outfile GROUP... n
 *   GROUP = meta m k r | sl p | psl p | pgl p | cyc
 *   e.g. haar_gen 7 8 3600 1 8 out.txt psl 31 3
 * Solution file: header line "d D <group spec> n N", then d lines: element index, then its description.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <signal.h>

#define MAXD 32
typedef struct { int a, b, c, d; } mat;

static int d, D, N, NM, ncyc;          /* N = NM * ncyc */
static int gtype;                      /* 0 meta, 1 sl, 2 psl, 3 pgl, 4 trivial */
static int m, k, p; static long long r;
static int64_t *R;
static mat *EL; static int *IDX;       /* matrix groups: element list, index of (a,b,c,d) */

static int mmul(int x, int y) {        /* product in M */
    if (gtype == 4) return 0;
    if (gtype == 0) {
        int a = x / k, j = x % k, b = y / k, l = y % k;
        int c = (int)((a + R[j] * b) % m);
        return c * k + (j + l) % k;
    }
    mat A = EL[x], B = EL[y], C;
    C.a = (A.a * B.a + A.b * B.c) % p; C.b = (A.a * B.b + A.b * B.d) % p;
    C.c = (A.c * B.a + A.d * B.c) % p; C.d = (A.c * B.b + A.d * B.d) % p;
    return IDX[((C.a * p + C.b) * p + C.c) * p + C.d];
}
static int gmul(int x, int y) {        /* G = M x Z_n, index = mi * n + z */
    int mi = mmul(x / ncyc, y / ncyc);
    return mi * ncyc + (x % ncyc + y % ncyc) % ncyc;
}
static int *INV;
static int ident;

static long long powmod(long long b, long long e, long long md) { long long r_ = 1; b %= md; while (e) { if (e & 1) r_ = r_ * b % md; b = b * b % md; e >>= 1; } return r_; }

static void build_matrix_group(void) {
    long long cap = (long long)p * p * p * p;
    IDX = malloc(sizeof(int) * cap);
    for (long long i = 0; i < cap; i++) IDX[i] = -1;
    EL = malloc(sizeof(mat) * (size_t)p * p * p * p);
    NM = 0;
    for (int a = 0; a < p; a++) for (int b = 0; b < p; b++) for (int c = 0; c < p; c++) for (int dd = 0; dd < p; dd++) {
        int det = ((a * dd - b * c) % p + p) % p;
        if (det == 0) continue;
        if ((gtype == 1 || gtype == 2) && det != 1) continue;
        long long key = ((a * p + b) * p + c) * p + dd;
        if (IDX[key] >= 0) continue;
        /* class of this matrix: {lambda * X} for lambda in the scalar group (+-1 for psl, all for pgl) */
        int id = NM++;
        EL[id] = (mat){ a, b, c, dd };
        if (gtype == 1) { IDX[key] = id; continue; }
        for (int l = 1; l < p; l++) {
            if (gtype == 2 && l != 1 && l != p - 1) continue;
            long long k2 = (((long long)(l * a % p) * p + l * b % p) * p + l * c % p) * p + l * dd % p;
            IDX[k2] = id;
        }
    }
}

static int S[MAXD], bestS[MAXD];
static int *L[MAXD], *Li[MAXD];        /* L[i][g] = s_i g, Li[i][g] = s_i^-1 g */
static int *cand, *candi;
static int *fa, *fb; static uint32_t *mk[2], stampv = 0;
static unsigned long long rs;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void fill(int *T, int x) { for (int g = 0; g < N; g++) T[g] = gmul(x, g); }

/* tables for the d generators in use: ptrs */
static int *TA[MAXD], *TB[MAXD];
static int reach(int startB, int depth, int target) {
    stampv++;
    if (stampv == 0) { memset(mk[0], 0, 4 * (size_t)N); memset(mk[1], 0, 4 * (size_t)N); stampv = 1; }
    int cnt[2] = { 1, 0 };
    int nf = 1, side = startB; fa[0] = ident; mk[side][ident] = stampv;
    for (int step = 0; step < depth; step++) {
        int ns = side ^ 1, nn = 0; uint32_t *M = mk[ns];
        int **T = side == 0 ? TA : TB;
        for (int f = 0; f < nf; f++) {
            int g = fa[f];
            for (int i = 0; i < d; i++) { int h = T[i][g]; if (M[h] != stampv) { M[h] = stampv; fb[nn++] = h; } }
        }
        cnt[ns == startB ? 0 : 1] += nn;
        int *t = fa; fa = fb; fb = t; nf = nn; side = ns;
    }
    return cnt[target];
}
/* uncovered lists, from the last call of collect(): elements on side utside[t] not reached from (e,ustart[t]) */
static int *UNC[2], nunc[2], ust[2], uside[2], nlists;
static void collect1(int t, int startB, int targetSame) {
    reach(startB, D - 1, 0);
    uint32_t *M = mk[targetSame ? startB : startB ^ 1];
    /* reach() marks with stampv; vertices on the target side not marked are uncovered */
    int n = 0;
    for (int g = 0; g < N; g++) if (M[g] != stampv) UNC[t][n++] = g;
    nunc[t] = n; ust[t] = startB; uside[t] = targetSame ? startB : startB ^ 1;
}
static void collect(void) {
    if (D % 2 == 0) { nlists = 1; collect1(0, 0, 0); }
    else { nlists = 2; collect1(0, 0, 1); collect1(1, 1, 1); }
}
/* random walk of length len from (g,side) avoiding generator `avoid`; returns end, updates *side */
static int walk(int g, int *side, int len, int avoid) {
    for (int s = 0; s < len; s++) {
        int j; do j = rnd() % d; while (j == avoid);
        g = (*side == 0) ? L[j][g] : Li[j][g];
        *side ^= 1;
    }
    return g;
}
/* targeted candidate for slot i: an element x that puts one uncovered vertex within D-1 of the start */
static int targeted(int i) {
    int tot = 0; for (int t = 0; t < nlists; t++) tot += nunc[t];
    if (tot == 0) return -1;
    int z = rnd() % tot, t = 0; while (z >= nunc[t]) { z -= nunc[t]; t++; }
    int u = UNC[t][z];
    /* path start ->(a)-> P -- Q <-(b)- u, a + b + 1 <= D-1, P and Q on opposite sides */
    for (int tries = 0; tries < 20; tries++) {
        int a = rnd() % (D - 1), b = rnd() % (D - 1 - a);
        int sp = ust[t], sq = uside[t];
        int P = walk(ident, &sp, a, i), Q = walk(u, &sq, b, i);
        if (sp == sq) continue;
        int gA = sp == 0 ? P : Q, hB = sp == 0 ? Q : P;      /* (gA,A) ~ (hB,B) iff hB = x gA */
        return gmul(hB, INV[gA]);
    }
    return -1;
}
static int cost(void) {
    if (D % 2 == 0) return N - reach(0, D - 1, 1);
    return (N - reach(0, D - 1, 0)) + (N - reach(1, D - 1, 0));
}
static int full_check(void) { return reach(0, D, 0) == N && reach(0, D, 1) == N && reach(1, D, 0) == N && reach(1, D, 1) == N; }
static int used(int x, int skip) { for (int i = 0; i < d; i++) if (i != skip && S[i] == x) return 1; return 0; }
static volatile int stop_flag = 0;
static void on_term(int s) { (void)s; stop_flag = 1; }

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: haar_gen d D seconds seed K outfile GROUP... n\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); double secs = atof(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((unsigned long long)atoll(argv[4]) + 1) * 2654435761ULL;
    int K = atoi(argv[5]); const char *out = argv[6];
    int a = 7; char spec[200];
    if (!strcmp(argv[a], "meta")) { gtype = 0; m = atoi(argv[a + 1]); k = atoi(argv[a + 2]); r = atoll(argv[a + 3]); a += 4;
        R = malloc(sizeof(int64_t) * k); R[0] = 1; for (int j = 1; j < k; j++) R[j] = R[j - 1] * r % m;
        if (R[k - 1] * r % m != 1) { fprintf(stderr, "r^k != 1\n"); return 2; }
        NM = m * k; snprintf(spec, sizeof spec, "meta %d %d %lld", m, k, r); }
    else if (!strcmp(argv[a], "sl") || !strcmp(argv[a], "psl") || !strcmp(argv[a], "pgl")) {
        gtype = !strcmp(argv[a], "sl") ? 1 : !strcmp(argv[a], "psl") ? 2 : 3; p = atoi(argv[a + 1]);
        snprintf(spec, sizeof spec, "%s %d", argv[a], p); a += 2; build_matrix_group(); }
    else if (!strcmp(argv[a], "cyc")) { gtype = 4; NM = 1; a += 1; snprintf(spec, sizeof spec, "cyc"); }
    else { fprintf(stderr, "bad group\n"); return 2; }
    ncyc = atoi(argv[a]); N = NM * ncyc;
    (void)powmod;
    signal(SIGTERM, on_term);
    /* identity and inverses */
    ident = -1;
    for (int x = 0; x < N && ident < 0; x++) { int ok = 1; for (int t = 0; t < 50 && ok; t++) { int y = rnd() % N; ok = gmul(x, y) == y && gmul(y, x) == y; } if (ok) ident = x; }
    INV = malloc(sizeof(int) * N);
    { int *T = malloc(sizeof(int) * N); for (int x = 0; x < N; x++) INV[x] = -1;
      for (int x = 0; x < N; x++) if (INV[x] < 0) { /* inverse = x^(ord-1) */ int y = x, prev = ident; while (y != ident) { prev = y; y = gmul(y, x); } INV[x] = prev; INV[prev] = x; }
      free(T); }
    for (int t = 0; t < 2000; t++) { int x = rnd() % N, y = rnd() % N, z = rnd() % N;
        if (gmul(gmul(x, y), z) != gmul(x, gmul(y, z)) || gmul(x, INV[x]) != ident) { fprintf(stderr, "group error\n"); return 2; } }
    fprintf(stderr, "group %s x Z_%d, N=%d, identity %d\n", spec, ncyc, N, ident);
    for (int i = 0; i < d; i++) { L[i] = malloc(4 * (size_t)N); Li[i] = malloc(4 * (size_t)N); }
    cand = malloc(4 * (size_t)N); candi = malloc(4 * (size_t)N);
    fa = malloc(4 * (size_t)N); fb = malloc(4 * (size_t)N); mk[0] = calloc(N, 4); mk[1] = calloc(N, 4);
    S[0] = ident;
    for (int i = 1; i < d; i++) { int x; do x = rnd() % N; while (x == ident || used(x, i)); S[i] = x; }
    for (int i = 0; i < d; i++) { fill(L[i], S[i]); fill(Li[i], INV[S[i]]); TA[i] = L[i]; TB[i] = Li[i]; }
    UNC[0] = malloc(4 * (size_t)N); UNC[1] = malloc(4 * (size_t)N);
    int c = cost(), best = c; memcpy(bestS, S, sizeof S); collect();
    double t0 = now(), T = 1.5, lastimp = t0, lastprint = t0; long long evals = 1, steps = 0;
    fprintf(stderr, "start cost=%d\n", c);
    while (!stop_flag && now() - t0 < secs && best > 0) {
        int i = 1 + rnd() % (d - 1), bx = -1, bc = 1 << 30;
        for (int t = 0; t < K; t++) {
            int x = (rnd() % 100 < 70) ? targeted(i) : -1;
            if (x < 0 || x == ident || used(x, i)) do x = rnd() % N; while (x == ident || used(x, i));
            fill(cand, x); fill(candi, INV[x]); TA[i] = cand; TB[i] = candi;
            int cc = cost(); evals++;
            if (cc < bc) { bc = cc; bx = x; }
        }
        TA[i] = L[i]; TB[i] = Li[i];
        if (bc <= c || exp((c - bc) / T) > (rnd() % 1000000) / 1e6) { S[i] = bx; fill(L[i], bx); fill(Li[i], INV[bx]); c = bc; collect(); }
        steps++;
        if (c < best) { best = c; memcpy(bestS, S, sizeof S); lastimp = now(); }
        T *= 0.9995; if (T < 0.15) T = 0.15;
        if (now() - lastimp > 150) { T = 1.5; memcpy(S, bestS, sizeof S); for (int j = 0; j < d; j++) { fill(L[j], S[j]); fill(Li[j], INV[S[j]]); } c = best; collect(); lastimp = now(); }
        if (now() - lastprint > 30) { fprintf(stderr, "t=%.0f steps=%lld evals=%lld cost=%d best=%d T=%.2f\n", now() - t0, steps, evals, c, best, T); lastprint = now(); }
    }
    memcpy(S, bestS, sizeof S);
    for (int j = 0; j < d; j++) { fill(L[j], S[j]); fill(Li[j], INV[S[j]]); TA[j] = L[j]; TB[j] = Li[j]; }
    printf("RESULT d=%d D=%d group=%s x Z_%d N=%d best=%d evals=%lld time=%.1f\n", d, D, spec, ncyc, N, best, evals, now() - t0);
    if (best == 0) {
        int ok = full_check();
        printf("full diameter check: %s\n", ok ? "OK" : "FAIL");
        if (ok) {
            FILE *f = fopen(out, "w");
            fprintf(f, "%d %d %s n %d N %d\n", d, D, spec, ncyc, N);
            for (int i = 0; i < d; i++) {
                int x = S[i], mi = x / ncyc, z = x % ncyc;
                if (gtype == 0) fprintf(f, "%d meta(a=%d,j=%d) z=%d\n", x, mi / k, mi % k, z);
                else if (gtype == 4) fprintf(f, "%d z=%d\n", x, z);
                else fprintf(f, "%d mat(%d,%d,%d,%d) z=%d\n", x, EL[mi].a, EL[mi].b, EL[mi].c, EL[mi].d, z);
            }
            fclose(f); printf("wrote %s\n", out);
        }
    }
    return best == 0 ? 0 : 1;
}
