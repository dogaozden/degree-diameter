/* c1.c (deep-65b round 1, card c1): tabu search over (E1,E2) for the [[1,5],[5,1]] lift family.
 * Cost = sum of the six missing counts C1..C6 of tools/split15.c (conditions as in its header).
 *
 * usage: c1 TAB SEED SECS [EDGES_OUT]     tabu search (restarts) until cost 0 or SECS elapsed; prints one RES line.
 *        c1 TAB cost e1 x5 e2 x5           prints the six miss counts for one state (for checking against split15).
 * TAB: m, the m x m table (identity 0), then optional "ngen k" lines (ignored here).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 256
#define INF 1000000
#define TENURE 10
#define RESTART 1500

typedef struct { uint64_t w[4]; } bs;
static int m, NW;
static uint8_t T[MAXM][MAXM];
static int inv_[MAXM];
static bs FULL;

static inline void bset(bs *b, int x) { b->w[x >> 6] |= 1ULL << (x & 63); }
static inline void bzero4(bs *b) { b->w[0] = b->w[1] = b->w[2] = b->w[3] = 0; }
static inline int bmiss(const bs *b) { int c = 0; for (int i = 0; i < NW; i++) c += __builtin_popcountll(FULL.w[i] & ~b->w[i]); return c; }
static inline int blist(const bs *b, int *out) {
    int n = 0;
    for (int i = 0; i < NW; i++) { uint64_t w = b->w[i]; while (w) { out[n++] = (i << 6) | __builtin_ctzll(w); w &= w - 1; } }
    return n;
}
static inline void prod_into(bs *c, const int *A, int na, const int *B, int nb) {
    for (int i = 0; i < na; i++) { const uint8_t *row = T[A[i]]; for (int j = 0; j < nb; j++) bset(c, row[B[j]]); }
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void readtab(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f || fscanf(f, "%d", &m) != 1 || m > MAXM) { fprintf(stderr, "bad table %s\n", fn); exit(2); }
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) { int x; if (fscanf(f, "%d", &x) != 1) exit(2); T[i][j] = (uint8_t)x; }
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (T[i][j] == 0) inv_[i] = j;
    NW = (m + 63) / 64;
    memset(&FULL, 0, sizeof FULL);
    for (int x = 0; x < m; x++) bset(&FULL, x);
}

/* six miss counts; returns their sum */
static int cost(const int *E1, const int *E2, int *brk) {
    int I1[5], I2[5], E[10], EI[10];
    for (int i = 0; i < 5; i++) {
        I1[i] = inv_[E1[i]]; I2[i] = inv_[E2[i]];
        E[i] = E1[i]; E[5 + i] = E2[i]; EI[i] = I1[i]; EI[5 + i] = I2[i];
    }
    bs bQ1, bQ2, bP1, bP2, bEEi, bEiE, bE;
    bzero4(&bQ1); bzero4(&bQ2); bzero4(&bP1); bzero4(&bP2); bzero4(&bEEi); bzero4(&bEiE); bzero4(&bE);
    prod_into(&bQ1, E1, 5, I1, 5);   /* E1 E1^-1 */
    prod_into(&bQ2, E2, 5, I2, 5);   /* E2 E2^-1 */
    prod_into(&bP1, I1, 5, E1, 5);   /* E1^-1 E1 */
    prod_into(&bP2, I2, 5, E2, 5);   /* E2^-1 E2 */
    prod_into(&bEEi, E, 10, EI, 10); /* E E^-1 */
    prod_into(&bEiE, EI, 10, E, 10); /* E^-1 E */
    for (int i = 0; i < 10; i++) bset(&bE, E[i]);
    int Q1[64], Q2[64], P1[64], P2[64], n1, n2, n3, n4;
    n1 = blist(&bQ1, Q1); n2 = blist(&bQ2, Q2); n3 = blist(&bP1, P1); n4 = blist(&bP2, P2);
    bs c;
    /* C1: E E^-1 u (E1E1^-1)^2 */
    c = bEEi; prod_into(&c, Q1, n1, Q1, n1); brk[0] = bmiss(&c);
    /* C2: E E^-1 u (E2E2^-1)^2 */
    c = bEEi; prod_into(&c, Q2, n2, Q2, n2); brk[1] = bmiss(&c);
    /* C3: E^-1 E u (E2^-1E2)^2 */
    c = bEiE; prod_into(&c, P2, n4, P2, n4); brk[2] = bmiss(&c);
    /* C4: E^-1 E u (E1^-1E1)^2 */
    c = bEiE; prod_into(&c, P1, n3, P1, n3); brk[3] = bmiss(&c);
    /* C5: E u Q1E1 u Q1E2 u E1P2 u Q2E2 */
    c = bE; prod_into(&c, Q1, n1, E1, 5); prod_into(&c, Q1, n1, E2, 5); prod_into(&c, E1, 5, P2, n4); prod_into(&c, Q2, n2, E2, 5);
    brk[4] = bmiss(&c);
    /* C6: E u Q1E1 u E2P1 u Q2E1 u Q2E2 */
    c = bE; prod_into(&c, Q1, n1, E1, 5); prod_into(&c, E2, 5, P1, n3); prod_into(&c, Q2, n2, E1, 5); prod_into(&c, Q2, n2, E2, 5);
    brk[5] = bmiss(&c);
    return brk[0] + brk[1] + brk[2] + brk[3] + brk[4] + brk[5];
}

static void write_edges(const int *E1, const int *E2, const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", 4 * m);
    for (int h = 0; h < m; h++) {
        fprintf(f, "%d %d\n", h, 2 * m + h);              /* A0_h - B0_h */
        fprintf(f, "%d %d\n", m + h, 3 * m + h);          /* A1_h - B1_h */
        for (int i = 0; i < 5; i++) {
            fprintf(f, "%d %d\n", h, 3 * m + T[h][E1[i]]);   /* A0_h - B1_{h e} */
            fprintf(f, "%d %d\n", 2 * m + h, m + T[h][E2[i]]); /* B0_h - A1_{h e} */
        }
    }
    fclose(f);
}

static inline int inset(const int *S, int x) { for (int k = 0; k < 5; k++) if (S[k] == x) return 1; return 0; }
static void rand_set(int *S) {   /* 5 distinct random elements */
    int n = 0;
    while (n < 5) { int x = rnd() % m; int ok = 1; for (int k = 0; k < n; k++) if (S[k] == x) ok = 0; if (ok) S[n++] = x; }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: c1 TAB SEED SECS [EDGES_OUT] | c1 TAB cost e1x5 e2x5\n"); return 2; }
    readtab(argv[1]);
    if (!strcmp(argv[2], "cost")) {
        int E1[5], E2[5], brk[6];
        if (argc < 13) return 2;
        for (int i = 0; i < 5; i++) { E1[i] = atoi(argv[3 + i]); E2[i] = atoi(argv[8 + i]); }
        int s = cost(E1, E2, brk);
        printf("%d %d %d %d %d %d total %d\n", brk[0], brk[1], brk[2], brk[3], brk[4], brk[5], s);
        return 0;
    }
    uint64_t seed = strtoull(argv[2], NULL, 10);
    double secs = atof(argv[3]);
    const char *outf = argc > 4 ? argv[4] : NULL;
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 1);
    for (int i = 0; i < 20; i++) rnd();
    double t0 = now();
    int best_all = INF, bE1[5] = {0,0,0,0,0}, bE2[5] = {0,0,0,0,0};
    double tbest = 0;
    long long iters = 0;
    int restarts = 0;
    static long long tabu[10][MAXM];
    int E1[5], E2[5], brk[6];
    while (now() - t0 < secs && best_all > 0) {
        rand_set(E1); rand_set(E2);
        memset(tabu, 0, sizeof tabu);
        int cur = cost(E1, E2, brk);
        int run_best = cur, since = 0;
        restarts++;
        for (long long it = 1;; it++) {
            iters++;
            int bv = INF, bp = -1, by = -1, nt = 0;
            for (int p = 0; p < 10; p++) {
                int *S = p < 5 ? E1 : E2;
                int idx = p % 5, old = S[idx];
                for (int y = 0; y < m; y++) {
                    if (inset(S, y)) continue;
                    int c;
                    S[idx] = y; c = cost(E1, E2, brk); S[idx] = old;
                    if (tabu[p][y] > it && c >= best_all) continue;   /* tabu unless it beats the global best */
                    if (c < bv) { bv = c; bp = p; by = y; nt = 1; }
                    else if (c == bv) { nt++; if (rnd() % nt == 0) { bp = p; by = y; } }
                }
            }
            if (bp < 0) break;
            int *S = bp < 5 ? E1 : E2;
            int idx = bp % 5, old = S[idx];
            S[idx] = by;
            tabu[bp][old] = it + TENURE + (long long)(rnd() % 5);
            cur = bv;
            if (cur < run_best) { run_best = cur; since = 0; } else since++;
            if (cur < best_all) {
                best_all = cur; tbest = now() - t0;
                memcpy(bE1, E1, sizeof bE1); memcpy(bE2, E2, sizeof bE2);
            }
            if (best_all == 0 || since > RESTART || now() - t0 > secs) break;
        }
    }
    double el = now() - t0;
    int b6[6];
    printf("RES n=%d seed=%llu best=%d t_best=%.2f elapsed=%.2f iters=%lld restarts=%d E1=", 4 * m, (unsigned long long)seed,
           best_all, tbest, el, iters, restarts);
    for (int i = 0; i < 5; i++) printf("%s%d", i ? "," : "", bE1[i]);
    printf(" E2=");
    for (int i = 0; i < 5; i++) printf("%s%d", i ? "," : "", bE2[i]);
    if (best_all < INF) { cost(bE1, bE2, b6); printf(" brk=%d,%d,%d,%d,%d,%d", b6[0], b6[1], b6[2], b6[3], b6[4], b6[5]); }
    printf("\n");
    if (best_all == 0 && outf) write_edges(bE1, bE2, outf);
    return 0;
}
