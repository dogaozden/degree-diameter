/* chart7: route charts over F_4^4 for the 17 = 5+4+4+4 lift.
   Lift: A-vertex (u,x) ~ B-vertex (v, A_c x + w), w in W_c; W_c = F4*b_c (4 elements), W_0 also contains e (5 elements).
   Walk from an A-vertex with letters p1..p4 (AB,BA,AB,BA) or from a B-vertex (BA,AB,BA,AB): endpoint set from start 0
   is the translation set S; the walk reaches a full fibre iff |S| = 256.
   Checks: 216 nonbacktracking patterns (108 per start side), pencil families (3 backtracking shapes x 4 colours per
   ordered pair (i,j) per side, union must be 256). Cost = sum of deficiencies 256-|S| (patterns + pencil).
   usage: chart7 eval FILE            -> prints statistics for a chart file (16+16 ints, then 4 ints for e if present)
          chart7 anneal SECONDS SEED OUT [INIT]  -> simulated annealing, writes best chart to OUT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
static double wall(void){struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec;}
static const int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static const int INVF[4] = {0,1,3,2};
static inline int co(int v, int r) { return (v >> (2*r)) & 3; }
typedef struct { int m[4][4]; } Mat;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rnd(int n) { return (int)(xr() % (uint64_t)n); }
static int smul(int l, int v) { int o = 0; for (int r = 0; r < 4; r++) o |= MUL[l][co(v, r)] << (2*r); return o; }
static int mvraw(const Mat *M, int v) {
    int out = 0;
    for (int r = 0; r < 4; r++) { int s = 0; for (int c = 0; c < 4; c++) s ^= MUL[M->m[r][c]][co(v, c)]; out |= s << (2*r); }
    return out;
}
static int matinv(const Mat *M, Mat *R) {
    int X[4][8];
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { X[r][c] = M->m[r][c]; X[r][4+c] = (r == c); }
    for (int col = 0; col < 4; col++) {
        int p = -1; for (int r = col; r < 4; r++) if (X[r][col]) { p = r; break; }
        if (p < 0) return 0;
        for (int c = 0; c < 8; c++) { int t = X[p][c]; X[p][c] = X[col][c]; X[col][c] = t; }
        int iv = INVF[X[col][col]]; for (int c = 0; c < 8; c++) X[col][c] = MUL[iv][X[col][c]];
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] ^= MUL[f][X[col][c]]; }
    }
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) R->m[r][c] = X[r][4+c];
    return 1;
}
typedef struct { Mat A[4], Ai[4]; int b[4]; int e; } Chart;  /* e < 0: no extra vector */
static int tabA[4][256], tabAi[4][256], Wv[4][5], nWv[4];
static int stampv[256], stampc = 0;
static void prep(const Chart *C) {
    for (int c = 0; c < 4; c++) for (int v = 0; v < 256; v++) { tabA[c][v] = mvraw(&C->A[c], v); tabAi[c][v] = mvraw(&C->Ai[c], v); }
    for (int c = 0; c < 4; c++) { nWv[c] = 0; for (int l = 0; l < 4; l++) Wv[c][nWv[c]++] = smul(l, C->b[c]); }
    if (C->e >= 0) Wv[0][nWv[0]++] = C->e;
}
/* endpoint set of walk with letters p[0..3] from start 0; startA: first step is AB. Marks into mark, returns size. */
static int pat_set(int startA, const int *p, unsigned char *mark) {
    int cur[256], nxt[256], n = 1; cur[0] = 0;
    for (int k = 0; k < 4; k++) {
        int c = p[k]; int isAB = startA ? !(k & 1) : (k & 1);
        int nn = 0; stampc++;
        for (int i = 0; i < n; i++) for (int w = 0; w < nWv[c]; w++) {
            int v = isAB ? (tabA[c][cur[i]] ^ Wv[c][w]) : tabAi[c][cur[i] ^ Wv[c][w]];
            if (stampv[v] != stampc) { stampv[v] = stampc; nxt[nn++] = v; }
        }
        memcpy(cur, nxt, nn * sizeof(int)); n = nn;
    }
    if (mark) for (int i = 0; i < n; i++) mark[cur[i]] = 1;
    return n;
}
typedef struct { int defp, nonfull, cyc, defpen, penfail; } Stats;
static void evalchart(const Chart *C, Stats *S) {
    prep(C);
    memset(S, 0, sizeof *S);
    unsigned char mark[256];
    for (int s = 0; s < 2; s++)
        for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1)
        for (int i3 = 0; i3 < 4; i3++) if (i3 != i2) for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) {
            int p[4] = {i1, i2, i3, i4};
            int n = pat_set(s, p, NULL);
            S->defp += 256 - n;
            if (n < 256) { S->nonfull++; if (i4 != i1) S->cyc++; }
        }
    for (int s = 0; s < 2; s++) for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) {
        memset(mark, 0, sizeof mark);
        for (int c = 0; c < 4; c++) {
            int p1[4] = {c, c, i, j}, p2[4] = {i, c, c, j}, p3[4] = {i, j, c, c};
            pat_set(s, p1, mark); pat_set(s, p2, mark); pat_set(s, p3, mark);
        }
        int cnt = 0; for (int v = 0; v < 256; v++) cnt += mark[v];
        S->defpen += 256 - cnt; if (cnt < 256) S->penfail++;
    }
}
static int cost_of(const Chart *C, Stats *S) { evalchart(C, S); return S->defp + S->defpen; }
static int read_chart(const char *fn, Chart *C) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    int x[96], n = 0, t;
    while (n < 84 && fscanf(f, "%d", &t) == 1) x[n++] = t;
    fclose(f);
    if (n < 80) return 0;
    for (int k = 0; k < 4; k++) {
        for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) C->A[k].m[r][c] = x[16*k + 4*r + c];
        if (matinv(&C->A[k], &C->Ai[k]) == 0) { fprintf(stderr, "singular A_%d\n", k); return 0; }
    }
    for (int k = 0; k < 4; k++) { int v = 0; for (int r = 0; r < 4; r++) v |= x[64 + 4*k + r] << (2*r); C->b[k] = v; }
    if (n >= 84) { int v = 0; for (int r = 0; r < 4; r++) v |= x[80 + r] << (2*r); C->e = v; } else C->e = -1;
    return 1;
}
static void write_chart(const char *fn, const Chart *C) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    for (int k = 0; k < 4; k++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) fprintf(f, "%d ", C->A[k].m[r][c]); fprintf(f, "\n"); }
    for (int k = 0; k < 4; k++) { for (int r = 0; r < 4; r++) fprintf(f, "%d ", co(C->b[k], r)); fprintf(f, "\n"); }
    if (C->e >= 0) { for (int r = 0; r < 4; r++) fprintf(f, "%d ", co(C->e, r)); fprintf(f, "\n"); }
    fclose(f);
}
static void print_stats(const char *tag, const Stats *S) {
    printf("%s cost=%d defp=%d nonfull=%d (cyclic %d) defpen=%d penfail=%d\n", tag, S->defp + S->defpen, S->defp,
           S->nonfull, S->cyc, S->defpen, S->penfail);
}
static int rand_gl(Mat *M, Mat *Mi) {
    do { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) M->m[r][c] = rnd(4); } while (!matinv(M, Mi));
    return 1;
}
static int rand_nz(void) { int v; do { v = rnd(256); } while (v == 0); return v; }
static int ok_e(int e, int b0) { for (int l = 0; l < 4; l++) if (smul(l, b0) == e) return 0; return 1; }
int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "eval")) {
        Chart C; if (!read_chart(argv[2], &C)) { fprintf(stderr, "bad file\n"); return 1; }
        Stats S; evalchart(&C, &S); print_stats(argv[2], &S);
        return 0;
    }
    if (argc >= 3 && !strcmp(argv[1], "list")) {
        Chart C; if (!read_chart(argv[2], &C)) { fprintf(stderr, "bad file\n"); return 1; }
        prep(&C);
        for (int s = 0; s < 2; s++) for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1)
        for (int i3 = 0; i3 < 4; i3++) if (i3 != i2) for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) {
            int p[4] = {i1, i2, i3, i4}; int n = pat_set(s, p, NULL);
            if (n < 256) printf("side %s pattern %d%d%d%d size %d\n", s ? "A" : "B", i1, i2, i3, i4, n);
        }
        return 0;
    }
    if (argc >= 5 && !strcmp(argv[1], "anneal")) {
        double secs = atof(argv[2]); uint64_t seed = strtoull(argv[3], NULL, 10);
        rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
        Chart C, best; Stats S;
        if (argc >= 6) { if (!read_chart(argv[5], &C)) { fprintf(stderr, "bad init\n"); return 1; } }
        else {
            memset(&C, 0, sizeof C);
            C.A[0].m[0][0] = C.A[0].m[1][1] = C.A[0].m[2][2] = C.A[0].m[3][3] = 1;
            C.Ai[0] = C.A[0]; C.b[0] = 1;   /* gauge: A_0 = I, b_0 = e_1 */
            for (int k = 1; k < 4; k++) { rand_gl(&C.A[k], &C.Ai[k]); C.b[k] = rand_nz(); }
            do { C.e = rnd(256); } while (!ok_e(C.e, C.b[0]));
        }
        int cur = cost_of(&C, &S); best = C; int bestc = cur; Stats bs = S;
        double t0 = wall(); long it = 0;
        while (1) {
            if ((it & 255) == 0) {
                double el = wall() - t0; if (el > secs) break;
                double T = 40.0 * (1.0 - el / secs) + 0.5;
                (void)T;
            }
            it++;
            double el = wall() - t0;
            double T = 40.0 * (1.0 - el / secs) + 0.5;
            Chart N = C; int mt = rnd(10);
            if (mt < 6) {
                int k = 1 + rnd(3), r = rnd(4), c = rnd(4), v = rnd(4);
                N.A[k].m[r][c] = v;
                if (!matinv(&N.A[k], &N.Ai[k])) continue;
            } else if (mt < 8) {
                int k = 1 + rnd(3); N.b[k] = rand_nz();
            } else {
                int e; do { e = rnd(256); } while (!ok_e(e, N.b[0])); N.e = e;
            }
            Stats NS; int nc = cost_of(&N, &NS);
            if (nc <= cur || (double)(xr() % 1000000) / 1e6 < __builtin_exp(-(nc - cur) / T)) {
                C = N; cur = nc; S = NS;
                if (cur < bestc) { bestc = cur; best = C; bs = S; write_chart(argv[4], &best);
                    printf("it %ld t %.1f best %d (defp %d defpen %d nonfull %d)\n", it, el, bestc, bs.defp, bs.defpen, bs.nonfull); fflush(stdout); }
                if (cur == 0) break;
            }
        }
        write_chart(argv[4], &best);
        print_stats("best", &bs);
        printf("iterations %ld\n", it);
        return 0;
    }
    fprintf(stderr, "usage: chart7 eval FILE | chart7 anneal SECONDS SEED OUT [INIT]\n");
    return 1;
}
