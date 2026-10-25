/* Simulated annealing for route charts over F_q^4 with k letters (k <= 8, q <= 16).
   cost = WS * (#singular nonbacktracking 4-patterns, both sides)
        + WP * (uncovered vectors in the one-detour unions of all (side,i,j) pencils) / q^2
        + WD * (uncovered vectors in the closed-backtracking union, both sides) / q^2
   Reachable sets are computed from the step rules: A->B along c: S -> A_c S + <b_c>; B->A: S -> A_c^-1 S + <w_c>.
   usage: chart_anneal GFTABLE k seconds seed WS WP WD [out.txt]
   Output format = squad165/charts/*.txt (k lines of 16 entries A_c row-major, k lines of b_c). A_0 = I (gauge).
   r3 variant (chart_anneal2): env INIT=chart.txt starts every restart from that chart (A_0 must be I); env T0 (default 2)
   and STALL (default 20000) set the temperature and the restart patience; env TAU (default 4000) the cooling length.
   chart_anneal3 (r3): env MOVES=star uses structured moves instead of single entries: (a) A_c <- R A_c with R a
   transvection fixing b_c (keeps the points w_c, b_c, changes the star collineation; 50%), (b) A_c <- A_c R' with R'
   a random transvection (moves w_c; 25%), (c) one entry of b_c (25%).  All letters move (no A_0 = I gauge during the
   run); the output is re-gauged to A_0 = I.  The D = 5 criterion depends only on the points and the collineations. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
#include <time.h>
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
#define N 4
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int q, k, ADD[128][128], MUL[128][128], INV[128], NEG[128], SUB[128][128];
int A[8][N][N], Ai[8][N][N], b[8][N], w[8][N];
double WS, WP, WD;
int Q4; unsigned char *mark;
static void matvec(int M[N][N], const int *v, int *out) { for (int r = 0; r < N; r++) { int s = 0; for (int c = 0; c < N; c++) s = ADD[s][MUL[M[r][c]][v[c]]]; out[r] = s; } }
static int matinv(int M[N][N], int R[N][N]) {
    int T[N][2 * N]; for (int r = 0; r < N; r++) for (int c = 0; c < 2 * N; c++) T[r][c] = c < N ? M[r][c] : (c - N == r);
    for (int c = 0; c < N; c++) { int p = -1; for (int r = c; r < N; r++) if (T[r][c]) { p = r; break; } if (p < 0) return 0;
        if (p != c) for (int t = 0; t < 2 * N; t++) { int x = T[c][t]; T[c][t] = T[p][t]; T[p][t] = x; }
        int iv = INV[T[c][c]]; for (int t = 0; t < 2 * N; t++) T[c][t] = MUL[iv][T[c][t]];
        for (int r = 0; r < N; r++) if (r != c && T[r][c]) { int f = T[r][c]; for (int t = 0; t < 2 * N; t++) T[r][t] = SUB[T[r][t]][MUL[f][T[c][t]]]; } }
    for (int r = 0; r < N; r++) for (int c = 0; c < N; c++) R[r][c] = T[r][c + N]; return 1; }
static int rankv(int (*V)[N], int m) {
    int T[8][N]; memcpy(T, V, sizeof(int) * N * m); int r = 0;
    for (int c = 0; c < N && r < m; c++) { int p = -1; for (int i = r; i < m; i++) if (T[i][c]) { p = i; break; } if (p < 0) continue;
        if (p != r) for (int t = 0; t < N; t++) { int x = T[r][t]; T[r][t] = T[p][t]; T[p][t] = x; }
        int iv = INV[T[r][c]]; for (int t = 0; t < N; t++) T[r][t] = MUL[iv][T[r][t]];
        for (int i = 0; i < m; i++) if (i != r && T[i][c]) { int f = T[i][c]; for (int t = 0; t < N; t++) T[i][t] = SUB[T[i][t]][MUL[f][T[r][t]]]; }
        r++; }
    return r; }
/* span of a walk: start side s (0=A,1=B), colours pat[0..L-1]; returns number of vectors in S (stored in S) */
static int walkspan(int s, const int *pat, int L, int (*S)[N]) {
    int m = 0, tmp[N];
    for (int t = 0; t < L; t++) { int c = pat[t];
        if (s == 0) { for (int i = 0; i < m; i++) { matvec(A[c], S[i], tmp); memcpy(S[i], tmp, sizeof tmp); } memcpy(S[m++], b[c], sizeof(int) * N); s = 1; }
        else { for (int i = 0; i < m; i++) { matvec(Ai[c], S[i], tmp); memcpy(S[i], tmp, sizeof tmp); } memcpy(S[m++], w[c], sizeof(int) * N); s = 0; } }
    return m; }
static void markspan(int (*S)[N], int m) {
    /* mark every combination of the m vectors (m <= 4); duplicates fine */
    int tot = 1; for (int i = 0; i < m; i++) tot *= q;
    for (int idx = 0; idx < tot; idx++) { int v[N] = {0}, x = idx;
        for (int i = 0; i < m; i++) { int c = x % q; x /= q; if (c) for (int t = 0; t < N; t++) v[t] = ADD[v[t]][MUL[c][S[i][t]]]; }
        int code = 0; for (int t = N - 1; t >= 0; t--) code = code * q + v[t]; mark[code] = 1; } }
int nsing, unc_p, unc_d;
static void write_gauged(const char *out, int (*AA)[N][N], int (*bb)[N]) {
    int G[N][N], T[N][N]; matinv(AA[0], G); FILE *g = fopen(out, "w");
    for (int c = 0; c < k; c++) { for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) { int x = 0; for (int t = 0; t < N; t++) x = ADD[x][MUL[AA[c][r][t]][G[t][s]]]; T[r][s] = x; }
        for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) fprintf(g, "%d ", T[r][s]); fprintf(g, "\n"); }
    for (int c = 0; c < k; c++) { for (int r = 0; r < N; r++) fprintf(g, "%d ", bb[c][r]); fprintf(g, "\n"); }
    fclose(g); }
/* chart_anneal4 (card c5, squad r3-chartlift): same cost as chart_anneal3 (WS*singular + WP*unc_pencil/q^2 + WD*unc_diag/q^2)
   with (1) early rejection: the acceptance cutoff is drawn first and the (expensive) pencil/diagonal part is skipped when
   the singular count alone already exceeds it (cost >= WS*singular); (2) the initial state is recorded as best
   (chart_anneal3 could lose an INIT chart whose first accepted move went uphill); (3) move set MOVES=star2:
   40% A_c <- R A_c (R a transvection fixing b_c: keeps the points b_c and w_c = A_c^-1 b_c),
   20% A_c <- A_c R' (R' a random transvection: moves w_c, keeps b_c),
   20% one entry of b_c (A_c fixed),
   20% NEW: b_c <- random point b' and A_c <- M' A_c with M' b_c = b', M' random invertible, so w_c = A_c^-1 b_c is kept
        (only the point b_c and the collineation move).
   usage: chart_anneal4 GFTABLE k seconds seed WS WP WD [out.txt]; env INIT, T0, STALL, TAU as in chart_anneal3. */
static int prep(void) { for (int c = 0; c < k; c++) { if (!matinv(A[c], Ai[c])) return 0; matvec(Ai[c], b[c], w[c]); } return 1; }
static void count_sing(void) {
    int S[8][N], pat[4]; nsing = 0;
    for (int s = 0; s < 2; s++)
        for (pat[0] = 0; pat[0] < k; pat[0]++) for (pat[1] = 0; pat[1] < k; pat[1]++) if (pat[1] != pat[0])
        for (pat[2] = 0; pat[2] < k; pat[2]++) if (pat[2] != pat[1]) for (pat[3] = 0; pat[3] < k; pat[3]++) if (pat[3] != pat[2]) {
            int m = walkspan(s, pat, 4, S); if (rankv(S, m) < N) nsing++; } }
static void count_rest(void) {
    int S[8][N]; unc_p = 0; unc_d = 0;
    for (int s = 0; s < 2; s++) for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) if (i != j) {
        memset(mark, 0, Q4);
        for (int t = 0; t < k; t++) {
            int p1[4] = {t, t, i, j}, p2[4] = {i, t, t, j}, p3[4] = {i, j, t, t}; int m;
            m = walkspan(s, p1, 4, S); markspan(S, m); m = walkspan(s, p2, 4, S); markspan(S, m); m = walkspan(s, p3, 4, S); markspan(S, m); }
        for (int x = 0; x < Q4; x++) unc_p += !mark[x]; }
    for (int s = 0; s < 2; s++) {
        memset(mark, 0, Q4);
        for (int u = 0; u < k; u++) for (int v = 0; v < k; v++) { int p1[4] = {u, u, v, v}, p2[4] = {u, v, v, u}; int m;
            m = walkspan(s, p1, 4, S); markspan(S, m); m = walkspan(s, p2, 4, S); markspan(S, m); }
        for (int x = 0; x < Q4; x++) unc_d += !mark[x]; } }
/* cost, or any value > cutoff (the singular part alone) when the candidate is rejected early */
static double cut_cost(double cutoff) {
    if (!prep()) return 1e9;
    count_sing(); if (WS * nsing > cutoff) return WS * nsing;
    count_rest();
    return WS * nsing + WP * unc_p / (double)(q * q) + WD * unc_d / (double)(q * q); }
static double cost(void) { return cut_cost(1e18); }
/* move helpers: each commits to A[c]/b[c] only when it succeeds */
static int mv_fix_b(int c) {   /* R A_c with R b_c = b_c */
    int u[N], v[N], R[N][N], Rinv[N][N], T[N][N];
    for (int t = 0; t < N; t++) { u[t] = xr() % q; v[t] = xr() % q; }
    int p = 0; while (!b[c][p]) p++; int s = 0; for (int t = 0; t < N; t++) s = ADD[s][MUL[v[t]][b[c][t]]];
    v[p] = SUB[v[p]][MUL[s][INV[b[c][p]]]];
    for (int r = 0; r < N; r++) for (int t = 0; t < N; t++) R[r][t] = ADD[(r == t)][MUL[u[r]][v[t]]];
    if (!matinv(R, Rinv)) return 0;
    for (int r = 0; r < N; r++) for (int t = 0; t < N; t++) { int x = 0; for (int z = 0; z < N; z++) x = ADD[x][MUL[R[r][z]][A[c][z][t]]]; T[r][t] = x; }
    int Ti[N][N]; if (!matinv(T, Ti)) return 0;
    memcpy(A[c], T, sizeof T); return 1; }
static int mv_right(int c) {   /* A_c R with a random transvection R (moves w_c) */
    int u[N], v[N], R[N][N], Rinv[N][N], T[N][N];
    for (int t = 0; t < N; t++) { u[t] = xr() % q; v[t] = xr() % q; }
    for (int r = 0; r < N; r++) for (int t = 0; t < N; t++) R[r][t] = ADD[(r == t)][MUL[u[r]][v[t]]];
    if (!matinv(R, Rinv)) return 0;
    for (int r = 0; r < N; r++) for (int t = 0; t < N; t++) { int x = 0; for (int z = 0; z < N; z++) x = ADD[x][MUL[A[c][r][z]][R[z][t]]]; T[r][t] = x; }
    if (!matinv(T, Ai[c])) return 0;
    memcpy(A[c], T, sizeof T); return 1; }
static int mv_bentry(int c) {  /* one entry of b_c */
    int sb[N]; memcpy(sb, b[c], sizeof sb); b[c][xr() % N] = xr() % q;
    if (!b[c][0] && !b[c][1] && !b[c][2] && !b[c][3]) { memcpy(b[c], sb, sizeof sb); return 0; } return 1; }
static int mv_bpoint(int c) {  /* b_c <- random point, A_c <- M A_c with M b_c = b' (so w_c = A_c^-1 b_c is unchanged) */
    int bn[N], M[N][N], Mi[N][N], Mb[N], d[N], T[N][N], p = 0, nz = 0;
    do { for (int t = 0; t < N; t++) bn[t] = xr() % q; } while (!(bn[0] | bn[1] | bn[2] | bn[3]));
    while (!b[c][p]) p++;
    do { for (int r = 0; r < N; r++) for (int t = 0; t < N; t++) M[r][t] = xr() % q; } while (!matinv(M, Mi));
    matvec(M, b[c], Mb); for (int t = 0; t < N; t++) d[t] = SUB[bn[t]][Mb[t]];
    for (int r = 0; r < N; r++) M[r][p] = ADD[M[r][p]][MUL[d[r]][INV[b[c][p]]]];
    if (!matinv(M, Mi)) return 0;
    for (int r = 0; r < N; r++) for (int t = 0; t < N; t++) { int x = 0; for (int z = 0; z < N; z++) x = ADD[x][MUL[M[r][z]][A[c][z][t]]]; T[r][t] = x; }
    (void)nz;
    memcpy(A[c], T, sizeof T); memcpy(b[c], bn, sizeof bn); return 1; }
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: chart_anneal4 GFTABLE k seconds seed WS WP WD [out]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d", &q) != 1) return 2;
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) if (fscanf(f, "%d", &ADD[a][c]) != 1) return 3;
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) if (fscanf(f, "%d", &MUL[a][c]) != 1) return 3;
    fclose(f);
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) { if (MUL[a][c] == 1) INV[a] = c; if (ADD[a][c] == 0) NEG[a] = c; }
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) SUB[a][c] = ADD[a][NEG[c]];
    k = atoi(argv[2]); double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr();
    WS = atof(argv[5]); WP = atof(argv[6]); WD = atof(argv[7]); const char *out = argc > 8 ? argv[8] : NULL;
    Q4 = q * q * q * q; mark = malloc(Q4);
    double best = 1e18; int bA[8][N][N], bb[8][N];
    double t0 = wall(); long it = 0; int restarts = 0;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0;
    long STALL = getenv("STALL") ? atol(getenv("STALL")) : 20000; double TAU = getenv("TAU") ? atof(getenv("TAU")) : 4000.0;
    while ((wall() - t0) < secs && best > 0) {
        restarts++;
        if (getenv("INIT")) { FILE *g = fopen(getenv("INIT"), "r");
            for (int c = 0; c < k; c++) for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) if (fscanf(g, "%d", &A[c][r][s]) != 1) return 7;
            for (int c = 0; c < k; c++) for (int r = 0; r < N; r++) if (fscanf(g, "%d", &b[c][r]) != 1) return 7;
            fclose(g); }
        else for (int c = 0; c < k; c++) {
            do { for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) A[c][r][s] = c == 0 ? (r == s) : (int)(xr() % q); } while (!matinv(A[c], Ai[c]));
            do { for (int r = 0; r < N; r++) b[c][r] = xr() % q; } while (!b[c][0] && !b[c][1] && !b[c][2] && !b[c][3]); }
        double cur = cost(); long stall = 0;
        if (cur < best) { best = cur; memcpy(bA, A, sizeof bA); memcpy(bb, b, sizeof bb); if (out) write_gauged(out, A, b);
            printf("t=%.1fs best=%.3f (start)\n", wall() - t0, best); fflush(stdout); }
        while (stall < STALL && (wall() - t0) < secs && best > 0) {
            it++; int sA[N][N], sb[N]; int c = xr() % k, mm = xr() % 5;
            memcpy(sA, A[c], sizeof sA); memcpy(sb, b[c], sizeof sb);
            int ok = mm < 2 ? mv_fix_b(c) : mm == 2 ? mv_right(c) : mm == 3 ? mv_bentry(c) : mv_bpoint(c);
            if (!ok) continue;
            double u = (xr() % 1000000) / 1e6; double TT = T0 * exp(-(double)stall / TAU) + 0.05;
            double cutoff = u > 0 ? cur - TT * log(u) : 1e18;
            double nc = cut_cost(cutoff);
            if (nc <= cutoff) { if (nc < cur) stall = 0; else stall++; cur = nc; }
            else { memcpy(A[c], sA, sizeof sA); memcpy(b[c], sb, sizeof sb); stall++; }
            if (cur < best) { best = cur; memcpy(bA, A, sizeof bA); memcpy(bb, b, sizeof bb);
                if (out) write_gauged(out, A, b);
                printf("t=%.1fs best=%.3f it=%ld\n", (wall() - t0), best, it); fflush(stdout); }
        }
    }
    memcpy(A, bA, sizeof bA); memcpy(b, bb, sizeof bb); cost();
    printf("FINAL q=%d k=%d best=%.3f sing=%d unc_pencil=%d unc_diag=%d iters=%ld restarts=%d\n", q, k, best, nsing, unc_p, unc_d, it, restarts);
    if (out) write_gauged(out, A, b);
    return 0; }
