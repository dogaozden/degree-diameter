/* Simulated annealing for route charts over F_q^4 with k letters (k <= 8, q <= 16).
   cost = WS * (#singular nonbacktracking 4-patterns, both sides)
        + WP * (uncovered vectors in the one-detour unions of all (side,i,j) pencils) / q^2
        + WD * (uncovered vectors in the closed-backtracking union, both sides) / q^2
   Reachable sets are computed from the step rules: A->B along c: S -> A_c S + <b_c>; B->A: S -> A_c^-1 S + <w_c>.
   usage: chart_anneal GFTABLE k seconds seed WS WP WD [out.txt]
   Output format = squad165/charts/*.txt (k lines of 16 entries A_c row-major, k lines of b_c). A_0 = I (gauge).
   r3 variant (chart_anneal2): env INIT=chart.txt starts every restart from that chart (A_0 must be I); env T0 (default 2)
   and STALL (default 20000) set the temperature and the restart patience; env TAU (default 4000) the cooling length. */
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
static double cost(void) {
    int S[8][N], pat[4];
    for (int c = 0; c < k; c++) { if (!matinv(A[c], Ai[c])) return 1e9; matvec(Ai[c], b[c], w[c]); }
    nsing = 0;
    if (WS > 0) for (int s = 0; s < 2; s++)
        for (pat[0] = 0; pat[0] < k; pat[0]++) for (pat[1] = 0; pat[1] < k; pat[1]++) if (pat[1] != pat[0])
        for (pat[2] = 0; pat[2] < k; pat[2]++) if (pat[2] != pat[1]) for (pat[3] = 0; pat[3] < k; pat[3]++) if (pat[3] != pat[2]) {
            int m = walkspan(s, pat, 4, S); if (rankv(S, m) < N) nsing++; }
    unc_p = 0;
    if (WP > 0) for (int s = 0; s < 2; s++) for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) if (i != j) {
        memset(mark, 0, Q4);
        for (int t = 0; t < k; t++) {
            int p1[4] = {t, t, i, j}, p2[4] = {i, t, t, j}, p3[4] = {i, j, t, t}; int m;
            m = walkspan(s, p1, 4, S); markspan(S, m); m = walkspan(s, p2, 4, S); markspan(S, m); m = walkspan(s, p3, 4, S); markspan(S, m); }
        for (int x = 0; x < Q4; x++) unc_p += !mark[x]; }
    unc_d = 0;
    if (WD > 0) for (int s = 0; s < 2; s++) {
        memset(mark, 0, Q4);
        for (int u = 0; u < k; u++) for (int v = 0; v < k; v++) { int p1[4] = {u, u, v, v}, p2[4] = {u, v, v, u}; int m;
            m = walkspan(s, p1, 4, S); markspan(S, m); m = walkspan(s, p2, 4, S); markspan(S, m); }
        for (int x = 0; x < Q4; x++) unc_d += !mark[x]; }
    return WS * nsing + WP * unc_p / (double)(q * q) + WD * unc_d / (double)(q * q); }
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: chart_anneal GFTABLE k seconds seed WS WP WD [out]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d", &q) != 1) return 2;
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) if (fscanf(f, "%d", &ADD[a][c]) != 1) return 3;
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) if (fscanf(f, "%d", &MUL[a][c]) != 1) return 3;
    fclose(f);
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) { if (MUL[a][c] == 1) INV[a] = c; if (ADD[a][c] == 0) NEG[a] = c; }
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) SUB[a][c] = ADD[a][NEG[c]];
    k = atoi(argv[2]); double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr();
    WS = atof(argv[5]); WP = atof(argv[6]); WD = atof(argv[7]); const char *out = argc > 8 ? argv[8] : NULL;
    Q4 = q * q * q * q; mark = (WP > 0 || WD > 0) ? malloc(Q4) : NULL;
    double best = 1e18; int bA[8][N][N], bb[8][N];
    double t0 = wall(); long it = 0; int restarts = 0;
    while ((wall() - t0) < secs && best > 0) {
        restarts++;
        if (getenv("INIT")) { FILE *g = fopen(getenv("INIT"), "r");
            for (int c = 0; c < k; c++) for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) if (fscanf(g, "%d", &A[c][r][s]) != 1) return 7;
            for (int c = 0; c < k; c++) for (int r = 0; r < N; r++) if (fscanf(g, "%d", &b[c][r]) != 1) return 7;
            fclose(g); }
        else for (int c = 0; c < k; c++) {
            do { for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) A[c][r][s] = c == 0 ? (r == s) : (int)(xr() % q); } while (!matinv(A[c], Ai[c]));
            do { for (int r = 0; r < N; r++) b[c][r] = xr() % q; } while (!b[c][0] && !b[c][1] && !b[c][2] && !b[c][3]); }
        double cur = cost(); double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0; long stall = 0;
        long STALL = getenv("STALL") ? atol(getenv("STALL")) : 20000; double TAU = getenv("TAU") ? atof(getenv("TAU")) : 4000.0;
        while (stall < STALL && (wall() - t0) < secs) {
            it++; int sA[N][N], sb[N]; int c = xr() % k, mv = xr() % 3;
            memcpy(sA, A[c], sizeof sA); memcpy(sb, b[c], sizeof sb);
            if (mv < 2 && c > 0) { A[c][xr() % N][xr() % N] = xr() % q; if (!matinv(A[c], Ai[c])) { memcpy(A[c], sA, sizeof sA); continue; } }
            else { b[c][xr() % N] = xr() % q; if (!b[c][0] && !b[c][1] && !b[c][2] && !b[c][3]) { memcpy(b[c], sb, sizeof sb); continue; } }
            double nc = cost(); double TT = T0 * exp(-(double)stall / TAU) + 0.05;
            if (nc <= cur || exp((cur - nc) / TT) > (double)(xr() % 1000000) / 1e6) { if (nc < cur) stall = 0; else stall++; cur = nc; }
            else { memcpy(A[c], sA, sizeof sA); memcpy(b[c], sb, sizeof sb); stall++; }
            if (cur < best) { best = cur; memcpy(bA, A, sizeof bA); memcpy(bb, b, sizeof bb);
                if (out) { FILE *g = fopen(out, "w");
                    for (int c = 0; c < k; c++) { for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) fprintf(g, "%d ", A[c][r][s]); fprintf(g, "\n"); }
                    for (int c = 0; c < k; c++) { for (int r = 0; r < N; r++) fprintf(g, "%d ", b[c][r]); fprintf(g, "\n"); }
                    fclose(g); }
                printf("t=%.1fs best=%.3f sing=%d unc_pencil=%d unc_diag=%d\n", (wall() - t0), best, nsing, unc_p, unc_d); fflush(stdout); if (best == 0) break; }
        }
    }
    memcpy(A, bA, sizeof bA); memcpy(b, bb, sizeof bb); cost();
    printf("FINAL q=%d k=%d best=%.3f sing=%d unc_pencil=%d unc_diag=%d iters=%ld restarts=%d\n", q, k, best, nsing, unc_p, unc_d, it, restarts);
    if (out) { FILE *g = fopen(out, "w");
        for (int c = 0; c < k; c++) { for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) fprintf(g, "%d ", A[c][r][s]); fprintf(g, "\n"); }
        for (int c = 0; c < k; c++) { for (int r = 0; r < N; r++) fprintf(g, "%d ", b[c][r]); fprintf(g, "\n"); }
        fclose(g); }
    return 0; }
