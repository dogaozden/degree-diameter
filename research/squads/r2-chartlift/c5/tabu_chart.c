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
/* Tabu search over single GF(2) bit flips (A_c entries for c>=1, b_c entries; A_0 = I fixed).
   Every step evaluates the whole neighbourhood (84 flips for k=5), takes the best non-tabu move (aspiration on
   global best), restarts from the best state after PATIENCE steps without improvement (with a few random flips).
   usage: tabu_chart GFTABLE k seconds seed WS WP WD out.txt   (env INIT=chart.txt optional, TENURE default 9) */
static void dump(const char *out, int (*AA)[N][N], int (*bb)[N]) { FILE *g = fopen(out, "w");
    for (int c = 0; c < k; c++) { for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) fprintf(g, "%d ", AA[c][r][s]); fprintf(g, "\n"); }
    for (int c = 0; c < k; c++) { for (int r = 0; r < N; r++) fprintf(g, "%d ", bb[c][r]); fprintf(g, "\n"); }
    fclose(g); }
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: tabu_chart GFTABLE k seconds seed WS WP WD out\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d", &q) != 1) return 2;
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) if (fscanf(f, "%d", &ADD[a][c]) != 1) return 3;
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) if (fscanf(f, "%d", &MUL[a][c]) != 1) return 3;
    fclose(f);
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) { if (MUL[a][c] == 1) INV[a] = c; if (ADD[a][c] == 0) NEG[a] = c; }
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) SUB[a][c] = ADD[a][NEG[c]];
    if (q != 2) { fprintf(stderr, "q must be 2 (bit flips)\n"); return 1; }
    k = atoi(argv[2]); double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr();
    WS = atof(argv[5]); WP = atof(argv[6]); WD = atof(argv[7]); const char *out = argv[8];
    int TEN = getenv("TENURE") ? atoi(getenv("TENURE")) : 9; int PAT = getenv("PATIENCE") ? atoi(getenv("PATIENCE")) : 400;
    Q4 = q * q * q * q; mark = malloc(Q4);
    /* init: INIT chart if given, else identity A_c for c>0 with random b */
    for (int c = 0; c < k; c++) for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) A[c][r][s] = (r == s);
    for (int c = 0; c < k; c++) for (int r = 0; r < N; r++) b[c][r] = xr() % 2;
    if (getenv("INIT")) { FILE *g = fopen(getenv("INIT"), "r");
        for (int c = 0; c < k; c++) for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) if (fscanf(g, "%d", &A[c][r][s]) != 1) return 7;
        for (int c = 0; c < k; c++) for (int r = 0; r < N; r++) if (fscanf(g, "%d", &b[c][r]) != 1) return 7;
        fclose(g); }
    else for (int c = 1; c < k; c++) { do { for (int r = 0; r < N; r++) for (int s = 0; s < N; s++) A[c][r][s] = xr() % 2; } while (!matinv(A[c], Ai[c])); }
    /* move index m in [0, NM): m < 64*(k-1)? -> A entries: colour 1+m/16, entry m%16; then b entries */
    int NA = 16 * (k - 1), NM = NA + 4 * k;
    int tabu_until[256] = {0};
    double cur = cost(); double best = cur; int bA[8][N][N], bb[8][N]; memcpy(bA, A, sizeof bA); memcpy(bb, b, sizeof bb);
    dump(out, A, b); printf("start cost=%.3f sing=%d unc_pencil=%d unc_diag=%d\n", cur, nsing, unc_p, unc_d); fflush(stdout);
    double t0 = wall(); long step = 0; long since = 0; int restarts = 0;
    while (wall() - t0 < secs && best > 0) {
        step++;
        double bestnc = 1e18; int bm = -1;
        for (int m = 0; m < NM; m++) {
            int c, r, s; int isA = m < NA;
            if (isA) { c = 1 + m / 16; r = (m % 16) / 4; s = m % 4; } else { int mm = m - NA; c = mm / 4; r = mm % 4; }
            /* flip */
            if (isA) { A[c][r][s] ^= 1; if (!matinv(A[c], Ai[c])) { A[c][r][s] ^= 1; continue; } }
            else { b[c][r] ^= 1; if (!b[c][0] && !b[c][1] && !b[c][2] && !b[c][3]) { b[c][r] ^= 1; continue; } }
            double nc = cost();
            if (isA) A[c][r][s] ^= 1; else b[c][r] ^= 1;
            if (isA) matinv(A[c], Ai[c]);
            int tabu = tabu_until[m] > step;
            if ((!tabu || nc < best) && nc < bestnc) { bestnc = nc; bm = m; }
        }
        if (bm < 0) { /* all tabu: random move */ bm = xr() % NM; }
        { int m = bm; int isA = m < NA; int c, r, s;
          if (isA) { c = 1 + m / 16; r = (m % 16) / 4; s = m % 4; A[c][r][s] ^= 1; matinv(A[c], Ai[c]); }
          else { int mm = m - NA; c = mm / 4; r = mm % 4; b[c][r] ^= 1; }
          tabu_until[m] = step + TEN + (int)(xr() % 5);
          cur = cost();
        }
        if (cur < best) { best = cur; memcpy(bA, A, sizeof bA); memcpy(bb, b, sizeof bb); since = 0; dump(out, bA, bb);
            printf("step %ld t=%.1fs best=%.3f sing=%d unc_pencil=%d unc_diag=%d\n", step, wall() - t0, best, nsing, unc_p, unc_d); fflush(stdout); }
        else since++;
        if (since > PAT) { /* restart from best with random perturbation */
            restarts++; since = 0; memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b);
            for (int j = 0; j < 3; j++) { int m = xr() % NM; if (m < NA) { int c = 1 + m / 16; int r = (m % 16) / 4, s = m % 4; A[c][r][s] ^= 1; if (!matinv(A[c], Ai[c])) A[c][r][s] ^= 1; }
                else { int mm = m - NA; b[mm / 4][mm % 4] ^= 1; } }
            for (int c = 1; c < k; c++) if (!matinv(A[c], Ai[c])) { memcpy(A, bA, sizeof A); break; }
            cur = cost(); }
    }
    memcpy(A, bA, sizeof bA); memcpy(b, bb, sizeof bb); cost();
    printf("FINAL best=%.3f sing=%d unc_pencil=%d unc_diag=%d steps=%ld restarts=%d\n", best, nsing, unc_p, unc_d, step, restarts);
    dump(out, bA, bb);
    return 0; }
