/* D-perfect route charts over F_q^n (n = D - 1 <= 8, q^n <= 2^20), k letters <= 6.  Same definition as perfect2.c:
   for both start sides and every reduced colour word y (free product of k copies of Z_2) with |y| <= n, |y| = n mod 2,
   the spans of all words of length n reducing to y must cover F_q^n.  Spans of full rank cover their target at once;
   others are enumerated into a bitset.  cost = uncovered (target, vector) pairs over both sides.
   usage: perfectq GFTABLE k D seconds seed [out.txt] [start.txt];  EVAL=chart.txt perfectq GFTABLE k D 0 0
   chart file: k lines of n*n entries (A_c row-major), then k lines of n entries (b_c). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
int q, k, D, n, QN, ADD[16][16], MUL[16][16], INV[16], NEG[16], SUB[16][16];
int A[6][8][8], Ai[6][8][8], b[6][8], w[6][8];
static void matvec(int M[8][8], const int *v, int *o) { for (int r = 0; r < n; r++) { int s = 0; for (int c = 0; c < n; c++) s = ADD[s][MUL[M[r][c]][v[c]]]; o[r] = s; } }
static int matinv(int M[8][8], int R[8][8]) {
    int T[8][16]; for (int r = 0; r < n; r++) for (int c = 0; c < 2 * n; c++) T[r][c] = c < n ? M[r][c] : (c - n == r);
    for (int c = 0; c < n; c++) { int p = -1; for (int r = c; r < n; r++) if (T[r][c]) { p = r; break; } if (p < 0) return 0;
        if (p != c) for (int t = 0; t < 2 * n; t++) { int x = T[c][t]; T[c][t] = T[p][t]; T[p][t] = x; }
        int iv = INV[T[c][c]]; for (int t = 0; t < 2 * n; t++) T[c][t] = MUL[iv][T[c][t]];
        for (int r = 0; r < n; r++) if (r != c && T[r][c]) { int f = T[r][c]; for (int t = 0; t < 2 * n; t++) T[r][t] = SUB[T[r][t]][MUL[f][T[c][t]]]; } }
    for (int r = 0; r < n; r++) for (int c = 0; c < n; c++) R[r][c] = T[r][c + n]; return 1; }
/* reduce a list of m vectors to an echelon basis; returns rank, basis in B */
static int echelon(int (*V)[8], int m, int (*B)[8]) {
    int r = 0; int T[16][8]; memcpy(T, V, sizeof(int) * 8 * m);
    for (int c = 0; c < n && r < m; c++) { int p = -1; for (int i = r; i < m; i++) if (T[i][c]) { p = i; break; } if (p < 0) continue;
        if (p != r) for (int t = 0; t < n; t++) { int x = T[r][t]; T[r][t] = T[p][t]; T[p][t] = x; }
        int iv = INV[T[r][c]]; for (int t = 0; t < n; t++) T[r][t] = MUL[iv][T[r][t]];
        for (int i = 0; i < m; i++) if (i != r && T[i][c]) { int f = T[i][c]; for (int t = 0; t < n; t++) T[i][t] = SUB[T[i][t]][MUL[f][T[r][t]]]; }
        r++; }
    memcpy(B, T, sizeof(int) * 8 * r); return r; }
int pw[9];
static int code(const int *v) { int c = 0; for (int t = n - 1; t >= 0; t--) c = c * q + v[t]; return c; }
int ntarget, *child, *dep; unsigned char *tpar, *full; uint64_t *cov; int WPT;   /* words per target bitset */
static void mark_span(int (*Bs)[8], int r, uint64_t *bits) {
    int tot = 1; for (int i = 0; i < r; i++) tot *= q;
    for (int idx = 0; idx < tot; idx++) { int v[8] = {0}, x = idx;
        for (int i = 0; i < r; i++) { int c = x % q; x /= q; if (c) for (int t = 0; t < n; t++) v[t] = ADD[v[t]][MUL[c][Bs[i][t]]]; }
        int cd = code(v); bits[cd >> 6] |= 1ULL << (cd & 63); } }
int vecs[17][17][8]; int path_nodes[17], path_last[17], plen;
int *pdim; int (*pbasis)[8][8]; int (*ppiv)[8];          /* per (side, node): path span echelon basis and pivot columns */
static void path_spans(int side, int node, int cur_side, int nv, int (*V)[8], int last) {
    int id = side * ntarget + node; int Bs[16][8]; int r = echelon(V, nv, Bs); pdim[id] = r;
    for (int i = 0; i < r; i++) { memcpy(pbasis[id][i], Bs[i], sizeof(int) * 8); int c = 0; while (!Bs[i][c]) c++; ppiv[id][i] = c; }
    if (dep[node] == n) return;
    int W2[17][8];
    for (int c = 0; c < k; c++) { if (c == last) continue;
        if (cur_side == 0) { for (int i = 0; i < nv; i++) matvec(A[c], V[i], W2[i]); memcpy(W2[nv], b[c], sizeof(int) * 8); }
        else { for (int i = 0; i < nv; i++) matvec(Ai[c], V[i], W2[i]); memcpy(W2[nv], w[c], sizeof(int) * 8); }
        path_spans(side, child[node * k + c], 1 - cur_side, nv + 1, W2, c); } }
/* reduce v modulo the path span of target id, return quotient coordinates in out (length n - pdim) */
static void quot(int id, const int *v, int *out) {
    int x[8]; memcpy(x, v, sizeof x); int r = pdim[id];
    for (int i = 0; i < r; i++) { int c = ppiv[id][i]; if (x[c]) { int f = x[c]; for (int t = 0; t < n; t++) x[t] = SUB[x[t]][MUL[f][pbasis[id][i][t]]]; } }
    int j = 0; for (int c = 0; c < n; c++) { int isp = 0; for (int i = 0; i < r; i++) if (ppiv[id][i] == c) isp = 1; if (!isp) out[j++] = x[c]; } }
static void dfs(int side, int depth, int cur_side, int nv) {
    if (depth == n) { int t = side * ntarget + path_nodes[plen]; if (full[t]) return;
        int m = n - pdim[t]; if (m == 0) { full[t] = 1; return; }
        int Qv[16][8]; for (int i = 0; i < nv; i++) { int o[8] = {0}; quot(t, vecs[depth][i], o); memset(Qv[i], 0, sizeof(int) * 8); memcpy(Qv[i], o, sizeof(int) * m); }
        int savedn = n; n = m; int Bs[16][8]; int r = echelon(Qv, nv, Bs);
        if (r == m) { full[t] = 1; n = savedn; return; }
        mark_span(Bs, r, cov + (size_t)t * WPT); n = savedn; return; }
    for (int c = 0; c < k; c++) {
        if (cur_side == 0) { for (int i = 0; i < nv; i++) matvec(A[c], vecs[depth][i], vecs[depth + 1][i]); memcpy(vecs[depth + 1][nv], b[c], sizeof(int) * 8); }
        else { for (int i = 0; i < nv; i++) matvec(Ai[c], vecs[depth][i], vecs[depth + 1][i]); memcpy(vecs[depth + 1][nv], w[c], sizeof(int) * 8); }
        int saved = plen, sl = plen > 0 ? path_last[plen - 1] : -1, sn = path_nodes[plen];
        if (plen > 0 && path_last[plen - 1] == c) plen--;
        else { path_nodes[plen + 1] = child[path_nodes[plen] * k + c]; path_last[plen] = c; plen++; }
        dfs(side, depth + 1, 1 - cur_side, nv + 1);
        plen = saved; if (saved > 0) path_last[saved - 1] = sl; path_nodes[saved] = sn; } }
long byd[2][17];
static long cost(void) {
    for (int c = 0; c < k; c++) { if (!matinv(A[c], Ai[c])) return 1L << 40; int nz = 0; for (int t = 0; t < n; t++) nz |= b[c][t]; if (!nz) return 1L << 40; matvec(Ai[c], b[c], w[c]); }
    memset(cov, 0, sizeof(uint64_t) * 2 * ntarget * WPT); memset(full, 0, 2 * ntarget);
    for (int s = 0; s < 2; s++) { int V0[17][8]; path_spans(s, 0, s, 0, V0, -1); }
    for (int s = 0; s < 2; s++) { plen = 0; path_nodes[0] = 0; dfs(s, 0, s, 0); }
    long u = 0; memset(byd, 0, sizeof byd);
    for (int s = 0; s < 2; s++) for (int t = 0; t < ntarget; t++) { if (!tpar[t]) continue; int id = s * ntarget + t; long un;
        if (full[id]) un = 0; else { long have = 0; uint64_t *c = cov + (size_t)id * WPT; for (int i = 0; i < WPT; i++) have += __builtin_popcountll(c[i]);
            long qm = 1, qp = 1; for (int i = 0; i < n - pdim[id]; i++) qm *= q; for (int i = 0; i < pdim[id]; i++) qp *= q; un = (qm - have) * qp; }
        u += un; byd[s][dep[t]] += un; }
    return u; }
static int new_node(void) { for (int c = 0; c < k; c++) child[ntarget * k + c] = -1; return ntarget++; }
static void build_trie(int node, int depth, int last) {
    if (depth == n) return;
    for (int c = 0; c < k; c++) { if (c == last) continue; int id = new_node(); child[node * k + c] = id; dep[id] = depth + 1; build_trie(id, depth + 1, c); } }
static void save(const char *fn) { FILE *f = fopen(fn, "w");
    for (int c = 0; c < k; c++) { for (int r = 0; r < n; r++) for (int s = 0; s < n; s++) fprintf(f, "%d ", A[c][r][s]); fprintf(f, "\n"); }
    for (int c = 0; c < k; c++) { for (int r = 0; r < n; r++) fprintf(f, "%d ", b[c][r]); fprintf(f, "\n"); } fclose(f); }
static int load(const char *fn) { FILE *f = fopen(fn, "r"); if (!f) return 0;
    for (int c = 0; c < k; c++) for (int r = 0; r < n; r++) for (int s = 0; s < n; s++) if (fscanf(f, "%d", &A[c][r][s]) != 1) return 0;
    for (int c = 0; c < k; c++) for (int r = 0; r < n; r++) if (fscanf(f, "%d", &b[c][r]) != 1) return 0; fclose(f); return 1; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &q) != 1) return 2;
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) if (fscanf(f, "%d", &ADD[a][c]) != 1) return 3;
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) if (fscanf(f, "%d", &MUL[a][c]) != 1) return 3; fclose(f);
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) { if (MUL[a][c] == 1) INV[a] = c; if (ADD[a][c] == 0) NEG[a] = c; }
    for (int a = 0; a < q; a++) for (int c = 0; c < q; c++) SUB[a][c] = ADD[a][NEG[c]];
    k = atoi(argv[2]); D = atoi(argv[3]); n = D - 1; double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; xr();
    const char *out = argc > 6 ? argv[6] : NULL, *start = argc > 7 ? argv[7] : NULL;
    QN = 1; for (int i = 0; i < n; i++) QN *= q; WPT = (QN + 63) / 64;
    long maxnodes = 1; for (int d = 0, p = 1; d <= n; d++) { maxnodes += p; p *= (d == 0 ? k : k - 1); }
    child = malloc(sizeof(int) * maxnodes * k); dep = malloc(sizeof(int) * maxnodes);
    ntarget = 0; new_node(); dep[0] = 0; build_trie(0, 0, -1);
    tpar = malloc(ntarget); for (int t = 0; t < ntarget; t++) tpar[t] = (dep[t] % 2) == (n % 2);
    cov = malloc(sizeof(uint64_t) * 2 * ntarget * WPT); full = malloc(2 * ntarget);
    pdim = malloc(sizeof(int) * 2 * ntarget); pbasis = malloc(sizeof(int) * 64 * 2 * ntarget); ppiv = malloc(sizeof(int) * 8 * 2 * ntarget);
    int nt = 0; for (int t = 0; t < ntarget; t++) nt += tpar[t];
    printf("q=%d k=%d D=%d n=%d targets per side %d, vectors %d, words %.0f\n", q, k, D, n, nt, QN, pow(k, n)); fflush(stdout);
    if (getenv("EVAL")) { if (!load(getenv("EVAL"))) { printf("bad chart\n"); return 1; } printf("EVAL cost=%ld\n", cost());
        for (int d = 0; d <= n; d++) if (byd[0][d] || byd[1][d] || d == n) printf("  |y|=%d uncovered A %ld B %ld\n", d, byd[0][d], byd[1][d]); return 0; }
    long best = -1; int bA[6][8][8], bb[6][8]; double t0 = wall(); long it = 0;
    while (wall() - t0 < secs && best != 0) {
        if (!(start && load(start))) for (int c = 0; c < k; c++) {
            do { for (int r = 0; r < n; r++) for (int s = 0; s < n; s++) A[c][r][s] = c == 0 ? (r == s) : (int)(xr() % q); } while (!matinv(A[c], Ai[c]));
            int nz; do { nz = 0; for (int r = 0; r < n; r++) { b[c][r] = xr() % q; nz |= b[c][r]; } } while (!nz); }
        start = NULL;
        long cur = cost(); if (best < 0 || cur < best) { best = cur; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); if (out) save(out); }
        long stall = 0;
        while (stall < 5000 && best != 0 && wall() - t0 < secs) {
            it++; int sA[6][8][8], sb[6][8]; memcpy(sA, A, sizeof A); memcpy(sb, b, sizeof b);
            int c = xr() % k, mv = xr() % 4;
            if (mv < 3 && c > 0) { A[c][xr() % n][xr() % n] = xr() % q; if (!matinv(A[c], Ai[c])) { memcpy(A, sA, sizeof A); continue; } }
            else { b[c][xr() % n] = xr() % q; int nz = 0; for (int r = 0; r < n; r++) nz |= b[c][r]; if (!nz) { memcpy(b, sb, sizeof b); continue; } }
            long nc = cost(); double TT = 0.02 * QN * exp(-(double)stall / 1000.0) + 1.0;
            if (nc <= cur || exp((cur - nc) / TT) > (double)(xr() % 1000000) / 1e6) { if (nc < cur) stall = 0; else stall++; cur = nc;
                if (cur < best) { best = cur; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); if (out) save(out);
                    printf("t=%.1f best=%ld it=%ld\n", wall() - t0, best, it); fflush(stdout); } }
            else { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); stall++; } } }
    memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); long c = cost();
    printf("FINAL q=%d k=%d D=%d best=%ld (recomputed %ld) iters=%ld\n", q, k, D, best, c, it);
    for (int d = 0; d <= n; d++) if (byd[0][d] || byd[1][d]) printf("  |y|=%d uncovered A %ld B %ld\n", d, byd[0][d], byd[1][d]);
    if (out) save(out);
    return 0; }
