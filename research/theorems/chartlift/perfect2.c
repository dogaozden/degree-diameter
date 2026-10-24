/* D-perfect route charts over F_2^n, n = D - 1 <= 8, k letters <= 8.
   The controller's universal cover is the k-regular tree = Cayley graph of Z_2 * ... * Z_2 (k copies); a walk is a
   colour word, its endpoint is the reduced word.  A chart is D-PERFECT if for both start sides and every reduced word y
   with |y| <= n, |y| = n mod 2, the walks (words) of length n that reduce to y have spans whose union is F_2^n.
   Then every k-regular bipartite controller of diameter <= D lifts to a (2k)-regular bipartite graph of diameter <= D
   (CHART_LIFTS.md, Theorem P).  Step rules: A->B along c: S -> A_c S + <b_c>; B->A: S -> A_c^-1 S + <w_c>.
   cost = total number of uncovered (target, vector) pairs over both sides.
   usage: perfect2 k D seconds seed [out.txt] [start.txt]     (out/start: k lines n*n bits of A_c row-major, k lines b_c bits) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
int k, D, n, NW;                 /* NW = number of 64-bit words per mask (2^n bits) */
int A[8][8], Ai[8][8], b[8], w[8];   /* A[c][r] = row r as n-bit int; vectors are n-bit ints */
static int matvec(const int *M, int v) { int out = 0; for (int r = 0; r < n; r++) out |= (__builtin_popcount(M[r] & v) & 1) << r; return out; }
static int inv(const int *M, int *R) {
    int a[8], e[8]; for (int r = 0; r < n; r++) { a[r] = M[r]; e[r] = 1 << r; }
    for (int c = 0; c < n; c++) { int p = -1; for (int r = c; r < n; r++) if (a[r] >> c & 1) { p = r; break; } if (p < 0) return 0;
        int t = a[p]; a[p] = a[c]; a[c] = t; t = e[p]; e[p] = e[c]; e[c] = t;
        for (int r = 0; r < n; r++) if (r != c && (a[r] >> c & 1)) { a[r] ^= a[c]; e[r] ^= e[c]; } }
    for (int r = 0; r < n; r++) R[r] = e[r]; return 1; }
static const uint64_t BM[6] = {0x5555555555555555ULL, 0x3333333333333333ULL, 0x0F0F0F0F0F0F0F0FULL, 0x00FF00FF00FF00FFULL, 0x0000FFFF0000FFFFULL, 0x00000000FFFFFFFFULL};
static void xorshift_mask(const uint64_t *m, int v, uint64_t *out) {   /* out[x ^ v] = m[x] as bitsets */
    for (int i = 0; i < NW; i++) out[i ^ (v >> 6)] = m[i];
    for (int j = 0; j < 6 && j < n; j++) if (v >> j & 1) for (int i = 0; i < NW; i++) { uint64_t x = out[i]; out[i] = ((x & BM[j]) << (1 << j)) | ((x >> (1 << j)) & BM[j]); } }
static void span_mask(const int *vec, int m, uint64_t *mask) {
    for (int i = 0; i < NW; i++) mask[i] = 0; mask[0] = 1; uint64_t t[4];
    for (int i = 0; i < m; i++) { if (!vec[i]) continue; xorshift_mask(mask, vec[i], t); for (int j = 0; j < NW; j++) mask[j] |= t[j]; } }
/* targets: reduced words, indexed by a trie over the free product */
int ntarget; int *child;            /* child[node*k + c] = node id or -1; node 0 = empty word */
uint64_t *cov;                      /* cov[(side*ntarget + node)*NW + i] */
static int new_node(void) { for (int c = 0; c < k; c++) child[ntarget * k + c] = -1; return ntarget++; }
int vecs[17][17];
int path_nodes[17], path_last[17], plen;   /* the reduced word so far, as a path in the trie */
unsigned char *tpar;
static void dfs(int side, int depth, int cur_side, int nv) {
    if (depth == n) { uint64_t m[4]; span_mask(vecs[depth], nv, m); uint64_t *c = cov + ((size_t)side * ntarget + path_nodes[plen]) * NW; for (int i = 0; i < NW; i++) c[i] |= m[i]; return; }
    for (int c = 0; c < k; c++) {
        int *src = vecs[depth], *dst = vecs[depth + 1];
        if (cur_side == 0) { for (int i = 0; i < nv; i++) dst[i] = matvec(A[c], src[i]); dst[nv] = b[c]; }
        else { for (int i = 0; i < nv; i++) dst[i] = matvec(Ai[c], src[i]); dst[nv] = w[c]; }
        int saved = plen, sl = plen > 0 ? path_last[plen - 1] : -1, sn = path_nodes[plen];
        if (plen > 0 && path_last[plen - 1] == c) plen--;
        else { path_nodes[plen + 1] = child[path_nodes[plen] * k + c]; path_last[plen] = c; plen++; }
        dfs(side, depth + 1, 1 - cur_side, nv + 1);
        plen = saved; if (saved > 0) path_last[saved - 1] = sl; path_nodes[saved] = sn;
    }
}
static long uncovered(void) {
    long u = 0; uint64_t full = n < 6 ? ((1ULL << (1 << n)) - 1) : ~0ULL;
    for (int s = 0; s < 2; s++) for (int t = 0; t < ntarget; t++) { if (!tpar[t]) continue;
        uint64_t *c = cov + ((size_t)s * ntarget + t) * NW; for (int i = 0; i < NW; i++) u += __builtin_popcountll(~c[i] & full); }
    return u; }
static long cost(void) {
    for (int c = 0; c < k; c++) { if (!inv(A[c], Ai[c])) return 1L << 40; if (!b[c]) return 1L << 40; w[c] = matvec(Ai[c], b[c]); }
    memset(cov, 0, sizeof(uint64_t) * 2 * ntarget * NW);
    for (int s = 0; s < 2; s++) { plen = 0; path_nodes[0] = 0; dfs(s, 0, s, 0); }
    return uncovered(); }
static void build_trie(int node, int depth, int last, int *dep) {
    if (depth == n) return;
    for (int c = 0; c < k; c++) { if (c == last) continue; int id = new_node(); child[node * k + c] = id; dep[id] = depth + 1; build_trie(id, depth + 1, c, dep); } }
static void save(const char *fn) { FILE *f = fopen(fn, "w");
    for (int c = 0; c < k; c++) { for (int r = 0; r < n; r++) for (int s = 0; s < n; s++) fprintf(f, "%d ", A[c][r] >> s & 1); fprintf(f, "\n"); }
    for (int c = 0; c < k; c++) { for (int r = 0; r < n; r++) fprintf(f, "%d ", b[c] >> r & 1); fprintf(f, "\n"); } fclose(f); }
static int load(const char *fn) { FILE *f = fopen(fn, "r"); if (!f) return 0;
    for (int c = 0; c < k; c++) { A[c][0] = 0; for (int r = 0; r < n; r++) { A[c][r] = 0; for (int s = 0; s < n; s++) { int x; if (fscanf(f, "%d", &x) != 1) return 0; A[c][r] |= x << s; } } }
    for (int c = 0; c < k; c++) { b[c] = 0; for (int r = 0; r < n; r++) { int x; if (fscanf(f, "%d", &x) != 1) return 0; b[c] |= x << r; } } fclose(f); return 1; }
int main(int argc, char **argv) {
    k = atoi(argv[1]); D = atoi(argv[2]); n = D - 1; double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr();
    const char *out = argc > 5 ? argv[5] : NULL, *start = argc > 6 ? argv[6] : NULL;
    NW = n <= 6 ? 1 : (1 << (n - 6));
    long maxnodes = 1; for (int d = 0, p = 1; d <= n; d++) { maxnodes += p; p *= (d == 0 ? k : k - 1); }
    child = malloc(sizeof(int) * maxnodes * k); int *dep = malloc(sizeof(int) * maxnodes);
    ntarget = 0; new_node(); dep[0] = 0; build_trie(0, 0, -1, dep);
    tpar = malloc(ntarget); for (int t = 0; t < ntarget; t++) tpar[t] = (dep[t] % 2) == (n % 2);
    cov = malloc(sizeof(uint64_t) * 2 * ntarget * NW);
    int nt = 0; for (int t = 0; t < ntarget; t++) nt += tpar[t];
    printf("k=%d D=%d n=%d targets per side %d, vectors %d, words %ld\n", k, D, n, nt, 1 << n, (long)pow(k, n)); fflush(stdout);
    if (getenv("EVAL")) { if (!load(getenv("EVAL"))) { printf("bad chart\n"); return 1; } printf("EVAL cost=%ld\n", cost());
        long byd[2][17] = {{0}}; long cnt[17] = {0}; uint64_t full = n < 6 ? ((1ULL << (1 << n)) - 1) : ~0ULL;
        for (int s = 0; s < 2; s++) for (int t = 0; t < ntarget; t++) { if (!tpar[t]) continue; if (s == 0) cnt[dep[t]]++;
            uint64_t *c = cov + ((size_t)s * ntarget + t) * NW; for (int i = 0; i < NW; i++) byd[s][dep[t]] += __builtin_popcountll(~c[i] & full); }
        for (int d = 0; d <= n; d++) if (cnt[d]) printf("  |y|=%d targets/side %ld: uncovered A %ld B %ld (of %ld each)\n", d, cnt[d], byd[0][d], byd[1][d], cnt[d] << n);
        return 0; }
    long best = -1; int bA[8][8], bb[8]; double t0 = wall(); long it = 0;
    while (wall() - t0 < secs && best != 0) {
        if (!(start && load(start))) for (int c = 0; c < k; c++) {
            do { for (int r = 0; r < n; r++) A[c][r] = c == 0 ? (1 << r) : (int)(xr() & ((1 << n) - 1)); } while (!inv(A[c], Ai[c]));
            do b[c] = xr() & ((1 << n) - 1); while (!b[c]); }
        start = NULL;
        long cur = cost(); if (best < 0 || cur < best) { best = cur; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); if (out) save(out); }
        long stall = 0;
        while (stall < 20000 && best != 0 && wall() - t0 < secs) {
            it++; int sA[8][8], sb[8]; memcpy(sA, A, sizeof A); memcpy(sb, b, sizeof b);
            int c = xr() % k, mv = xr() % 4;
            if (mv < 3 && c > 0) { A[c][xr() % n] ^= 1 << (xr() % n); if (!inv(A[c], Ai[c])) { memcpy(A, sA, sizeof A); continue; } }
            else { b[c] ^= 1 << (xr() % n); if (!b[c]) { memcpy(b, sb, sizeof b); continue; } }
            long nc = cost(); double TT = 3.0 * exp(-(double)stall / 3000.0) + 0.3;
            if (nc <= cur || exp((cur - nc) / TT) > (double)(xr() % 1000000) / 1e6) { if (nc < cur) stall = 0; else stall++; cur = nc;
                if (cur < best) { best = cur; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); if (out) save(out);
                    printf("t=%.1f best=%ld it=%ld\n", wall() - t0, best, it); fflush(stdout); } }
            else { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); stall++; } } }
    memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); long c = cost();
    printf("FINAL k=%d D=%d best=%ld (recomputed %ld) iters=%ld\n", k, D, best, c, it);
    if (out) save(out);
    return 0; }
