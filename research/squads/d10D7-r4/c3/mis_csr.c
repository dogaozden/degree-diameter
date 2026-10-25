/* c3: k-fixed tabu search for a maximum independent set in the orbit conflict graph (CSR, binary input from
   orbit7.py). Each vertex is an orbit of 7 lines under a diagonal order-7 automorphism of H(8); a set of
   pairwise non-conflicting orbits is a partial spread of 7 x (number of orbits) lines.
   Usage: mis_csr GRAPHBIN OUTLINES SEED SECONDS */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int n, m; static int *mem, *off, *nb, *bestset; static uint64_t *bits; static int W;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int isadj(int u, int v) { return (int)((bits[(size_t)u * W + (v >> 6)] >> (v & 63)) & 1); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int *c, *Sl, *posS, k; static char *inS; static long long f;
static void add(int v) { f += c[v]; inS[v] = 1; posS[v] = k; Sl[k++] = v; for (int i = off[v]; i < off[v + 1]; i++) c[nb[i]]++; }
static void removev(int u) { f -= c[u]; inS[u] = 0; int idx = posS[u]; Sl[idx] = Sl[--k]; posS[Sl[idx]] = idx; for (int i = off[u]; i < off[u + 1]; i++) c[nb[i]]--; }
static void write_sol(const char *fn, int *S, int cnt) {
    FILE *g = fopen(fn, "w"); if (!g) return;
    for (int i = 0; i < cnt; i++) for (int j = 0; j < m; j++) fprintf(g, "%d\n", mem[S[i] * m + j]);
    fclose(g);
}
static void grow(void) { int bv = -1, bval = 1 << 30, nt = 0;
    for (int v = 0; v < n; v++) { if (inS[v]) continue;
        if (c[v] < bval) { bval = c[v]; bv = v; nt = 1; } else if (c[v] == bval) { nt++; if (rnd() % nt == 0) bv = v; } }
    add(bv); }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: mis_csr GRAPHBIN OUTLINES SEED SECONDS\n"); return 2; }
    FILE *fp = fopen(argv[1], "rb"); int hdr[2]; if (!fp || fread(hdr, 4, 2, fp) != 2) return 2;
    n = hdr[0]; m = hdr[1];
    mem = malloc(sizeof(int) * n * m); if (fread(mem, 4, (size_t)n * m, fp) != (size_t)n * m) return 2;
    off = malloc(sizeof(int) * (n + 1)); if (fread(off, 4, n + 1, fp) != (size_t)(n + 1)) return 2;
    int E2 = off[n]; nb = malloc(sizeof(int) * (E2 > 0 ? E2 : 1)); if (fread(nb, 4, E2, fp) != (size_t)E2) return 2; fclose(fp);
    W = (n + 63) / 64; bits = calloc((size_t)n * W, 8);
    for (int v = 0; v < n; v++) for (int i = off[v]; i < off[v + 1]; i++) { int w = nb[i]; bits[(size_t)v * W + (w >> 6)] |= 1ULL << (w & 63); }
    fprintf(stderr, "orbit graph n=%d m=%d degree~%.1f\n", n, m, (double)E2 / n);
    unsigned long long seed = strtoull(argv[3], 0, 10); rs ^= (seed + 3) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1; for (int i = 0; i < 20; i++) rnd();
    double secs = atof(argv[4]); const char *outfile = argv[2];
    c = calloc(n, sizeof(int)); inS = calloc(n, 1); Sl = malloc(sizeof(int) * n); posS = malloc(sizeof(int) * n);
    long long *tabuAdd = calloc(n, sizeof(long long)), *tabuRem = calloc(n, sizeof(long long));
    char *mark = calloc(n, 1);
    int *perm = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < n; i++) if (c[perm[i]] == 0 && !inS[perm[i]]) add(perm[i]);
    bestset = malloc(sizeof(int) * n);
    int bestk = k; memcpy(bestset, Sl, sizeof(int) * k); write_sol(outfile, Sl, k); printf("orbits %d (lines %d) start\n", k, 7 * k); fflush(stdout);
    double t0 = now(), tl = t0; long long it = 0, last_imp = 0; long long bestf = f;
    while (1) {
        if (f == 0) {
            if (k > bestk) { bestk = k; memcpy(bestset, Sl, sizeof(int) * k); write_sol(outfile, Sl, k); printf("orbits %d (lines %d) at iter %lld t=%.1fs\n", k, 7 * k, it, now() - t0); fflush(stdout); }
            grow(); last_imp = it; bestf = f; continue;
        }
        it++;
        if ((it & 4095) == 0) { double tn = now(); if (tn - t0 > secs) break;
            if (tn - tl > 30) { tl = tn; fprintf(stderr, "t=%.0f k=%d f=%lld it=%lld bestk=%d\n", tn - t0, k, f, it, bestk); } }
        if (it - last_imp > 200000) {       /* kick: rebuild from best and drop 3 random members */
            last_imp = it; int bkk = bestk;
            while (k > 0) removev(Sl[k - 1]);
            for (int i = 0; i < bkk; i++) add(bestset[i]);
            for (int r = 0; r < 3 && k > 0; r++) removev(Sl[rnd() % k]);
            while (k < bkk + 1) grow();
            bestf = f; continue;
        }
        int bu = -1, bc = -1, nt = 0;
        for (int i = 0; i < k; i++) { int u = Sl[i]; if (tabuRem[u] > (long long)it) continue;
            if (c[u] > bc) { bc = c[u]; bu = u; nt = 1; } else if (c[u] == bc) { nt++; if (rnd() % nt == 0) bu = u; } }
        if (bu < 0 || bc == 0) { do { bu = Sl[rnd() % k]; } while (c[bu] == 0); }
        int u = bu;
        for (int i = off[u]; i < off[u + 1]; i++) mark[nb[i]] = 1;
        int bv = -1, bval = 1 << 30; nt = 0;
        for (int v = 0; v < n; v++) {
            if (inS[v] || tabuAdd[v] > (long long)it) continue;
            int val = c[v] - mark[v];
            if (val < bval) { bval = val; bv = v; nt = 1; } else if (val == bval) { nt++; if (rnd() % nt == 0) bv = v; }
        }
        for (int i = off[u]; i < off[u + 1]; i++) mark[nb[i]] = 0;
        if (bv < 0) continue;
        removev(u); add(bv);
        tabuAdd[u] = (long long)it + 7 + (long long)(rnd() % 10);
        tabuRem[bv] = (long long)it + 2 + (long long)(rnd() % 4);
        if (f < bestf) { bestf = f; last_imp = it; }
        if (k > bestk) { /* valid-size bookkeeping happens at f==0 */ }
    }
    printf("FINAL best orbits %d = %d lines, iterations %lld, time %.1fs\n", bestk, 7 * bestk, it, now() - t0);
    return 0;
}
