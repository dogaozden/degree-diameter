/* c3: largest set of pairwise opposite lines (partial spread) of H(q), q = 8.
   Conflict graph: lines L ~ L' iff distance <= 4 in the incidence graph (not opposite).
   Method: k-fixed tabu search (swap moves: drop the most conflicting set member, add the least conflicting
   outsider, tabu tenures), growing k each time a conflict-free set of size k is reached.
   Usage: tabu HEXBIN OUTFILE SEED SECONDS [INITFILE]
   OUTFILE is rewritten (whitespace-separated line ids) every time a larger valid set is found. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1, D, W;
static int32_t *LP, *PL;
static uint16_t *adj;
static uint64_t *bits;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int isadj(int u, int v) { return (int)((bits[(size_t)u * W + (v >> 6)] >> (v & 63)) & 1); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int *c, *Sl, *posS, k;
static char *inS;
static long long f;

static void add(int v) {
    f += c[v]; inS[v] = 1; posS[v] = k; Sl[k++] = v;
    const uint16_t *a = adj + (size_t)v * D;
    for (int i = 0; i < D; i++) c[a[i]]++;
}
static void removev(int u) {
    f -= c[u]; inS[u] = 0;
    int idx = posS[u]; Sl[idx] = Sl[--k]; posS[Sl[idx]] = idx;
    const uint16_t *a = adj + (size_t)u * D;
    for (int i = 0; i < D; i++) c[a[i]]--;
}
static void write_set(const char *fn, int *S, int n) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *g = fopen(tmp, "w"); if (!g) return;
    for (int i = 0; i < n; i++) fprintf(g, "%d\n", S[i]);
    fclose(g); rename(tmp, fn);
}
static void grow(void) {          /* add an outsider with the fewest conflicts (random ties) */
    int bv = -1, bval = 1 << 30, nt = 0;
    for (int v = 0; v < N; v++) { if (inS[v]) continue;
        if (c[v] < bval) { bval = c[v]; bv = v; nt = 1; }
        else if (c[v] == bval) { nt++; if (rnd() % nt == 0) bv = v; } }
    add(bv);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: tabu HEXBIN OUTFILE SEED SECONDS [INITFILE]\n"); return 2; }
    FILE *fp = fopen(argv[1], "rb"); if (!fp) { perror(argv[1]); return 2; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, fp) != 3) return 2;
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    if (hdr[2] != N) { fprintf(stderr, "bad header\n"); return 2; }
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, fp) != (size_t)N * Q1) return 2;
    fclose(fp);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1);
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int i = 0; i < Q1; i++) { int p = LP[(size_t)l * Q1 + i]; PL[(size_t)p * Q1 + cnt[p]++] = l; }
    for (int p = 0; p < N; p++) if (cnt[p] != Q1) { fprintf(stderr, "bad incidence\n"); return 2; }
    free(cnt);

    D = q * Q1 + q * q * q * Q1;           /* distance 2: q(q+1); distance 4: q^3(q+1) */
    adj = malloc(sizeof(uint16_t) * (size_t)N * D);
    W = (N + 63) / 64;
    bits = calloc((size_t)N * W, sizeof(uint64_t));
    for (int L = 0; L < N; L++) {
        uint16_t *a = adj + (size_t)L * D; int m = 0;
        for (int i = 0; i < Q1; i++) { int p = LP[(size_t)L * Q1 + i];
            for (int j = 0; j < Q1; j++) { int M = PL[(size_t)p * Q1 + j]; if (M == L) continue;
                a[m++] = (uint16_t)M;
                for (int t = 0; t < Q1; t++) { int r = LP[(size_t)M * Q1 + t]; if (r == p) continue;
                    for (int s = 0; s < Q1; s++) { int L2 = PL[(size_t)r * Q1 + s]; if (L2 == M) continue; a[m++] = (uint16_t)L2; } } } }
        if (m != D) { fprintf(stderr, "degree %d != %d at line %d\n", m, D, L); return 2; }
        for (int i = 0; i < D; i++) { int v = a[i]; bits[(size_t)L * W + (v >> 6)] |= 1ULL << (v & 63); }
    }
    for (int L = 0; L < N; L++) { int pc = 0; for (int w = 0; w < W; w++) pc += __builtin_popcountll(bits[(size_t)L * W + w]);
        if (pc != D) { fprintf(stderr, "duplicate conflict at %d\n", L); return 2; } }
    fprintf(stderr, "conflict graph built: N=%d D=%d\n", N, D);

    unsigned long long seed = strtoull(argv[3], 0, 10);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1; for (int i = 0; i < 20; i++) rnd();
    double secs = atof(argv[4]); const char *outfile = argv[2];

    c = calloc(N, sizeof(int)); inS = calloc(N, 1); Sl = malloc(sizeof(int) * N); posS = malloc(sizeof(int) * N);
    long long *tabuAdd = calloc(N, sizeof(long long)), *tabuRem = calloc(N, sizeof(long long));
    char *mark = calloc(N, 1);
    k = 0; f = 0;

    if (argc >= 6) {                      /* initial set from file */
        FILE *g = fopen(argv[5], "r"); int x;
        while (g && fscanf(g, "%d", &x) == 1) if (!inS[x] && c[x] == 0) add(x);
        if (g) fclose(g);
    }
    if (k == 0) {                         /* random greedy */
        int *perm = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) perm[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        for (int i = 0; i < N; i++) if (c[perm[i]] == 0 && !inS[perm[i]]) add(perm[i]);
        free(perm);
    }
    int bestk = k;
    write_set(outfile, Sl, k);
    fprintf(stderr, "start greedy/init size %d\n", k);
    printf("size %d (start)\n", k); fflush(stdout);

    double t0 = now(), tlast = t0; long long it = 0, last_imp = 0; long long bestf = f;
    while (1) {
        if (f == 0) {
            if (k > bestk) { bestk = k; write_set(outfile, Sl, k);
                printf("size %d at iter %lld t=%.1fs\n", k, it, now() - t0); fflush(stdout); }
            grow(); last_imp = it; bestf = f;
            continue;
        }
        it++;
        if ((it & 4095) == 0) {
            double tn = now();
            if (tn - t0 > secs) break;
            if (tn - tlast > 30) { tlast = tn; fprintf(stderr, "t=%.0f k=%d f=%lld it=%lld bestk=%d\n", tn - t0, k, f, it, bestk); }
        }
        /* stagnation: kick from the best known set */
        if (it - last_imp > 300000) {
            last_imp = it;
            int bkk = bestk;
            /* rebuild: best set (file) plus random kicks */
            while (k > 0) removev(Sl[k - 1]);
            FILE *g = fopen(outfile, "r"); int x;
            while (g && fscanf(g, "%d", &x) == 1) if (!inS[x] && c[x] == 0) add(x);
            if (g) fclose(g);
            for (int r = 0; r < 4 && k > 0; r++) { int v = Sl[rnd() % k]; removev(v); }
            while (k < bkk + 1) grow();
            bestf = f;
            continue;
        }
        /* remove: non-tabu member with the most conflicts */
        int bu = -1, bc = -1, nt = 0;
        for (int i = 0; i < k; i++) { int u = Sl[i]; if (tabuRem[u] > (long long)it) continue;
            if (c[u] > bc) { bc = c[u]; bu = u; nt = 1; }
            else if (c[u] == bc) { nt++; if (rnd() % nt == 0) bu = u; } }
        if (bu < 0 || bc == 0) { do { bu = Sl[rnd() % k]; } while (c[bu] == 0); }
        int u = bu;
        /* add: non-tabu outsider minimizing conflicts after removing u */
        const uint16_t *au = adj + (size_t)u * D;
        for (int i = 0; i < D; i++) mark[au[i]] = 1;
        int bv = -1, bval = 1 << 30; nt = 0;
        for (int v = 0; v < N; v++) {
            if (inS[v] || tabuAdd[v] > (long long)it) continue;
            int val = c[v] - mark[v];
            if (val < bval) { bval = val; bv = v; nt = 1; }
            else if (val == bval) { nt++; if (rnd() % nt == 0) bv = v; }
        }
        for (int i = 0; i < D; i++) mark[au[i]] = 0;
        if (bv < 0) continue;
        removev(u);
        add(bv);
        tabuAdd[u] = (long long)it + 7 + (long long)(rnd() % 10);
        tabuRem[bv] = (long long)it + 2 + (long long)(rnd() % 4);
        if (f < bestf) { bestf = f; last_imp = it; }
    }
    printf("FINAL best valid size %d, iterations %lld, time %.1fs\n", bestk, it, now() - t0);
    return 0;
}
