/* ls6.c: card c6 (squad r4, H(5) partial ovoid / partial spread).
   Min-conflicts tabu search for large sets of pairwise opposite points (or lines) of the generalized hexagon H(q).
   Conflict = distance 2 or 4 in the incidence graph (i.e. not opposite). Conflict graph is 780-regular for q = 5.
   Grows a conflict-free set greedily, then for size k+1 runs tabu swaps (u out, v in) that minimise the number of
   conflicting pairs, until conflict-free or the time limit is reached.
   Usage: ls6 HEXBIN points|lines SECONDS SEED OUTPREFIX
   After each size reached, writes OUTPREFIX_best.txt (whitespace-separated ids, sorted). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <limits.h>

static int q, N, Q1, Lc;
static int *LP, *PL, *conf, D;
static int *cnt, *Sarr, *posS, k;
static unsigned char *inS, *nb;
static long long *tabuIn, *tabuOut;
static long long F;
static uint64_t rs;
static const long long PERT = 60000;   /* iterations without improvement before a random perturbation */
static const int PERT_SWAPS = 3;
static const char *prefix;
static int isline;

static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int n) { return (int)(xr() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

/* BFS in the incidence graph: nodes 0..N-1 points, N..2N-1 lines. */
static void bfs(int s, unsigned char *d, int *qu) {
    memset(d, 255, 2 * N);
    int h = 0, t = 0; d[s] = 0; qu[t++] = s;
    while (h < t) {
        int v = qu[h++]; int dv = d[v];
        if (v < N) {
            for (int j = 0; j < Q1; j++) { int w = N + PL[v * Q1 + j]; if (d[w] == 255) { d[w] = dv + 1; qu[t++] = w; } }
        } else {
            int l = v - N;
            for (int j = 0; j < Q1; j++) { int w = LP[l * Q1 + j]; if (d[w] == 255) { d[w] = dv + 1; qu[t++] = w; } }
        }
    }
}

static void build(void) {
    unsigned char *d = malloc(2 * N); int *qu = malloc(sizeof(int) * 2 * N);
    D = 0; conf = NULL;
    int base = isline ? N : 0;
    for (int x = 0; x < N; x++) {
        bfs(isline ? N + x : x, d, qu);
        int c = 0;
        for (int y = 0; y < N; y++) {
            int dd = d[base + y];
            if (y != x && (dd == 2 || dd == 4)) c++;
        }
        if (x == 0) { D = c; conf = malloc(sizeof(int) * (size_t)N * D); }
        if (c != D) { fprintf(stderr, "non-regular conflict graph: %d vs %d\n", c, D); exit(1); }
        c = 0;
        for (int y = 0; y < N; y++) {
            int dd = d[base + y];
            if (y != x && (dd == 2 || dd == 4)) conf[(size_t)x * D + c++] = y;
        }
    }
    free(d); free(qu);
    fprintf(stderr, "conflict graph: %s, N=%d, degree %d\n", isline ? "lines" : "points", N, D);
}

static void addv(int v) {
    inS[v] = 1; posS[v] = k; Sarr[k++] = v;
    const int *cv = conf + (size_t)v * D;
    for (int i = 0; i < D; i++) cnt[cv[i]]++;
}

static void remv(int v) {
    inS[v] = 0; int p = posS[v]; int last = Sarr[--k]; Sarr[p] = last; posS[last] = p; posS[v] = -1;
    const int *cv = conf + (size_t)v * D;
    for (int i = 0; i < D; i++) cnt[cv[i]]--;
}

static long long recountF(void) { long long s = 0; for (int i = 0; i < k; i++) s += cnt[Sarr[i]]; return s / 2; }

static int cmpint(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return (x > y) - (x < y); }

static void save_best(void) {
    char fn[1024]; snprintf(fn, sizeof fn, "%s_best.txt", prefix);
    int *tmp = malloc(sizeof(int) * (k + 1)); memcpy(tmp, Sarr, sizeof(int) * k);
    qsort(tmp, k, sizeof(int), cmpint);
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); exit(1); }
    for (int i = 0; i < k; i++) fprintf(f, "%d\n", tmp[i]);
    fclose(f); free(tmp);
}

static void perturb(void) {
    for (int t = 0; t < PERT_SWAPS; t++) {
        int u = Sarr[rndn(k)];
        int v; do { v = rndn(N); } while (inS[v]);
        remv(u); addv(v);
    }
    F = recountF();
}

/* tabu search at the current size k until F == 0 (returns 1) or the deadline passes (returns 0) */
static int search_level(double deadline) {
    long long it = 0, bestF = F, lastImp = 0;
    while (F > 0) {
        it++;
        if ((it & 0x3FFF) == 0) {
            if (now() > deadline) return 0;
            if ((it & 0xFFFFF) == 0) fprintf(stderr, "  k=%d F=%lld bestF=%lld it=%lld\n", k, F, bestF, it);
        }
        /* u in S: most conflicts among non-tabu members (random tie) */
        int bu = -1, bcu = -1, nt = 0;
        for (int i = 0; i < k; i++) {
            int s = Sarr[i];
            if (tabuOut[s] > it) continue;
            int cu = cnt[s];
            if (cu > bcu) { bcu = cu; bu = s; nt = 1; }
            else if (cu == bcu && rndn(++nt) == 0) bu = s;
        }
        if (bu < 0) { bu = Sarr[rndn(k)]; bcu = cnt[bu]; }
        /* v outside: minimise cnt[v] - adj(bu, v) over non-tabu vertices (random tie) */
        const int *cu_list = conf + (size_t)bu * D;
        for (int i = 0; i < D; i++) nb[cu_list[i]] = 1;
        int bv = -1, bcv = INT_MAX; nt = 0;
        for (int v = 0; v < N; v++) {
            if (inS[v] || tabuIn[v] > it) continue;
            int val = cnt[v] - nb[v];
            if (val < bcv) { bcv = val; bv = v; nt = 1; }
            else if (val == bcv && rndn(++nt) == 0) bv = v;
        }
        for (int i = 0; i < D; i++) nb[cu_list[i]] = 0;
        if (bv < 0) continue;
        long long delta = (long long)bcv - bcu;
        remv(bu); addv(bv);
        F += delta;
        tabuIn[bu] = it + 7 + rndn(10 + (int)(F > 0 ? F : 0));
        tabuOut[bv] = it + 1 + rndn(4);
        if (F < bestF) { bestF = F; lastImp = it; }
        if (it - lastImp > PERT) { perturb(); bestF = F; lastImp = it; }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ls6 HEXBIN points|lines SECONDS SEED OUTPREFIX\n"); return 2; }
    isline = !strcmp(argv[2], "lines");
    double secs = atof(argv[3]);
    rs = strtoull(argv[4], NULL, 10) * 2654435761ULL + 88172645463325252ULL; if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) xr();
    prefix = argv[5];

    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3];
    if (!f || fread(hdr, 4, 3, f) != 3) { fprintf(stderr, "cannot read header\n"); return 2; }
    q = hdr[0]; N = hdr[1]; Lc = hdr[2]; Q1 = q + 1;
    LP = malloc(sizeof(int) * (size_t)Lc * Q1);
    if (fread(LP, 4, (size_t)Lc * Q1, f) != (size_t)Lc * Q1) { fprintf(stderr, "short read\n"); return 2; }
    fclose(f);
    PL = malloc(sizeof(int) * (size_t)N * Q1);
    int *c = calloc(N, sizeof(int));
    for (int l = 0; l < Lc; l++) for (int j = 0; j < Q1; j++) { int p = LP[l * Q1 + j]; PL[p * Q1 + c[p]++] = l; }
    free(c);
    build();

    cnt = calloc(N, sizeof(int)); Sarr = malloc(sizeof(int) * N); posS = malloc(sizeof(int) * N);
    inS = calloc(N, 1); nb = calloc(N, 1);
    tabuIn = calloc(N, sizeof(long long)); tabuOut = calloc(N, sizeof(long long));
    for (int v = 0; v < N; v++) posS[v] = -1;
    k = 0;
    int *perm = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rndn(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < N; i++) if (cnt[perm[i]] == 0) addv(perm[i]);
    F = recountF();
    fprintf(stderr, "greedy start size %d\n", k);
    save_best();
    int best = k;

    double t0 = now(), deadline = t0 + secs;
    while (now() < deadline) {
        /* extend by the outside vertex with fewest conflicts (random tie) */
        int bv = -1, bc = INT_MAX, nt = 0;
        for (int v = 0; v < N; v++) {
            if (inS[v]) continue;
            if (cnt[v] < bc) { bc = cnt[v]; bv = v; nt = 1; }
            else if (cnt[v] == bc && rndn(++nt) == 0) bv = v;
        }
        addv(bv); F = recountF();
        if (!search_level(deadline)) { fprintf(stderr, "time out at k=%d (target conflicts F=%lld)\n", k, F); break; }
        if (k > best) { best = k; save_best(); }
        fprintf(stderr, "FOUND k=%d at %.1fs\n", k, now() - t0);
    }
    /* final sanity: independence of the saved set */
    if (F == 0) { /* current set is conflict free and is the best */ }
    printf("best size %d -> %s_best.txt\n", best, prefix);
    return 0;
}
