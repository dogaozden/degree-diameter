/* ls6w.c: card c6 (squad r4). Breakout / edge-weighting local search for large sets of pairwise opposite points
   (or lines) of H(q). Conflict = distance 2 or 4 in the incidence graph. Maintains a set S of size k and the number of
   conflicting pairs F; a swap (u out, v in) is taken when it lowers the weighted conflict sum; at a local minimum the
   weights of the conflicting pairs inside S are raised by 1 (breakout). Level k+1 is started when F = 0.
   Usage: ls6w HEXBIN points|lines SECONDS SEED OUTPREFIX [START_FILE|-]
   Writes OUTPREFIX_best.txt after every size reached. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <limits.h>

static int q, N, Q1, Lc, D, k, isline;
static int *LP, *PL, *conf, *Sarr, *posS;
static int *cnt;                  /* number of S-neighbours */
static long long *Wsum;           /* weighted sum over S-neighbours */
static uint32_t *w;               /* w[a*N+b] weight of conflicting pair (a,b) */
static unsigned char *inS, *nb, *allowed;
static long long *tabuIn;
static long long F;
static uint64_t rs;
static const char *prefix;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int n) { return (int)(xr() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void bfs(int s, unsigned char *d, int *qu) {
    memset(d, 255, 2 * N);
    int h = 0, t = 0; d[s] = 0; qu[t++] = s;
    while (h < t) {
        int v = qu[h++]; int dv = d[v];
        if (v < N) { for (int j = 0; j < Q1; j++) { int x = N + PL[v * Q1 + j]; if (d[x] == 255) { d[x] = dv + 1; qu[t++] = x; } } }
        else { int l = v - N; for (int j = 0; j < Q1; j++) { int x = LP[l * Q1 + j]; if (d[x] == 255) { d[x] = dv + 1; qu[t++] = x; } } }
    }
}
static void build(void) {
    unsigned char *d = malloc(2 * N); int *qu = malloc(sizeof(int) * 2 * N);
    int base = isline ? N : 0; D = 780; conf = malloc(sizeof(int) * (size_t)N * D);
    for (int x = 0; x < N; x++) {
        bfs(isline ? N + x : x, d, qu); int c = 0;
        for (int y = 0; y < N; y++) { int dd = d[base + y]; if (y != x && (dd == 2 || dd == 4)) { if (c >= D) { fprintf(stderr, "degree\n"); exit(1); } conf[(size_t)x * D + c++] = y; } }
        if (c != D) { fprintf(stderr, "non-regular conflict graph\n"); exit(1); }
    }
    free(d); free(qu);
}
static void addv(int v) {
    inS[v] = 1; posS[v] = k; Sarr[k++] = v;
    const int *cv = conf + (size_t)v * D;
    for (int i = 0; i < D; i++) { int x = cv[i]; cnt[x]++; Wsum[x] += w[(size_t)x * N + v]; }
}
static void remv(int v) {
    inS[v] = 0; int p = posS[v]; int last = Sarr[--k]; Sarr[p] = last; posS[last] = p; posS[v] = -1;
    const int *cv = conf + (size_t)v * D;
    for (int i = 0; i < D; i++) { int x = cv[i]; cnt[x]--; Wsum[x] -= w[(size_t)x * N + v]; }
}
static long long recountF(void) { long long s = 0; for (int i = 0; i < k; i++) s += cnt[Sarr[i]]; return s / 2; }
static int cmpint(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return (x > y) - (x < y); }
static void save_best(void) {
    char fn[1024]; snprintf(fn, sizeof fn, "%s_best.txt", prefix);
    int *tmp = malloc(sizeof(int) * (k + 1)); memcpy(tmp, Sarr, sizeof(int) * k); qsort(tmp, k, sizeof(int), cmpint);
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); exit(1); }
    for (int i = 0; i < k; i++) fprintf(f, "%d\n", tmp[i]);
    fclose(f); free(tmp);
}
/* raise the weight of every conflicting pair inside S by one */
static void bump_weights(void) {
    for (int i = 0; i < k; i++) {
        int u = Sarr[i]; const int *cu = conf + (size_t)u * D;
        for (int j = 0; j < D; j++) {
            int x = cu[j];
            if (inS[x] && u < x) {
                w[(size_t)u * N + x]++; w[(size_t)x * N + u]++;
                Wsum[u]++; Wsum[x]++;
            }
        }
    }
}
static int search_level(double deadline) {
    long long it = 0;
    while (F > 0) {
        it++;
        if ((it & 0x3FF) == 0 && now() > deadline) return 0;
        /* u: member of S with largest weighted conflict (random tie) */
        int bu = -1; long long bWu = -1; int nt = 0;
        for (int i = 0; i < k; i++) {
            int s = Sarr[i]; long long val = Wsum[s];
            if (val > bWu) { bWu = val; bu = s; nt = 1; }
            else if (val == bWu && rndn(++nt) == 0) bu = s;
        }
        /* v: outside vertex with smallest weighted conflict after removing u (random tie) */
        const int *cu = conf + (size_t)bu * D;
        for (int i = 0; i < D; i++) nb[cu[i]] = 1;
        int bv = -1; long long bWv = LLONG_MAX; nt = 0;
        for (int v = 0; v < N; v++) {
            if (inS[v] || !allowed[v] || tabuIn[v] > it) continue;
            long long val = Wsum[v] - (nb[v] ? (long long)w[(size_t)bu * N + v] : 0);
            if (val < bWv) { bWv = val; bv = v; nt = 1; }
            else if (val == bWv && rndn(++nt) == 0) bv = v;
        }
        for (int i = 0; i < D; i++) nb[cu[i]] = 0;
        if (bv < 0) continue;
        long long dW = bWv - bWu;
        if (dW < 0) {
            F -= cnt[bu];
            int adjuv = 0; /* cnt[bv] counts bu if adjacent */
            for (int i = 0; i < D; i++) if (cu[i] == bv) { adjuv = 1; break; }
            F += cnt[bv] - adjuv;
            remv(bu); addv(bv);
            tabuIn[bu] = it + 3;
        } else {
            bump_weights();   /* local minimum of the weighted sum: breakout */
            F = recountF();   /* weights do not change F, kept for safety */
        }
        if ((it & 0xFFFFF) == 0) fprintf(stderr, "  k=%d F=%lld it=%lld\n", k, F, it);
    }
    return 1;
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ls6w HEXBIN points|lines SECONDS SEED OUTPREFIX [START_FILE|-]\n"); return 2; }
    isline = !strcmp(argv[2], "lines"); double secs = atof(argv[3]);
    rs = strtoull(argv[4], NULL, 10) * 2654435761ULL + 88172645463325252ULL; if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) xr();
    prefix = argv[5];
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3];
    if (!f || fread(hdr, 4, 3, f) != 3) return 2;
    q = hdr[0]; N = hdr[1]; Lc = hdr[2]; Q1 = q + 1;
    LP = malloc(sizeof(int) * (size_t)Lc * Q1);
    if (fread(LP, 4, (size_t)Lc * Q1, f) != (size_t)Lc * Q1) return 2;
    fclose(f);
    PL = malloc(sizeof(int) * (size_t)N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < Lc; l++) for (int j = 0; j < Q1; j++) { int p = LP[l * Q1 + j]; PL[p * Q1 + c[p]++] = l; }
    free(c);
    build();
    cnt = calloc(N, sizeof(int)); Wsum = calloc(N, sizeof(long long)); Sarr = malloc(sizeof(int) * N); posS = malloc(sizeof(int) * N);
    inS = calloc(N, 1); nb = calloc(N, 1); allowed = malloc(N); memset(allowed, 1, N); tabuIn = calloc(N, sizeof(long long));
    w = malloc(sizeof(uint32_t) * (size_t)N * N);
    for (size_t i = 0; i < (size_t)N * N; i++) w[i] = 1;
    for (int v = 0; v < N; v++) posS[v] = -1;
    k = 0;
    int use_start = (argc >= 7 && strcmp(argv[6], "-") != 0);
    if (!use_start) {
        int *perm = malloc(sizeof(int) * N);
        for (int i = 0; i < N; i++) perm[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rndn(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        for (int i = 0; i < N; i++) if (cnt[perm[i]] == 0) addv(perm[i]);
        free(perm);
    } else {
        FILE *g = fopen(argv[6], "r"); int x;
        if (!g) { perror(argv[6]); return 2; }
        while (fscanf(g, "%d", &x) == 1) if (x >= 0 && x < N && !inS[x] && cnt[x] == 0) addv(x);
        fclose(g);
    }
    F = recountF();
    fprintf(stderr, "start size %d\n", k);
    save_best();
    int best = k;
    double t0 = now(), deadline = t0 + secs;
    while (now() < deadline) {
        int bv = -1; long long bc = LLONG_MAX; int nt = 0;
        for (int v = 0; v < N; v++) {
            if (inS[v]) continue;
            if (Wsum[v] < bc) { bc = Wsum[v]; bv = v; nt = 1; }
            else if (Wsum[v] == bc && rndn(++nt) == 0) bv = v;
        }
        addv(bv); F = recountF();
        if (!search_level(deadline)) { fprintf(stderr, "time out at k=%d F=%lld\n", k, F); break; }
        if (k > best) { best = k; save_best(); }
        fprintf(stderr, "FOUND k=%d at %.1fs\n", k, now() - t0);
    }
    printf("best size %d -> %s_best.txt\n", best, prefix);
    return 0;
}
