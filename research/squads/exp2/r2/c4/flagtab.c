/* flagtab.c: conflict measures for freed flags (p,l) (p on l) of the generalized hexagon H(q), card c4 of exp2 r2.
   S'(p,l) = {u point : d(p,u)=4, d(l,u)=5},  S(p,l) = {N line : d(l,N)=4, d(p,N)=5}   (d = incidence-graph distance)
   For two flags 1,2: a = |S'1 n S'2| (points), b = |S1 n S2| (lines).
   Exact covers M(S'_j) = S_j for all j (M a bijection points->lines) force M(S'1 n S'2) = S1 n S2, so a = b is needed;
   the pairwise mismatch is 2|a-b| (points that cannot be matched type-by-type). Also compat: a freed point's own
   line must lie in S of the other flag exactly when the point lies in S' of the other flag.
   usage:
     flagtab HEX table NREF SEED            per 4-distance class (d(p1,p2), d(l1,l2), d(p1,l2), d(p2,l1)): a, b, compat
     flagtab HEX eval FLAGS                 K flags ("p l" per line): pairwise sum, exact K-wise mass mismatch U, compat
     flagtab HEX random K SEED MIND OUT     K random flags with pairwise point distance >= MIND
     flagtab HEX greedy K SEED MIND OUT     greedy: add flags with minimal pairwise weight (w = 2|a-b| + 2*compat fails)
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q, N, Q1, W2;
static int32_t *LP, *PL;
static uint8_t *DP, *DL;     /* DP[p*W2+v] = d(point p, v), DL[l*W2+v] = d(line l, v); v<N point, v>=N line */

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) exit(1);
    q = hdr[0]; N = hdr[1]; Q1 = q + 1; W2 = 2 * N;
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1);
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1);
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + cnt[p]++] = l; }
    free(cnt);
}

static void bfs_inc(int s, uint8_t *d, int *qq) {
    memset(d, 255, W2);
    int h = 0, t = 0; d[s] = 0; qq[t++] = s;
    while (h < t) {
        int v = qq[h++]; int dv = d[v];
        if (v < N) { for (int k = 0; k < Q1; k++) { int w = N + PL[v * Q1 + k]; if (d[w] == 255) { d[w] = dv + 1; qq[t++] = w; } } }
        else { int l = v - N; for (int k = 0; k < Q1; k++) { int w = LP[l * Q1 + k]; if (d[w] == 255) { d[w] = dv + 1; qq[t++] = w; } } }
    }
}

static void build_dist(void) {
    DP = malloc((size_t)N * W2); DL = malloc((size_t)N * W2);
    int *qq = malloc(sizeof(int) * W2);
    for (int p = 0; p < N; p++) bfs_inc(p, DP + (size_t)p * W2, qq);
    for (int l = 0; l < N; l++) bfs_inc(N + l, DL + (size_t)l * W2, qq);
    free(qq);
}

/* 4 distances of flags 1=(p1,l1), 2=(p2,l2): t0=d(p1,p2) t1=d(l1,l2) t2=d(p1,l2) t3=d(l1,p2) */
static inline void tuple_of(int p1, int l1, int p2, int l2, int *t) {
    t[0] = DP[(size_t)p1 * W2 + p2];
    t[1] = DL[(size_t)l1 * W2 + N + l2];
    t[2] = DP[(size_t)p1 * W2 + N + l2];
    t[3] = DL[(size_t)l1 * W2 + p2];
}
static inline int cls_index(const int *t) { return ((t[0] / 2) * 4 + t[1] / 2) * 9 + ((t[2] - 1) / 2) * 3 + (t[3] - 1) / 2; }
static inline int compat(const int *t) {
    int c1 = ((t[0] == 4 && t[3] == 5) == (t[1] == 4 && t[2] == 5));
    int c2 = ((t[0] == 4 && t[2] == 5) == (t[1] == 4 && t[3] == 5));
    return c1 && c2;
}
static void pair_ab(int p1, int l1, int p2, int l2, int *a, int *b) {
    const uint8_t *dp1 = DP + (size_t)p1 * W2, *dl1 = DL + (size_t)l1 * W2, *dp2 = DP + (size_t)p2 * W2, *dl2 = DL + (size_t)l2 * W2;
    int aa = 0, bb = 0;
    for (int u = 0; u < N; u++) aa += (dp1[u] == 4 && dl1[u] == 5 && dp2[u] == 4 && dl2[u] == 5);
    for (int x = N; x < W2; x++) bb += (dl1[x] == 4 && dp1[x] == 5 && dl2[x] == 4 && dp2[x] == 5);
    *a = aa; *b = bb;
}
static void random_flag(int *p, int *l) { *p = rndi(N); *l = PL[(*p) * Q1 + rndi(Q1)]; }

static const char *ctname[144];

static void cmd_table(int nref, uint64_t seed) {
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    static int cnt[144], amn[144], amx[144], bmn[144], bmx[144], nc[144], rep[144][4], ok[144];
    for (int i = 0; i < 144; i++) { cnt[i] = 0; amn[i] = 1 << 30; amx[i] = -1; bmn[i] = 1 << 30; bmx[i] = -1; nc[i] = 0; ok[i] = 1; }
    for (int r = 0; r < nref; r++) {
        int p1, l1; random_flag(&p1, &l1);
        for (int p2 = 0; p2 < N; p2++) for (int k = 0; k < Q1; k++) {
            int l2 = PL[p2 * Q1 + k], t[4], a, b;
            tuple_of(p1, l1, p2, l2, t);
            int id = cls_index(t);
            pair_ab(p1, l1, p2, l2, &a, &b);
            if (cnt[id] == 0) { for (int i = 0; i < 4; i++) rep[id][i] = t[i]; }
            cnt[id]++; nc[id] += compat(t);
            if (a < amn[id]) amn[id] = a; if (a > amx[id]) amx[id] = a;
            if (b < bmn[id]) bmn[id] = b; if (b > bmx[id]) bmx[id] = b;
        }
        fprintf(stderr, "reference flag %d done (p1=%d l1=%d)\n", r, p1, l1);
    }
    printf("# class = (d(p1,p2), d(l1,l2), d(p1,l2), d(p2,l1)) over %d reference flags; flags counted per reference\n", nref);
    printf("# %-16s %8s %12s %12s %8s %8s %8s\n", "class", "count", "a range", "b range", "a-b", "compat", "2|a-b|");
    for (int id = 0; id < 144; id++) if (cnt[id]) {
        int d = amx[id] - amn[id];
        printf("  (%d,%d,%d,%d)  %8d  %5d..%-5d  %5d..%-5d  %8d  %7.3f  %6d%s\n", rep[id][0], rep[id][1], rep[id][2], rep[id][3],
               cnt[id] / nref, amn[id], amx[id], bmn[id], bmx[id], amn[id] - bmn[id], (double)nc[id] / cnt[id],
               2 * abs(amn[id] - bmn[id]), (d || bmx[id] != bmn[id]) ? "   <- not constant" : "");
    }
}

static int read_flags(const char *fn, int *P, int *L, int maxk) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int K = 0; while (K < maxk && fscanf(f, "%d %d", &P[K], &L[K]) == 2) K++;
    fclose(f); return K;
}

static void cmd_eval(const char *fn) {
    int P[64], L[64], K = read_flags(fn, P, L, 64);
    for (int j = 0; j < K; j++) if (DP[(size_t)P[j] * W2 + N + L[j]] != 1) { fprintf(stderr, "flag %d not incident\n", j); exit(1); }
    uint64_t *mp = malloc(8 * (size_t)N), *ml = malloc(8 * (size_t)N);
    /* per-vertex masks: bit j set if the vertex is in S'_j (points) or S_j (lines) */
    for (int u = 0; u < N; u++) mp[u] = 0;
    for (int x = 0; x < N; x++) ml[x] = 0;
    int sizeA[64], sizeB[64];
    for (int j = 0; j < K; j++) {
        const uint8_t *dp = DP + (size_t)P[j] * W2, *dl = DL + (size_t)L[j] * W2;
        sizeA[j] = sizeB[j] = 0;
        for (int u = 0; u < N; u++) if (dp[u] == 4 && dl[u] == 5) { mp[u] |= 1ULL << j; sizeA[j]++; }
        for (int x = 0; x < N; x++) if (dl[N + x] == 4 && dp[N + x] == 5) { ml[x] |= 1ULL << j; sizeB[j]++; }
    }
    /* exact K-wise balance: points not freed vs lines not freed, same mask classes */
    int m = 0; uint64_t *sp = malloc(8 * (size_t)N), *sl = malloc(8 * (size_t)N);
    int isFp[N]; memset(isFp, 0, sizeof(isFp)); for (int j = 0; j < K; j++) isFp[P[j]] = 1;
    int isFl[N]; memset(isFl, 0, sizeof(isFl)); for (int j = 0; j < K; j++) isFl[L[j]] = 1;
    int np = 0, nl = 0;
    for (int u = 0; u < N; u++) if (!isFp[u]) sp[np++] = mp[u];
    for (int x = 0; x < N; x++) if (!isFl[x]) sl[nl++] = ml[x];
    (void)m;
    int cmpu(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }
    qsort(sp, np, 8, cmpu); qsort(sl, nl, 8, cmpu);
    long U = 0; int i = 0, j2 = 0;
    while (i < np || j2 < nl) {
        uint64_t v = (i < np && (j2 >= nl || sp[i] <= sl[j2])) ? sp[i] : sl[j2];
        long n = 0, mm = 0;
        while (i < np && sp[i] == v) { n++; i++; }
        while (j2 < nl && sl[j2] == v) { mm++; j2++; }
        if (n > mm) U += n - mm;
    }
    int incompat = 0;
    for (int j = 0; j < K; j++) incompat += __builtin_popcountll(mp[P[j]] ^ ml[L[j]]);
    long pairsum = 0; int npairs_bad = 0, pair_compat_bad = 0;
    for (int j = 0; j < K; j++) for (int k = j + 1; k < K; k++) {
        int a, b, t[4];
        pair_ab(P[j], L[j], P[k], L[k], &a, &b);
        tuple_of(P[j], L[j], P[k], L[k], t);
        pairsum += 2 * abs(a - b); npairs_bad += (a != b); pair_compat_bad += !compat(t);
    }
    int sizes_ok = 1; for (int j = 0; j < K; j++) sizes_ok &= (sizeA[j] == sizeB[j]);
    printf("K=%d |S'|=|S| all equal: %s (|S'|=%d)  pairs with a!=b: %d of %d  pairwise sum 2|a-b|: %ld  compat-bad pairs: %d\n",
           K, sizes_ok ? "yes" : "NO", sizeA[0], npairs_bad, K * (K - 1) / 2, pairsum, pair_compat_bad);
    printf("EXACT K-wise: mass mismatch U = %ld (points that cannot be matched type-by-type), freed-vertex incompat bits = %d\n", U, incompat);
}

static int mind_ok(int p, int *P, int K, int mind) { for (int j = 0; j < K; j++) if (DP[(size_t)p * W2 + P[j]] < mind) return 0; return 1; }

static void cmd_random(int K, uint64_t seed, int mind, const char *out) {
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int P[64], L[64], k = 0, tries = 0;
    while (k < K && tries < 1000000) { tries++; int p = rndi(N); if (!mind_ok(p, P, k, mind)) continue; P[k] = p; L[k] = PL[p * Q1 + rndi(Q1)]; k++; }
    FILE *f = fopen(out, "w"); for (int j = 0; j < k; j++) fprintf(f, "%d %d\n", P[j], L[j]); fclose(f);
    fprintf(stderr, "random: wrote %d flags to %s\n", k, out);
}

/* greedy: candidate pool of random flags, choose the one with least weight to the chosen set */
static void cmd_greedy(int K, uint64_t seed, int mind, const char *out, int pool) {
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int P[64], L[64], k = 0;
    /* first flag random */
    P[0] = rndi(N); L[0] = PL[P[0] * Q1 + rndi(Q1)]; k = 1;
    long total = 0;
    while (k < K) {
        long bestw = 1L << 60; int bp = -1, bl = -1, nok = 0;
        for (int c = 0; c < pool; c++) {
            int p = rndi(N); if (!mind_ok(p, P, k, mind)) continue;
            int l = PL[p * Q1 + rndi(Q1)];
            long w = 0;
            for (int j = 0; j < k; j++) { int t[4]; tuple_of(p, l, P[j], L[j], t); w += 2 * (compat(t) ? 0 : 1); }
            if (w < bestw) { bestw = w; bp = p; bl = l; }
            nok++;
        }
        if (bp < 0) { fprintf(stderr, "greedy: no candidate at step %d\n", k); break; }
        /* exact pairwise weight of the chosen flag */
        long add = 0;
        for (int j = 0; j < k; j++) { int a, b; pair_ab(bp, bl, P[j], L[j], &a, &b); add += 2 * abs(a - b); }
        total += add;
        P[k] = bp; L[k] = bl; k++;
        if (k <= 3 || k == K) fprintf(stderr, "greedy: added flag %d (p=%d l=%d) pairwise 2|a-b| sum +%ld, compat-weight %ld\n", k - 1, bp, bl, add, bestw);
    }
    FILE *f = fopen(out, "w"); for (int j = 0; j < k; j++) fprintf(f, "%d %d\n", P[j], L[j]); fclose(f);
    fprintf(stderr, "greedy: wrote %d flags, pairwise sum %ld\n", k, total);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see header\n"); return 1; }
    load(argv[1]);
    build_dist();
    if (!strcmp(argv[2], "table")) cmd_table(argc > 3 ? atoi(argv[3]) : 3, argc > 4 ? atoll(argv[4]) : 1);
    else if (!strcmp(argv[2], "eval")) cmd_eval(argv[3]);
    else if (!strcmp(argv[2], "random")) cmd_random(atoi(argv[3]), atoll(argv[4]), atoi(argv[5]), argv[6]);
    else if (!strcmp(argv[2], "greedy")) cmd_greedy(atoi(argv[3]), atoll(argv[4]), atoi(argv[5]), argv[6], argc > 7 ? atoi(argv[7]) : 2000);
    else { fprintf(stderr, "unknown mode\n"); return 1; }
    return 0;
}
