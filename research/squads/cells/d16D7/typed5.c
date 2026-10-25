/* typed5.c: bipartite (q+1+r, 7) graphs on L = 2r+1 levels of the generalized hexagon H(q) where some levels carry the
   DUAL hexagon. cell-16-7 session (resume), 2026-10-25.

   Levels j in Z_L, each a copy of the incidence graph I of H(q), with a type t_j in {H, D}. In a level of type H the
   "points" (class A) are the points of H and the "lines" (class B) the lines of H; in a level of type D (the dual
   hexagon H^D, same incidence graph) the roles are swapped. Matchings, k = 1..r:
       M_k^(j): A_j -> B_{j+k}, a bijection; edge (a, j) ~ (M_k^(j)(a), j+k).
   Base graph: diameter <= 7 for ANY bijections (each pair of levels j, j+k is the three-copy situation of
   research/d13D7/REPORT.md section 2 with its own matching; the proof there never uses the type).
   A transition (j,k) is FRIENDLY when t_j != t_{j+k}: then A_j and B_{j+k} are the same kind of element of H (both points
   or both lines) and M_k^(j) = identity. The identity maps the q(q+1) elements at distance 2 from x onto the elements at
   distance 2 from x, so the local-duality condition (H3) of the surgery theorem holds at EVERY element and a freed set
   only has to be non-collinear (points) / non-concurrent (lines). Unfriendly transitions (t_j = t_{j+k}) use any
   bijection (here a random one, or none freed).
   Surgery: for a friendly transition and x in the freed set F (R_H for points, R_L for lines) the edge (x,j)-(x,j+k)
   is deleted; this frees one A-slot at (x, j) and one B-slot at (x, j+k).
   Hubs: a line-side hub (class B) is joined to ONE free A-slot in EVERY level, a point-side hub (class A) to one free
   B-slot in every level; then a hub reaches all of level j within 1 + 6 (through its level-j neighbour), hubs of
   opposite sides are within 1 + 5 + 1 = 7, and same-side hubs are joined through the hub graph (bipartite, line-side
   hub ~ point-side hub, degree <= q+1+r - L) so that they are within 6.
   Number of hubs per side = min over levels of the free slots of that class. With L = 5 and types HDHDH every level
   has one friendly outgoing and one friendly incoming transition, so both minima are min(|R_H|, |R_L|) (if the
   unfriendly transitions free nothing).

   Usage: typed5 HEXBIN TYPES SEED HUBDEG OUT.edges [RHFILE|-] [RLFILE|-] [KMAX]
     TYPES e.g. HDHDH (length L, odd); RHFILE/RLFILE: one index per line (hexgen point / line ids); '-' = greedy
     random maximal set (seeded). KMAX caps the number of hubs per side (0 = no cap).
   Output: apsp.c edge list ("n" then "u v"). Vertex ids: (point p, level j) = 2Nj + p, (line l, level j) = 2Nj + N + l,
   line-side hub h = 2NL + h, point-side hub h = 2NL + KB + h. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q, N, Q1, L, R;
static int32_t *LP, *PL;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void shuffle(int *a, int n) { for (int i = n - 1; i > 0; i--) { int j = (int)(rnd() % (uint64_t)(i + 1)); int t = a[i]; a[i] = a[j]; a[j] = t; } }

static void load_hex(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    int32_t h[3]; if (fread(h, 4, 3, f) != 3) exit(1);
    q = h[0]; N = h[1]; Q1 = q + 1; if (h[2] != N) { fprintf(stderr, "points != lines\n"); exit(1); }
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1);
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[(size_t)l * Q1 + k]; PL[(size_t)p * Q1 + c[p]++] = l; }
    for (int p = 0; p < N; p++) if (c[p] != Q1) { fprintf(stderr, "bad hexagon\n"); exit(1); }
    free(c);
}

/* greedy random maximal non-collinear point set (kind 0) or non-concurrent line set (kind 1) */
static int greedy(int kind, int *out) {
    int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i; shuffle(ord, N);
    char *blk = calloc(N, 1); int n = 0;
    const int32_t *A = kind == 0 ? PL : LP, *B = kind == 0 ? LP : PL;   /* x -> its Q1 neighbours -> their Q1 neighbours */
    for (int t = 0; t < N; t++) {
        int x = ord[t]; if (blk[x]) continue;
        out[n++] = x; blk[x] = 1;
        for (int a = 0; a < Q1; a++) { int y = A[(size_t)x * Q1 + a]; for (int b = 0; b < Q1; b++) blk[B[(size_t)y * Q1 + b]] = 1; }
    }
    free(ord); free(blk); return n;
}
static int read_set(const char *fn, int *out) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int n = 0, x; char buf[256];
    while (fgets(buf, sizeof buf, f)) { if (buf[0] == '#') continue; if (sscanf(buf, "%d", &x) == 1) { if (x < 0 || x >= N) { fprintf(stderr, "bad id\n"); exit(1); } out[n++] = x; } }
    fclose(f); return n;
}
/* independent check of the set condition */
static void check_set(int kind, const int *s, int n) {
    char *in = calloc(N, 1); for (int i = 0; i < n; i++) { if (in[s[i]]) { fprintf(stderr, "duplicate in set\n"); exit(1); } in[s[i]] = 1; }
    const int32_t *A = kind == 0 ? PL : LP, *B = kind == 0 ? LP : PL;
    for (int i = 0; i < n; i++) { int x = s[i];
        for (int a = 0; a < Q1; a++) { int y = A[(size_t)x * Q1 + a]; for (int b = 0; b < Q1; b++) { int z = B[(size_t)y * Q1 + b]; if (z != x && in[z]) { fprintf(stderr, "set %d not independent (%d %d)\n", kind, x, z); exit(1); } } } }
    free(in);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: typed5 HEXBIN TYPES SEED HUBDEG OUT.edges [RHFILE|-] [RLFILE|-] [KMAX]\n"); return 2; }
    load_hex(argv[1]);
    const char *T = argv[2]; L = (int)strlen(T); R = (L - 1) / 2;
    if (L < 3 || L % 2 == 0) { fprintf(stderr, "L must be odd >= 3\n"); return 2; }
    int ty[64]; for (int j = 0; j < L; j++) ty[j] = T[j] == 'D';
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int hubdeg = atoi(argv[4]); const char *out = argv[5];
    int *RH = malloc(sizeof(int) * N), *RL = malloc(sizeof(int) * N), nH, nL;
    nH = (argc > 6 && strcmp(argv[6], "-")) ? read_set(argv[6], RH) : greedy(0, RH);
    nL = (argc > 7 && strcmp(argv[7], "-")) ? read_set(argv[7], RL) : greedy(1, RL);
    int kmax = argc > 8 ? atoi(argv[8]) : 0;
    check_set(0, RH, nH); check_set(1, RL, nL);
    char *inH = calloc(N, 1), *inL = calloc(N, 1);
    for (int i = 0; i < nH; i++) inH[RH[i]] = 1;
    for (int i = 0; i < nL; i++) inL[RL[i]] = 1;
    fprintf(stderr, "q=%d N=%d L=%d r=%d types=%s |R_H|=%d |R_L|=%d (Hoffman bound %d)\n", q, N, L, R, T, nH, nL, N / Q1);

    long NV0 = 2L * N * L;
    /* kinds: 0 point, 1 line. A-kind of level j = ty[j] (H: points), B-kind = 1 - ty[j] */
    #define VID(j, kind, x) ((long)(j) * 2 * N + (long)(kind) * N + (x))
    /* unfriendly bijections, random */
    int **perm = malloc(sizeof(int *) * L * (R + 1));
    long *slA[64], *slB[64]; int nA[64] = {0}, nB[64] = {0};
    for (int j = 0; j < L; j++) { slA[j] = malloc(sizeof(long) * 2 * R * (size_t)N); slB[j] = malloc(sizeof(long) * 2 * R * (size_t)N); }
    for (int j = 0; j < L; j++) for (int k = 1; k <= R; k++) {
        int j2 = (j + k) % L, a = ty[j], b = 1 - ty[j2];
        int *pm = NULL;
        if (a != b) { pm = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) pm[i] = i; shuffle(pm, N); }
        perm[j * (R + 1) + k] = pm;
        if (a == b) { /* friendly: freed set */
            const char *in = a == 0 ? inH : inL;
            for (int x = 0; x < N; x++) if (in[x]) { slA[j][nA[j]++] = VID(j, a, x); slB[j2][nB[j2]++] = VID(j2, b, x); }
        }
    }
    int KB = 1 << 30, KA = 1 << 30;
    for (int j = 0; j < L; j++) { if (nA[j] < KB) KB = nA[j]; if (nB[j] < KA) KA = nB[j]; }
    if (kmax > 0) { if (KB > kmax) KB = kmax; if (KA > kmax) KA = kmax; }
    for (int j = 0; j < L; j++) { fprintf(stderr, "level %d (%c): free A-slots %d, free B-slots %d\n", j, T[j], nA[j], nB[j]); }
    long n = NV0 + KB + KA;
    fprintf(stderr, "hubs: %d line-side, %d point-side; n = %ld (base %ld, +%d)\n", KB, KA, n, NV0, KB + KA);
    for (int j = 0; j < L; j++) {   /* shuffle slot lists so that hubs get random slots */
        for (int i = nA[j] - 1; i > 0; i--) { int t = (int)(rnd() % (uint64_t)(i + 1)); long s = slA[j][i]; slA[j][i] = slA[j][t]; slA[j][t] = s; }
        for (int i = nB[j] - 1; i > 0; i--) { int t = (int)(rnd() % (uint64_t)(i + 1)); long s = slB[j][i]; slB[j][i] = slB[j][t]; slB[j][t] = s; }
    }
    FILE *f = fopen(out, "w"); if (!f) { perror(out); return 1; }
    fprintf(f, "%ld\n", n);
    long m = 0;
    for (int j = 0; j < L; j++) for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { fprintf(f, "%ld %ld\n", VID(j, 0, LP[(size_t)l * Q1 + k]), VID(j, 1, l)); m++; }
    for (int j = 0; j < L; j++) for (int k = 1; k <= R; k++) {
        int j2 = (j + k) % L, a = ty[j], b = 1 - ty[j2]; int *pm = perm[j * (R + 1) + k];
        const char *in = a == 0 ? inH : inL;
        for (int x = 0; x < N; x++) {
            if (!pm && in[x]) continue;
            fprintf(f, "%ld %ld\n", VID(j, a, x), VID(j2, b, pm ? pm[x] : x)); m++;
        }
    }
    for (int h = 0; h < KB; h++) for (int j = 0; j < L; j++) { fprintf(f, "%ld %ld\n", NV0 + h, slA[j][h]); m++; }
    for (int h = 0; h < KA; h++) for (int j = 0; j < L; j++) { fprintf(f, "%ld %ld\n", NV0 + KB + h, slB[j][h]); m++; }
    /* hub graph: union of hubdeg random injections line-side -> point-side (no repeated edge) */
    int K = KB < KA ? KB : KA, KX = KB > KA ? KB : KA;
    int *deg = calloc(KB + KA, sizeof(int));
    char *used = NULL; long usedn = (long)KB * KA; if (usedn < 400000000L) used = calloc(usedn, 1);
    for (int r2 = 0; r2 < hubdeg; r2++) {
        int *pa = malloc(sizeof(int) * KX), *pb = malloc(sizeof(int) * KX);
        for (int i = 0; i < KX; i++) { pa[i] = i % KB; pb[i] = i % KA; }
        shuffle(pa, KX); shuffle(pb, KX);
        for (int i = 0; i < KX; i++) {
            int u = pa[i], v = pb[i];
            if (used && used[(long)u * KA + v]) continue;
            if (deg[u] >= hubdeg || deg[KB + v] >= hubdeg) continue;
            if (used) used[(long)u * KA + v] = 1;
            deg[u]++; deg[KB + v]++;
            fprintf(f, "%ld %ld\n", NV0 + u, NV0 + KB + v); m++;
        }
        free(pa); free(pb);
    }
    (void)K;
    fclose(f);
    int mx = 0; for (int i = 0; i < KB + KA; i++) if (deg[i] > mx) mx = deg[i];
    fprintf(stderr, "edges %ld, hub-graph max degree %d (hub degree <= %d), Delta should be %d\n", m, mx, mx + L, q + 1 + R);
    return 0;
}
