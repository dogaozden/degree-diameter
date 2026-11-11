/* wlift: fixed-base voltage lift annealer (card c17).
   Base: incidence graph of GQ(3,3) (gq33.base, points 0..39, lines 40..79, 4-regular bipartite, diameter 4, girth 8).
   Voltage group G from a gtab.py table (one block). Lift vertex (u,g) = u*N+g; base edge (p,l,x) gives (p,g)~(l,g*x).
   Tree edges (BFS tree from base vertex 0) have voltage identity (index 0) and are fixed; the other 81 edges are free.
   Left multiplication by G is an automorphism, so dist((u,g),(v,h)) = dist((u,e),(v,g^-1 h)).
   Cost = number of pairs (base root u, lift vertex x) with dist((u,e),x) > D.  Computed exactly by a bit-parallel
   BFS: bit u of A[x] is set iff dist((u,e),x) <= t after t steps (80 roots fit in __int128).
   Usage: wlift GROUPTAB BASE SEED SECS D T0 T1 OUTPREFIX [START.best]
   Writes OUTPREFIX.best ("N cost" then one voltage per base edge) on each improvement, and OUTPREFIX.edges at cost 0 (then stops). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef unsigned __int128 u128;
static int N, NB, NE, D;
static int *M, *INV;
static int eu[400], ev[400], isfree[400], volt[400];
static int adjn[200], adjv[200][4], adje[200][4], side[200];
static int nfree, freelist[400];
static u128 *A, *Bf;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static int popc128(u128 v) { return __builtin_popcountll((uint64_t)v) + __builtin_popcountll((uint64_t)(v >> 64)); }

static long cost(void) {
    int Y[200][4];
    for (int u = 0; u < NB; u++) for (int j = 0; j < adjn[u]; j++) {
        int e = adje[u][j];
        Y[u][j] = side[u] == 0 ? volt[e] : INV[volt[e]];
    }
    int n = NB * N;
    u128 *a = A, *b = Bf;
    memset(a, 0, sizeof(u128) * n);
    for (int u = 0; u < NB; u++) a[u * N] |= ((u128)1) << u;
    u128 FULL = (((u128)1) << NB) - 1;
    for (int t = 0; t < D; t++) {
        int done = 1;
        for (int u = 0; u < NB; u++) {
            int dg = adjn[u];
            for (int g = 0; g < N; g++) {
                int x = u * N + g;
                u128 val = a[x];
                const int *mrow = M + (size_t)g * N;
                for (int j = 0; j < dg; j++) {
                    int y = Y[u][j];
                    val |= a[adjv[u][j] * N + mrow[y]];
                }
                b[x] = val;
                if ((val & FULL) != FULL) done = 0;
            }
        }
        u128 *tmp = a; a = b; b = tmp;
        if (done) { A = a; Bf = b; return 0; }
    }
    long miss = 0;
    for (int x = 0; x < n; x++) miss += NB - popc128(a[x]);
    A = a; Bf = b;
    return miss;
}

static void write_best(const char *pre, long c) {
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", pre);
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d %ld\n", N, c);
    for (int e = 0; e < NE; e++) fprintf(f, "%d\n", volt[e]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: wlift GROUPTAB BASE SEED SECS D T0 T1 OUTPREFIX [START.best]\n"); return 1; }
    FILE *gf = fopen(argv[1], "r"); if (!gf) return 2;
    char name[256]; int gid; char line[1024];
    if (fscanf(gf, "%255s %d %d", name, &N, &gid) != 3) return 2;
    fgets(line, sizeof line, gf); /* rest of header line */
    M = malloc(sizeof(int) * (size_t)N * N);
    for (long i = 0; i < (long)N * N; i++) if (fscanf(gf, "%d", &M[i]) != 1) return 3;
    fclose(gf);
    INV = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int h = 0; h < N; h++) if (M[(size_t)g * N + h] == 0) INV[g] = h; if (INV[g] < 0) return 4; }
    rng ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
    double secs = atof(argv[4]); D = atoi(argv[5]);
    double T0 = atof(argv[6]), T1 = atof(argv[7]);
    const char *pre = argv[8];
    FILE *bf = fopen(argv[2], "r"); if (!bf) return 5;
    if (fscanf(bf, "%d %d", &NB, &NE) != 2) return 5;
    for (int e = 0; e < NE; e++) if (fscanf(bf, "%d %d", &eu[e], &ev[e]) != 2) return 5;
    fclose(bf);
    /* adjacency with edge indices; side 0 = point (first endpoint) */
    memset(adjn, 0, sizeof adjn);
    for (int e = 0; e < NE; e++) {
        int p = eu[e], l = ev[e];
        side[p] = 0; side[l] = 1;
        adjv[p][adjn[p]] = l; adje[p][adjn[p]] = e; adjn[p]++;
        adjv[l][adjn[l]] = p; adje[l][adjn[l]] = e; adjn[l]++;
    }
    /* BFS spanning tree from 0: tree edges get identity voltage and are fixed */
    int seen[200] = {0}, treeE[400] = {0}, q[200], qh = 0, qt = 0;
    q[qt++] = 0; seen[0] = 1;
    while (qh < qt) { int x = q[qh++]; for (int j = 0; j < adjn[x]; j++) { int y = adjv[x][j]; if (!seen[y]) { seen[y] = 1; treeE[adje[x][j]] = 1; q[qt++] = y; } } }
    nfree = 0;
    for (int e = 0; e < NE; e++) { isfree[e] = !treeE[e]; if (isfree[e]) freelist[nfree++] = e; volt[e] = 0; }
    /* initial state */
    if (argc >= 10) {
        FILE *sf = fopen(argv[9], "r");
        if (!sf) return 6;
        int nn; long cc; if (fscanf(sf, "%d %ld", &nn, &cc) != 2 || nn != N) return 6;
        for (int e = 0; e < NE; e++) if (fscanf(sf, "%d", &volt[e]) != 1) return 6;
        fclose(sf);
        for (int e = 0; e < NE; e++) if (!isfree[e]) volt[e] = 0;
    } else {
        for (int e = 0; e < NE; e++) if (isfree[e]) volt[e] = (int)(xr() % N);
    }
    A = malloc(sizeof(u128) * NB * N); Bf = malloc(sizeof(u128) * NB * N);
    if (!A || !Bf) return 7;
    long cur = cost(), best = cur;
    write_best(pre, best);
    fprintf(stderr, "N=%d n=%d start cost=%ld\n", N, NB * N, cur);
    struct timespec t0s, ts; clock_gettime(CLOCK_MONOTONIC, &t0s);
    long it = 0, acc = 0; int bestvolt[400]; memcpy(bestvolt, volt, sizeof volt);
    while (1) {
        if ((it & 15) == 0) {
            clock_gettime(CLOCK_MONOTONIC, &ts);
            double el = (ts.tv_sec - t0s.tv_sec) + 1e-9 * (ts.tv_nsec - t0s.tv_nsec);
            if (el >= secs) break;
        }
        clock_gettime(CLOCK_MONOTONIC, &ts);
        double el = (ts.tv_sec - t0s.tv_sec) + 1e-9 * (ts.tv_nsec - t0s.tv_nsec);
        double T = T0 * pow(T1 / T0, el / secs);
        int e = freelist[xr() % nfree];
        int old = volt[e];
        int nv = (int)(xr() % N); if (nv == old) { it++; continue; }
        volt[e] = nv;
        long c = cost();
        long dl = c - cur;
        if (dl <= 0 || ur() < exp(-(double)dl / T)) {
            cur = c; acc++;
            if (cur < best) {
                best = cur; memcpy(bestvolt, volt, sizeof volt);
                write_best(pre, best);
                fprintf(stderr, "it %ld t=%.1f T=%.2f best=%ld\n", it, el, T, best);
            }
            if (cur == 0) break;
        } else volt[e] = old;
        it++;
    }
    memcpy(volt, bestvolt, sizeof volt);
    write_best(pre, best);
    printf("N=%d n=%d D=%d iters=%ld acc=%ld best=%ld final_cur=%ld\n", N, NB * N, D, it, acc, best, cur);
    if (best == 0) {
        char fn[512]; snprintf(fn, sizeof fn, "%s.edges", pre);
        FILE *f = fopen(fn, "w");
        int n = NB * N; fprintf(f, "%d\n", n);
        for (int e = 0; e < NE; e++) {
            int p = eu[e], l = ev[e], x = volt[e];
            for (int g = 0; g < N; g++) fprintf(f, "%d %d\n", p * N + g, l * N + M[(size_t)g * N + x]);
        }
        fclose(f);
        printf("wrote %s\n", fn);
    }
    return 0;
}
