/* scan.c (card c4, round d12D7-r2): damage of removing matching edges from the MAIN graph (5 levels of H(9), no
   hubs). Base graph = x5gen2/x5gen3 main graph for the freed points F and the duality M of a d7hex .sol: incidence
   edges (p,i)~(N+l,i) for all i, and matching edges (p,i)~(N+M[p],(i+s)%5), s in {1,2}, for p not in F.
   CANDS: one candidate per line; each candidate is a list of triples "p i s" naming matching edges to REMOVE
   (p must not be in F; i = -1 means all five levels; s in {1,2}). An empty line is the baseline (nothing removed).
   For each candidate: bit-parallel BFS to depth 7 from K sources (mode sym: random level-0 vertices, mode all: random
   main vertices, fixed SEED for all candidates); S = ordered pairs (source, main target) at distance > 7 among the
   sources; est = n * S / K (for sym the level shift is an automorphism only if the removal is level-symmetric, so use
   sym only for i = -1 candidates; then est is the full count over all sources).
   With WRITE_IDX and OUT.edges the candidate with that index is also written (orbcat format) for an exact check.
   Usage: scan HEX SOL CANDS sym|all K SEED [WRITE_IDX OUT.edges]     build: gcc -O2 -o scan scan.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int N, Q1;
static long n;
static long m;
static uint32_t *eu, *ew;
static int32_t *etag;
static char *freed;
static char *removed;
static uint32_t *st, *adj, *deg, *pos;
static uint64_t *vis, *fr, *nx;
static uint64_t rs;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void add(long u, long v, long tag) {
    if (m == 0) {}
    eu[m] = (uint32_t)u; ew[m] = (uint32_t)v; etag[m] = (int32_t)tag; m++;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_csr(void) {
    memset(deg, 0, (n + 1) * sizeof(uint32_t));
    for (long e = 0; e < m; e++) { if (etag[e] >= 0 && removed[etag[e]]) continue; deg[eu[e]]++; deg[ew[e]]++; }
    st[0] = 0; for (long x = 0; x < n; x++) st[x + 1] = st[x] + deg[x];
    for (long x = 0; x < n; x++) pos[x] = st[x];
    for (long e = 0; e < m; e++) { if (etag[e] >= 0 && removed[etag[e]]) continue; adj[pos[eu[e]]++] = ew[e]; adj[pos[ew[e]]++] = eu[e]; }
}

static long long bfs_sum(const long *srcs, long K, int D) {
    long long tot = 0;
    for (long k0 = 0; k0 < K; k0 += 64) {
        int ns = (K - k0 < 64) ? (int)(K - k0) : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int k = 0; k < ns; k++) { long s = srcs[k0 + k]; vis[s] |= 1ULL << k; fr[s] |= 1ULL << k; }
        for (int lev = 1; lev <= D; lev++) {
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (uint32_t i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; nx[x] = acc & ~vis[x]; }
            for (long x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        for (long x = 0; x < n; x++) tot += __builtin_popcountll(~vis[x] & full);
    }
    return tot;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: scan HEX SOL CANDS sym|all K SEED [WRITE_IDX OUT.edges]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3];
    if (!f || fread(hdr, 4, 3, f) != 3) { fprintf(stderr, "no hex\n"); return 1; }
    int q = hdr[0]; N = hdr[1]; Q1 = q + 1; int Lines = hdr[2];
    if (Lines != N) { fprintf(stderr, "expected L == N\n"); return 1; }
    int *LP = malloc(sizeof(int) * (size_t)Lines * Q1);
    if (fread(LP, 4, (size_t)Lines * Q1, f) != (size_t)Lines * Q1) return 1; fclose(f);
    int K, nn, qq, nv; char w[32];
    f = fopen(argv[2], "r");
    if (!f || fscanf(f, "d7hex %d %d %d %d %31s", &qq, &nn, &K, &nv, w) != 5 || qq != q || nn != N) { fprintf(stderr, "bad sol\n"); return 1; }
    freed = calloc(N, 1);
    for (int k = 0; k < K; k++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; freed[x] = 1; }
    char tok[32]; int hm; if (fscanf(f, "%31s %d", tok, &hm) != 2) return 1;
    for (int e = 0; e < 2 * hm; e++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; }
    int *M = malloc(sizeof(int) * N);
    for (int p = 0; p < N; p++) if (fscanf(f, "%d", &M[p]) != 1) return 1;
    fclose(f);
    n = 10L * N;
    long cap = 4000000L + 16L * N;
    eu = malloc(cap * 4); ew = malloc(cap * 4); etag = malloc(cap * 4); m = 0;
#define ID(v, i) ((long)(i) * 2 * N + (v))
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; for (int i = 0; i < 5; i++) add(ID(p, i), ID(N + l, i), -1); }
    for (int p = 0; p < N; p++) { if (freed[p]) continue;
        for (int i = 0; i < 5; i++) for (int s = 1; s <= 2; s++) add(ID(p, i), ID(N + M[p], (i + s) % 5), (long)p * 10 + i * 2 + (s - 1)); }
    fprintf(stderr, "base: N=%d K(freed)=%d edges=%ld (n=%ld)\n", N, K, m, n);
    removed = calloc(10L * N, 1);
    st = malloc((n + 1) * 4); adj = malloc(2 * m * 4); deg = malloc((n + 1) * 4); pos = malloc((n + 1) * 4);
    vis = malloc(n * 8); fr = malloc(n * 8); nx = malloc(n * 8);
    const char *mode = argv[4]; long Ns = atol(argv[5]); rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[6]) * 2654435761ULL; if (!rs) rs = 1;
    long wr = argc > 7 ? atol(argv[7]) : -2; const char *wout = argc > 8 ? argv[8] : NULL;
    long *srcs = malloc(Ns * sizeof(long));
    for (long k = 0; k < Ns; k++) srcs[k] = (strcmp(mode, "sym") == 0) ? (long)(rnd() % (2L * N)) : (long)(rnd() % n);
    FILE *cf = fopen(argv[3], "r"); if (!cf) { fprintf(stderr, "no cands\n"); return 1; }
    static char line[1 << 16];
    long *marked = malloc(sizeof(long) * 1000000); int idx = 0;
    while (fgets(line, sizeof line, cf)) {
        long nm = 0; int bad = 0;
        int tc = 0, tv[3];
        char *t = strtok(line, " \t\r\n");
        while (t) {
            tv[tc++] = atoi(t);
            if (tc == 3) {
                int p = tv[0], i = tv[1], s = tv[2];
                if (p < 0 || p >= N || freed[p] || (s != 1 && s != 2) || i < -1 || i > 4) { bad = 1; }
                else if (strcmp(mode, "sym") == 0 && i != -1) { bad = 2; }
                else for (int ii = (i < 0 ? 0 : i); ii <= (i < 0 ? 4 : i); ii++) {
                    long tag = (long)p * 10 + ii * 2 + (s - 1);
                    if (!removed[tag]) { removed[tag] = 1; marked[nm++] = tag; }
                }
                tc = 0;
            }
            t = strtok(NULL, " \t\r\n");
        }
        if (bad) { fprintf(stderr, "candidate %d: bad triple (%d)\n", idx, bad); return 1; }
        double t0 = now();
        build_csr();
        long long S = bfs_sum(srcs, Ns, 7);
        double est = (double)n * (double)S / (double)Ns;
        printf("cand %d removed %ld sampled %ld sum %lld est %.1f time %.1fs\n", idx, nm, Ns, S, est, now() - t0);
        fflush(stdout);
        if (idx == wr && wout) {
            FILE *o = fopen(wout, "w"); fprintf(o, "%ld\n", n);
            for (long e = 0; e < m; e++) { if (etag[e] >= 0 && removed[etag[e]]) continue; fprintf(o, "%u %u\n", eu[e], ew[e]); }
            fclose(o); fprintf(stderr, "wrote %s\n", wout);
        }
        for (long k = 0; k < nm; k++) removed[marked[k]] = 0;
        idx++;
    }
    return 0;
}
