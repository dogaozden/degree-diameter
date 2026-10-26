/* c41 parity lift annealer: lift of a NON-bipartite base b (4-regular) by a group G with an index-2 hom phi.
   Tree edges fixed to e after the BFS 2-colouring c of the spanning tree; each non-tree edge (u,v) gets a voltage g
   with phi(g) = 1 if c(u)==c(v) else 0. Then (u,x) gets colour c(u)+phi(x), a proper 2-colouring: lift is bipartite.
   Cost and moves are as in lift.c (sum over roots of lift vertices farther than D). Usage:
   parlift BASE GROUP.bin PHI.txt D seconds seed [K] [OUT] ; env T0 T1 EPOCH QUIET */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXB 4096
#define MAXE 16384
static int b, m, N, D, K = 8;
static uint16_t *MT; static int *INV;
static int eu[MAXE], ev[MAXE], isfree[MAXE], volt[MAXE], bestv[MAXE], qpar[MAXE];
static int nfree, freeidx[MAXE];
static int ndart[MAXB], dto[MAXB][64], dedge[MAXB][64], dinv[MAXB][64];
static int *dist, *queue; static int stampv = 0;
static int *cls[2]; static int ncls[2];
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int dvolt(int u, int j) { int g = volt[dedge[u][j]]; return dinv[u][j] ? INV[g] : g; }

static void load_group(const char *p, const char *pp) {
    FILE *f = fopen(p, "rb"); if (!f) { fprintf(stderr, "no group\n"); exit(2); }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) exit(2); N = n32; MT = malloc((size_t)N * N * 2);
    if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) exit(2); fclose(f);
    INV = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int h = 0; h < N; h++) if (MT[(size_t)g * N + h] == 0) { INV[g] = h; break; } }
    FILE *g = fopen(pp, "r"); if (!g) exit(2);
    int ph[MAXB * 0 + 1]; (void)ph;
    int *phi = malloc(N * sizeof(int)); for (int i = 0; i < N; i++) if (fscanf(g, "%d", &phi[i]) != 1) exit(2); fclose(g);
    for (int c = 0; c < 2; c++) { cls[c] = malloc(N * sizeof(int)); ncls[c] = 0; }
    for (int x = 0; x < N; x++) cls[phi[x]][ncls[phi[x]]++] = x;
    if (!ncls[0] || !ncls[1]) { fprintf(stderr, "phi trivial\n"); exit(2); }
    /* sanity: phi is a homomorphism */
    for (int x = 0; x < N; x += 1) for (int y = 0; y < N; y += 7) if (phi[MT[(size_t)x * N + y]] != (phi[x] ^ phi[y])) { fprintf(stderr, "phi not a hom\n"); exit(2); }
    /* keep phi in the global via qpar trick: store as static */
    static int *PHI; PHI = phi; (void)PHI;
    free(INV); INV = malloc(N * sizeof(int));
    for (int x = 0; x < N; x++) { INV[x] = -1; for (int h = 0; h < N; h++) if (MT[(size_t)x * N + h] == 0) { INV[x] = h; break; } }
    extern int *gPHI; gPHI = phi;
}
int *gPHI;

static void load_base(const char *p) {
    FILE *f = fopen(p, "r"); if (!f) { fprintf(stderr, "cannot open base\n"); exit(2); }
    if (fscanf(f, "%d %d", &b, &m) != 2) exit(2);
    for (int i = 0; i < m; i++) { if (fscanf(f, "%d %d", &eu[i], &ev[i]) != 2) exit(2); }
    fclose(f);
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        dto[u][ndart[u]] = v; dedge[u][ndart[u]] = i; dinv[u][ndart[u]] = 0; ndart[u]++;
        dto[v][ndart[v]] = u; dedge[v][ndart[v]] = i; dinv[v][ndart[v]] = 1; ndart[v]++;
    }
    static int col[MAXB], seen[MAXB], qq[MAXB], intree[MAXE]; for (int u = 0; u < b; u++) { col[u] = -1; seen[u] = 0; }
    col[0] = 0; seen[0] = 1; int h = 0, t = 0; qq[t++] = 0;
    while (h < t) { int u = qq[h++]; for (int j = 0; j < ndart[u]; j++) { int v = dto[u][j], e = dedge[u][j];
        if (!seen[v]) { seen[v] = 1; col[v] = 1 - col[u]; intree[e] = 1; qq[t++] = v; } } }
    if (t != b) { fprintf(stderr, "base not connected\n"); exit(2); }
    nfree = 0;
    for (int i = 0; i < m; i++) {
        if (intree[i]) { isfree[i] = 0; qpar[i] = 0; }
        else { isfree[i] = 1; qpar[i] = (col[eu[i]] == col[ev[i]]) ? 1 : 0; freeidx[nfree++] = i; }
    }
    /* base must be non-bipartite somewhere, otherwise the parity pattern is still valid (fine) */
    for (int i = 0; i < m; i++) if (!isfree[i]) { /* tree edge: c(u)!=c(v) so qpar 0 */ }
}

static int ok_at(int u) {
    for (int j = 0; j < ndart[u]; j++) {
        int g = dvolt(u, j);
        for (int i = 0; i < j; i++) if (dto[u][i] == dto[u][j] && dvolt(u, i) == g) return 0;
        if (dto[u][j] == u && g == 0) return 0;
    }
    return 1;
}
static int ok_edge(int e) { return ok_at(eu[e]) && ok_at(ev[e]); }
static int randg(int e) { int c = qpar[e]; return cls[c][rnd() % ncls[c]]; }

static long cost(long lim) {
    long c = 0; int n = b * N;
    for (int r = 0; r < b; r++) {
        stampv++;
        if (stampv == 0x7fffffff) { memset(dist, 0, n * sizeof(int)); stampv = 1; }
        int h = 0, t = 0, s0 = r * N; dist[s0] = stampv; queue[t++] = s0; int lev_end = t, lev = 0;
        while (h < t && lev < D) {
            int s = queue[h++], u = s / N, x = s % N;
            for (int j = 0; j < ndart[u]; j++) { int y = dto[u][j] * N + MT[(size_t)x * N + dvolt(u, j)];
                if (dist[y] != stampv) { dist[y] = stampv; queue[t++] = y; } }
            if (h == lev_end) { lev++; lev_end = t; }
        }
        c += n - t;
        if (c > lim) return c;
    }
    return c;
}

static void write_sol(const char *out, long c) {
    FILE *f = fopen(out, "w");
    fprintf(f, "# parlift D=%d n=%d cost=%ld\nbase %d %d\nN %d\n", D, b * N, c, b, m, N);
    for (int i = 0; i < m; i++) fprintf(f, "e %d %d %d\n", eu[i], ev[i], volt[i]);
    fclose(f);
    char p[1024]; snprintf(p, sizeof p, "%s.edges", out);
    f = fopen(p, "w"); fprintf(f, "%d\n", b * N);
    for (int i = 0; i < m; i++) for (int x = 0; x < N; x++) {
        int y = MT[(size_t)x * N + volt[i]];
        fprintf(f, "%d %d\n", eu[i] * N + x, ev[i] * N + y);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: parlift BASE GROUP.bin PHI.txt D seconds seed [K] [OUT]\n"); return 2; }
    load_group(argv[2], argv[3]); load_base(argv[1]);
    D = atoi(argv[4]);
    double secs = atof(argv[5]); rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();
    if (argc > 7) K = atoi(argv[7]);
    const char *out = argc > 8 ? argv[8] : NULL;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 3.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    long EPOCH = getenv("EPOCH") ? atol(getenv("EPOCH")) : 20000;
    int quiet = getenv("QUIET") ? atoi(getenv("QUIET")) : 0;
    int n = b * N; dist = calloc(n, sizeof(int)); queue = malloc(n * sizeof(int));
    for (int i = 0; i < m; i++) volt[i] = 0;
    for (int f = 0; f < nfree; f++) { int e = freeidx[f], tries = 0;
        do { volt[e] = randg(e); } while (!ok_edge(e) && ++tries < 100000); }
    long cur = cost(1L << 60), best = cur; memcpy(bestv, volt, sizeof volt);
    if (!quiet) printf("N=%d b=%d m=%d free=%d n=%d start cost=%ld\n", N, b, m, nfree, n, cur);
    double t0 = now(), tl = t0; long step = 0, evals = 0;
    while (best > 0 && nfree > 0) {
        if ((step & 255) == 0) { double tn = now(); if (tn - t0 > secs) break;
            if (!quiet && tn - tl > 10) { printf("t=%.0f cur=%ld best=%ld\n", tn - t0, cur, best); fflush(stdout); tl = tn; } }
        long ph = step % EPOCH;
        if (ph == 0 && step > 0) { memcpy(volt, bestv, sizeof volt); cur = best; }
        double T = T0 * pow(T1 / T0, (double)ph / EPOCH);
        int e = freeidx[rnd() % nfree], old = volt[e], bg = -1; long bc = 1L << 60;
        long lim = cur + (long)(T * 10) + 2;
        for (int k = 0; k < K; k++) {
            int g = randg(e);
            if (g == old) continue;
            volt[e] = g; if (!ok_edge(e)) continue;
            long c = cost(bc < lim ? bc : lim); evals++;
            if (c < bc) { bc = c; bg = g; }
        }
        volt[e] = old;
        if (bg >= 0 && (bc <= cur || rnd01() < exp(-(bc - cur) / T))) { volt[e] = bg; cur = bc;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof volt); } }
        step++;
    }
    memcpy(volt, bestv, sizeof volt);
    printf("RESULT D=%d N=%d b=%d n=%d best=%ld miss=%.4f evals=%ld time=%.1f\n", D, N, b, n, best,
           (double)best / b, evals, now() - t0);
    if (out) { write_sol(out, best); printf("wrote %s (cost %ld)\n", out, best); }
    return best == 0 ? 0 : 1;
}
