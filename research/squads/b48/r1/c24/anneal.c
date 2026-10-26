/* c24: bit-parallel voltage-lift annealer for a 4-regular base (degree 4, simple) and a group of order N <= 64.
   Each lift vertex y carries a bitset over the base roots u (roots (u,e)): bit u set iff dist((u,e), y) <= t.
   After D steps, cost = sum_y (b - popcount(R_D(y))) = sum over roots of the number of lift vertices farther than D.
   usage: anneal BASE GROUP.bin SECONDS SEED OUT_PREFIX [T0 T1 EPOCH]   (tree edges get voltage e) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXB 128
#define MAXM 512
#define MAXN 64
#define DEG 4
static int b, m, N, n, D = 8;
static int eu[MAXM], ev[MAXM], volt[MAXM], bestv[MAXM], intree[MAXM], freeidx[MAXM], nfree;
static int dto[MAXB][DEG], dedge[MAXB][DEG], dinv[MAXB][DEG], ndart[MAXB];
static uint16_t MT[MAXN * MAXN]; static int INV[MAXN];
static uint32_t *nb; static uint64_t *S1, *S2;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int dvolt(int w, int j) { int g = volt[dedge[w][j]]; return dinv[w][j] ? INV[g] : g; }

static void load_base(const char *p) {
    FILE *f = fopen(p, "r"); if (!f) exit(2);
    if (fscanf(f, "%d %d", &b, &m) != 2) exit(2);
    for (int i = 0; i < m; i++) { if (fscanf(f, "%d %d", &eu[i], &ev[i]) != 2) exit(2); }
    fclose(f); n = 0;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        dto[u][ndart[u]] = v; dedge[u][ndart[u]] = i; dinv[u][ndart[u]] = 0; ndart[u]++;
        dto[v][ndart[v]] = u; dedge[v][ndart[v]] = i; dinv[v][ndart[v]] = 1; ndart[v]++;
    }
    for (int u = 0; u < b; u++) if (ndart[u] != DEG) { fprintf(stderr, "base not %d-regular\n", DEG); exit(2); }
    static int seen[MAXB], qq[MAXB]; int h = 0, t = 0; seen[0] = 1; qq[t++] = 0;
    while (h < t) { int u = qq[h++]; for (int j = 0; j < DEG; j++) { int v = dto[u][j];
        if (!seen[v]) { seen[v] = 1; intree[dedge[u][j]] = 1; qq[t++] = v; } } }
    if (t != b) { fprintf(stderr, "base disconnected\n"); exit(2); }
}
static void load_group(const char *p) {
    FILE *f = fopen(p, "rb"); if (!f) exit(2);
    int32_t NN; if (fread(&NN, 4, 1, f) != 1) exit(2); N = NN;
    if (N > MAXN) exit(2);
    for (int i = 0; i < N * N; i++) { uint16_t x; if (fread(&x, 2, 1, f) != 1) exit(2); MT[i] = x; }
    fclose(f);
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (MT[g * N + h] == 0) INV[g] = h;
}
static void build_nb(void) {
    for (int w = 0; w < b; w++) for (int x = 0; x < N; x++) {
        int y = w * N + x;
        for (int j = 0; j < DEG; j++) nb[y * DEG + j] = dto[w][j] * N + MT[x * N + dvolt(w, j)];
    }
}
static long evalcost(void) {
    build_nb();
    memset(S1, 0, sizeof(uint64_t) * 2 * n);
    for (int u = 0; u < b; u++) S1[2 * (u * N) + (u >> 6)] |= 1ULL << (u & 63);
    uint64_t *cur = S1, *nxt = S2;
    for (int t = 0; t < D; t++) {
        for (int y = 0; y < n; y++) {
            uint64_t a0 = cur[2 * y], a1 = cur[2 * y + 1];
            const uint32_t *p = nb + y * DEG;
            for (int j = 0; j < DEG; j++) { uint32_t z = p[j]; a0 |= cur[2 * z]; a1 |= cur[2 * z + 1]; }
            nxt[2 * y] = a0; nxt[2 * y + 1] = a1;
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long tot = 0;
    for (int y = 0; y < n; y++) tot += __builtin_popcountll(cur[2 * y]) + __builtin_popcountll(cur[2 * y + 1]);
    return (long)n * b - tot;
}
static void write_out(const char *prefix, long cost) {
    char fn[512]; snprintf(fn, sizeof fn, "%s.volt", prefix);
    FILE *f = fopen(fn, "w"); fprintf(f, "%d %d %d\n", b, m, N);
    for (int e = 0; e < m; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], volt[e]);
    fclose(f);
    snprintf(fn, sizeof fn, "%s.edges", prefix);
    f = fopen(fn, "w"); fprintf(f, "%d\n", n);
    for (int e = 0; e < m; e++) for (int x = 0; x < N; x++)
        fprintf(f, "%d %d\n", eu[e] * N + x, ev[e] * N + MT[x * N + volt[e]]);
    fclose(f);
    printf("wrote %s (cost %ld)\n", prefix, cost);
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: anneal BASE GROUP.bin SECONDS SEED OUT [T0 T1 EPOCH]\n"); return 2; }
    load_base(argv[1]); load_group(argv[2]);
    double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double T0 = argc > 6 ? atof(argv[6]) : 6.0, T1 = argc > 7 ? atof(argv[7]) : 0.3;
    long EPOCH = argc > 8 ? atol(argv[8]) : 200000;
    n = b * N;
    nb = malloc(sizeof(uint32_t) * n * DEG); S1 = malloc(sizeof(uint64_t) * 2 * n); S2 = malloc(sizeof(uint64_t) * 2 * n);
    nfree = 0; for (int e = 0; e < m; e++) { if (intree[e]) volt[e] = 0; else { volt[e] = rnd() % N; freeidx[nfree++] = e; } }
    long cur = evalcost(), best = cur; memcpy(bestv, volt, sizeof volt);
    double t0 = now(); long evals = 1; long start_cost = cur;
    int done = 0;
    while (best > 0 && !done) {
        memcpy(volt, bestv, sizeof volt); cur = best;
        for (long k = 0; k < EPOCH; k++) {
            if ((k & 1023) == 0 && now() - t0 > secs) { done = 1; break; }
            double T = T0 * pow(T1 / T0, (double)k / EPOCH);
            int e = freeidx[rnd() % nfree]; int old = volt[e];
            int g = rnd() % N; if (g == old) continue;
            volt[e] = g;
            long c = evalcost(); evals++;
            long d = c - cur;
            if (d <= 0 || rnd01() < exp(-(double)d / T)) {
                cur = c;
                if (cur < best) { best = cur; memcpy(bestv, volt, sizeof volt); if (best == 0) break; }
            } else volt[e] = old;
        }
    }
    memcpy(volt, bestv, sizeof volt);
    long fin = evalcost();
    printf("RESULT group=%s base=%s n=%d start=%ld best=%ld evals=%ld time=%.1f miss=%.3f\n", argv[2], argv[1], n, start_cost, fin, evals, now() - t0, (double)fin / b);
    write_out(argv[5], fin);
    return fin == 0 ? 0 : 1;
}
