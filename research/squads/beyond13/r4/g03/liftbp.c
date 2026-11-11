/* liftbp: bit-parallel version of liftd (squad r4 g03). Same model: bipartite DEG-regular base (A=[0,h), B=[h,2h)),
   Z_n voltages, tree voltages fixed 0, cost = sum over base sources (u,0) of #vertices at distance > D.
   Reachability for all sources at once: 2 x 64-bit words per lifted vertex (b <= 128 sources).
   Usage: liftbp BASE n D seconds seed OUTPREFIX [T0 T1 L]   env: DEG (default 4), START=file ("e x" lines), EVAL=1 (cost only)
   Writes OUTPREFIX.best ("e x" lines for free edges) and OUTPREFIX.edges (N then "u v" lines) when cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXE 1024
#define MAXV 256
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
int b, h, E, n, D, DEG = 4; long N;
int eu[MAXE], ev[MAXE], volt[MAXE], isfree[MAXE];
int inc[MAXV][8], sgn[MAXV][8];
int nbw[MAXV][8], nbs[MAXV][8];
uint64_t *A, *Bf;
int nfree, freeidx[MAXE];

static void prep(void) {
    for (int w = 0; w < b; w++) for (int k = 0; k < DEG; k++) {
        int e = inc[w][k], s = sgn[w][k];
        nbw[w][k] = s > 0 ? ev[e] : eu[e];
        nbs[w][k] = s > 0 ? volt[e] : (n - volt[e]) % n;
    }
}

long cost(void) {
    prep();
    memset(A, 0, 16 * (size_t)N);
    for (int u = 0; u < b; u++) { long v = (long)u * n; A[2 * v + (u >> 6)] |= 1ULL << (u & 63); }
    for (int lev = 0; lev < D; lev++) {
        for (int w = 0; w < b; w++) for (int g = 0; g < n; g++) {
            long v = (long)w * n + g;
            uint64_t a0 = A[2 * v], a1 = A[2 * v + 1];
            for (int k = 0; k < DEG; k++) {
                int gg = g + nbs[w][k]; if (gg >= n) gg -= n;
                long y = 2 * ((long)nbw[w][k] * n + gg);
                a0 |= A[y]; a1 |= A[y + 1];
            }
            Bf[2 * v] = a0; Bf[2 * v + 1] = a1;
        }
        uint64_t *t = A; A = Bf; Bf = t;
    }
    long pop = 0;
    for (long v = 0; v < N; v++) pop += __builtin_popcountll(A[2 * v]) + __builtin_popcountll(A[2 * v + 1]);
    return (long)b * N - pop;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: liftbp BASE n D seconds seed OUTPREFIX [T0 T1 L]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int nb; if (!f || fscanf(f, "%d", &nb) != 1) return 2; b = nb; h = b / 2;
    if (getenv("DEG")) DEG = atoi(getenv("DEG"));
    E = 0;
    for (int i = 0; i < DEG * h; i++) { if (fscanf(f, "%d %d", &eu[E], &ev[E]) != 2) return 2; E++; }
    fclose(f);
    n = atoi(argv[2]); D = atoi(argv[3]); double secs = atof(argv[4]);
    rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 2.0, T1 = argc > 8 ? atof(argv[8]) : 0.05; long L = argc > 9 ? atol(argv[9]) : 20000;
    N = (long)b * n;
    A = calloc(2 * N, sizeof(uint64_t)); Bf = calloc(2 * N, sizeof(uint64_t));
    int dg[MAXV] = {0};
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e];
        inc[u][dg[u]] = e; sgn[u][dg[u]++] = 1;
        inc[v][dg[v]] = e; sgn[v][dg[v]++] = -1;
    }
    for (int u = 0; u < b; u++) if (dg[u] != DEG) { fprintf(stderr, "degree %d at %d\n", dg[u], u); return 3; }
    int seen[MAXV] = {0}, bq[MAXV], bh = 0, bt = 0; int treeE[MAXE] = {0};
    seen[0] = 1; bq[bt++] = 0;
    while (bh < bt) { int x = bq[bh++]; for (int k = 0; k < DEG; k++) { int e = inc[x][k]; int y = sgn[x][k] > 0 ? ev[e] : eu[e];
        if (!seen[y]) { seen[y] = 1; treeE[e] = 1; bq[bt++] = y; } } }
    if (bt != b) { fprintf(stderr, "base disconnected\n"); return 4; }
    nfree = 0; for (int e = 0; e < E; e++) { isfree[e] = !treeE[e]; volt[e] = 0; if (isfree[e]) freeidx[nfree++] = e; }
    if (getenv("START")) { FILE *s = fopen(getenv("START"), "r"); int e, x; while (s && fscanf(s, "%d %d", &e, &x) == 2) volt[e] = ((x % n) + n) % n; if (s) fclose(s); }
    else for (int i = 0; i < nfree; i++) volt[freeidx[i]] = rnd() % n;
    long cur = cost(), best = cur; int bestv[MAXE]; memcpy(bestv, volt, sizeof(volt));
    if (getenv("EVAL")) { printf("EVALCOST b=%d n=%d N=%ld D=%d cost=%ld\n", b, n, N, D, cur); return 0; }
    long evals = 1; double t0 = now(); long pos = 0; double T = T0;
    fprintf(stderr, "b=%d h=%d E=%d n=%d N=%ld D=%d nfree=%d init cost %ld\n", b, h, E, n, N, D, nfree, cur);
    while (cur > 0 && now() - t0 < secs) {
        int e = freeidx[rnd() % nfree]; int old = volt[e]; int nv = rnd() % (n - 1); if (nv >= old) nv++;
        volt[e] = nv; long c = cost(); evals++;
        if (c <= cur || (double)(rnd() % 1000000) / 1e6 < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(volt)); }
        } else volt[e] = old;
        pos++; if (pos >= L) { pos = 0; memcpy(volt, bestv, sizeof(volt)); cur = best; }
        T = T0 * pow(T1 / T0, (double)pos / L);
    }
    memcpy(volt, bestv, sizeof(volt));
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", outp); FILE *o = fopen(fn, "w");
    for (int i = 0; i < nfree; i++) fprintf(o, "%d %d\n", freeidx[i], volt[freeidx[i]]); fclose(o);
    printf("RESULT b=%d n=%d N=%ld D=%d best=%ld evals=%ld secs=%.1f\n", b, n, N, D, best, evals, now() - t0);
    if (best == 0) {
        snprintf(fn, sizeof fn, "%s.edges", outp); o = fopen(fn, "w");
        fprintf(o, "%ld\n", N);
        for (int e = 0; e < E; e++) for (int g = 0; g < n; g++) fprintf(o, "%d %d\n", eu[e] * n + g, ev[e] * n + (g + volt[e]) % n);
        fclose(o);
    }
    return 0;
}
