/* liftg: voltage-lift annealer over an arbitrary finite group given by its multiplication table.
   Usage: liftg BASE GROUPFILE D seconds seed OUTPREFIX [T0 T1 L]
   GROUPFILE: first integer k, then k*k integers: mul[a*k+b] (identity must be index 0).
   Lift vertex (u,g) -> id u*k+g. Edge e=(a,b) voltage x: (a,g) ~ (b, g*x) (right multiplication).
   Spanning-tree voltages fixed to identity (gauge). Cost = number of (source u, target) pairs at distance > D,
   sources (u, identity) for all base u (exact by left-multiplication automorphisms).
   START=file ("e x" lines) optional. Writes OUTPREFIX.best; OUTPREFIX.edges when cost 0 (edge list for apsp). */
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
int b, h, E, k, D; long N;
int *mul, *inv;
int eu[MAXE], ev[MAXE], volt[MAXE], isfree[MAXE];
int inc[MAXV][3], sgn[MAXV][3];
int *vis, stamp = 0, *qu;
int nfree, freeidx[MAXE];

/* from base vertex w0 slot kk: target base vertex and voltage (already inverted when traversed backwards) */
int tgt[MAXV][3], tvol[MAXV][3];

long cost(void) {
    long total = 0;
    for (int u = 0; u < b; u++) {
        stamp++;
        int head = 0, tail = 0; long src = (long)u * k;
        vis[src] = stamp; qu[tail++] = (int)src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                long x = qu[head]; int w0 = (int)(x / k), g = (int)(x % k);
                for (int s = 0; s < 3; s++) {
                    int w = tgt[w0][s];
                    int gg = mul[g * k + tvol[w0][s]];
                    long y = (long)w * k + gg;
                    if (vis[y] != stamp) { vis[y] = stamp; qu[tail++] = (int)y; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void setvoltages(void) {
    for (int u = 0; u < b; u++) for (int s = 0; s < 3; s++) {
        int e = inc[u][s];
        if (sgn[u][s] > 0) { tgt[u][s] = ev[e]; tvol[u][s] = volt[e]; }
        else { tgt[u][s] = eu[e]; tvol[u][s] = inv[volt[e]]; }
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: liftg BASE GROUPFILE D seconds seed OUTPREFIX [T0 T1 L]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int nb; if (fscanf(f, "%d", &nb) != 1) return 2; b = nb; h = b / 2;
    E = 0;
    for (int i = 0; i < 3 * h; i++) { if (fscanf(f, "%d %d", &eu[E], &ev[E]) != 2) return 2; E++; }
    fclose(f);
    f = fopen(argv[2], "r"); if (fscanf(f, "%d", &k) != 1) return 5;
    mul = malloc(sizeof(int) * k * k); inv = malloc(sizeof(int) * k);
    for (long i = 0; i < (long)k * k; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 5;
    fclose(f);
    for (int a = 0; a < k; a++) { int found = 0; for (int c = 0; c < k; c++) if (mul[a * k + c] == 0) { inv[a] = c; found = 1; break; } if (!found) return 6; }
    D = atoi(argv[3]); double secs = atof(argv[4]); rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 2.0, T1 = argc > 8 ? atof(argv[8]) : 0.05; long L = argc > 9 ? atol(argv[9]) : 20000;
    N = (long)b * k;
    vis = calloc(N, sizeof(int)); qu = malloc(N * sizeof(int));
    int dg[MAXV] = {0};
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e];
        inc[u][dg[u]] = e; sgn[u][dg[u]++] = 1;
        inc[v][dg[v]] = e; sgn[v][dg[v]++] = -1;
    }
    for (int u = 0; u < b; u++) if (dg[u] != 3) { fprintf(stderr, "degree %d at %d\n", dg[u], u); return 3; }
    int seen[MAXV] = {0}, bq[MAXV], bh = 0, bt = 0; int treeE[MAXE] = {0};
    seen[0] = 1; bq[bt++] = 0;
    while (bh < bt) { int x = bq[bh++]; for (int q = 0; q < 3; q++) { int e = inc[x][q]; int y = sgn[x][q] > 0 ? ev[e] : eu[e];
        if (!seen[y]) { seen[y] = 1; treeE[e] = 1; bq[bt++] = y; } } }
    if (bt != b) { fprintf(stderr, "base disconnected\n"); return 4; }
    nfree = 0; for (int e = 0; e < E; e++) { isfree[e] = !treeE[e]; volt[e] = 0; if (isfree[e]) freeidx[nfree++] = e; }
    if (getenv("START")) { FILE *s = fopen(getenv("START"), "r"); int e, x; while (s && fscanf(s, "%d %d", &e, &x) == 2) volt[e] = x % k; if (s) fclose(s); }
    else for (int i = 0; i < nfree; i++) volt[freeidx[i]] = rnd() % k;
    setvoltages();
    long cur = cost(), best = cur; int bestv[MAXE]; memcpy(bestv, volt, sizeof(volt));
    long evals = 1; double t0 = now(); long pos = 0; double T = T0;
    fprintf(stderr, "b=%d h=%d E=%d k=%d N=%ld D=%d nfree=%d init cost %ld\n", b, h, E, k, N, D, nfree, cur);
    while (cur > 0 && now() - t0 < secs) {
        int e = freeidx[rnd() % nfree]; int old = volt[e]; int nv = rnd() % (k - 1); if (nv >= old) nv++;
        volt[e] = nv; setvoltages(); long c = cost(); evals++;
        if (c <= cur || (double)(rnd() % 1000000) / 1e6 < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(volt)); }
        } else { volt[e] = old; }
        pos++; if (pos >= L) { pos = 0; memcpy(volt, bestv, sizeof(volt)); cur = best; setvoltages(); }
        T = T0 * pow(T1 / T0, (double)pos / L);
    }
    memcpy(volt, bestv, sizeof(volt)); setvoltages();
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", outp); FILE *o = fopen(fn, "w");
    for (int i = 0; i < nfree; i++) fprintf(o, "%d %d\n", freeidx[i], volt[freeidx[i]]); fclose(o);
    printf("RESULT k=%d N=%ld D=%d best=%ld evals=%ld secs=%.1f\n", k, N, D, best, evals, now() - t0);
    if (best == 0) {
        snprintf(fn, sizeof fn, "%s.edges", outp); o = fopen(fn, "w");
        fprintf(o, "%ld\n", N);
        for (int e = 0; e < E; e++) for (int g = 0; g < k; g++) fprintf(o, "%d %d\n", eu[e] * k + g, ev[e] * k + mul[g * k + volt[e]]);
        fclose(o);
    }
    return 0;
}
