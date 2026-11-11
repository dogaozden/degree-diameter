/* a05: voltage-lift annealer over an arbitrary finite abelian group Z_m1 x ... x Z_mk (mixed radix).
   Base = bipartite cubic multigraph (sides A=[0,h), B=[h,2h)), file: "2h" then "u v" lines (u in A, v in B).
   Lift vertex (u,g) -> u*n+g, n = prod m_i. Edge e=(a,b) voltage x: (a,g)~(b,g+x). Spanning-tree voltages 0.
   Cost = # ordered pairs at distance > D, counted from (u,0) for every base u (exact: translations are automorphisms).
   Usage: ablift BASE "m1,m2,..." D seconds seed OUTPREFIX [T0 T1 L]; env START=file ("edgeidx element" lines).
   Writes OUTPREFIX.best; on cost 0 writes OUTPREFIX.edges (first line N, then "u v" lines). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXE 1024
#define MAXV 256
#define MAXN 4096
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
int b, h, E, n, D; long N;
int eu[MAXE], ev[MAXE], volt[MAXE], isfree[MAXE], freeidx[MAXE], nfree;
int inc[MAXV][3], sgn[MAXV][3];
int *vis, stamp = 0, *qu;
static int *addt, *negt;           /* addt[g*n+h], negt[g] */
int nd, mods[8];

static void build_group(void) {
    n = 1; for (int i = 0; i < nd; i++) n *= mods[i];
    addt = malloc(sizeof(int) * (size_t)n * n); negt = malloc(sizeof(int) * n);
    for (int g = 0; g < n; g++) {
        int dg[8], t = g; for (int i = nd - 1; i >= 0; i--) { dg[i] = t % mods[i]; t /= mods[i]; }
        int ng = 0, st = 1; int ndg[8];
        for (int i = 0; i < nd; i++) ndg[i] = (mods[i] - dg[i]) % mods[i];
        for (int i = nd - 1; i >= 0; i--) { ng += ndg[i] * st; st *= mods[i]; }
        negt[g] = ng;
        for (int hh = 0; hh < n; hh++) {
            int hd[8], t2 = hh; for (int i = nd - 1; i >= 0; i--) { hd[i] = t2 % mods[i]; t2 /= mods[i]; }
            int r = 0, s2 = 1; for (int i = nd - 1; i >= 0; i--) { r += ((dg[i] + hd[i]) % mods[i]) * s2; s2 *= mods[i]; }
            addt[(size_t)g * n + hh] = r;
        }
    }
}

long cost(void) {
    long total = 0;
    for (int u = 0; u < b; u++) {
        stamp++;
        int head = 0, tail = 0; long src = (long)u * n;
        vis[src] = stamp; qu[tail++] = (int)src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                long x = qu[head]; int w0 = (int)(x / n), g = (int)(x % n);
                for (int k = 0; k < 3; k++) {
                    int e = inc[w0][k], s = sgn[w0][k];
                    int w, gg;
                    if (s > 0) { w = ev[e]; gg = addt[(size_t)g * n + volt[e]]; }
                    else { w = eu[e]; gg = addt[(size_t)g * n + negt[volt[e]]]; }
                    long y = (long)w * n + gg;
                    if (vis[y] != stamp) { vis[y] = stamp; qu[tail++] = (int)y; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: ablift BASE \"m1,m2,..\" D seconds seed OUTPREFIX [T0 T1 L]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int nb; if (!f || fscanf(f, "%d", &nb) != 1) return 2; b = nb; h = b / 2;
    E = 0;
    for (int i = 0; i < 3 * h; i++) { if (fscanf(f, "%d %d", &eu[E], &ev[E]) != 2) return 2; E++; }
    fclose(f);
    nd = 0; { char buf[256]; strncpy(buf, argv[2], 255); buf[255] = 0; char *tok = strtok(buf, ",");
      while (tok && nd < 8) { mods[nd++] = atoi(tok); tok = strtok(NULL, ","); } }
    build_group();
    if (n > MAXN) { fprintf(stderr, "group too big\n"); return 5; }
    D = atoi(argv[3]); double secs = atof(argv[4]); rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 2.0, T1 = argc > 8 ? atof(argv[8]) : 0.05; long L = argc > 9 ? atol(argv[9]) : 1200;
    N = (long)b * n;
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
    while (bh < bt) { int x = bq[bh++]; for (int k = 0; k < 3; k++) { int e = inc[x][k]; int y = sgn[x][k] > 0 ? ev[e] : eu[e];
        if (!seen[y]) { seen[y] = 1; treeE[e] = 1; bq[bt++] = y; } } }
    if (bt != b) { fprintf(stderr, "base disconnected\n"); return 4; }
    nfree = 0; for (int e = 0; e < E; e++) { isfree[e] = !treeE[e]; volt[e] = 0; if (isfree[e]) freeidx[nfree++] = e; }
    if (getenv("START")) { FILE *s = fopen(getenv("START"), "r"); int e, x; while (s && fscanf(s, "%d %d", &e, &x) == 2) volt[e] = x % n; if (s) fclose(s); }
    else for (int i = 0; i < nfree; i++) volt[freeidx[i]] = rnd() % n;
    long cur = cost(), best = cur; int bestv[MAXE]; memcpy(bestv, volt, sizeof(volt));
    long evals = 1; double t0 = now(); long pos = 0; double T = T0;
    fprintf(stderr, "b=%d E=%d n=%d N=%ld D=%d nfree=%d init cost %ld\n", b, E, n, N, D, nfree, cur);
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
        for (int e = 0; e < E; e++) for (int g = 0; g < n; g++)
            fprintf(o, "%d %d\n", eu[e] * n + g, ev[e] * n + addt[(size_t)g * n + volt[e]]);
        fclose(o);
    }
    return 0;
}
