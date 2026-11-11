/* e16: cyclic voltage-lift annealer. Base = bipartite cubic multigraph (sides A=[0,h), B=[h,2h)), voltages in Z_n.
   Lift vertex (u,g) -> id u*n+g. Edge e=(a,b) with voltage x: (a,g)~(b,g+x). Spanning tree voltages fixed 0.
   Cost = number of ordered pairs at distance > D, counted from sources (u,0) for all base u (exact by Z_n symmetry).
   Usage: lift BASE n D seconds seed OUTPREFIX [T0 T1 L] ; START=file (voltages "e x" lines) optional.
   Writes OUTPREFIX.best (voltages), and OUTPREFIX.edges when cost 0 (edge list for apsp). */
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
int b, h, E, n, D; long N;
int eu[MAXE], ev[MAXE], volt[MAXE], isfree[MAXE];
int inc[MAXV][3], sgn[MAXV][3];
int *vis, stamp = 0, *qu, *dd;
int nfree, freeidx[MAXE];

long cost(void) {
    long total = 0;
    for (int u = 0; u < b; u++) {
        stamp++;
        int head = 0, tail = 0; long src = (long)u * n;
        vis[src] = stamp; qu[tail++] = (int)src; long reached = 1;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                long x = qu[head]; int w0 = (int)(x / n), g = (int)(x % n);
                for (int k = 0; k < 3; k++) {
                    int e = inc[w0][k], s = sgn[w0][k];
                    int w = s > 0 ? ev[e] : eu[e];
                    int sh = s > 0 ? volt[e] : (n - volt[e]) % n;
                    int gg = g + sh; if (gg >= n) gg -= n;
                    long y = (long)w * n + gg;
                    if (vis[y] != stamp) { vis[y] = stamp; qu[tail++] = (int)y; }
                }
            }
        }
        reached = tail;
        total += N - reached;
    }
    return total;
}


/* h02 scan: exhaustive 1-opt neighbourhood scan with plateau tabu walk (cyclic Z_n voltage lifts).
   usage: scan BASE n D seconds seed OUTPREFIX [TENURE]   START=file (voltages "e x") optional
   Each step: enumerate all (free edge, new voltage) moves in random order; take the first strictly improving one.
   If none, take a random cost-equal move not on tabu (edge changed within TENURE steps). */
static long eval_cost_cnt = 0;

long cost_lim(long lim) {
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
                    int w = s > 0 ? ev[e] : eu[e];
                    int sh = s > 0 ? volt[e] : (n - volt[e]) % n;
                    int gg = g + sh; if (gg >= n) gg -= n;
                    long y = (long)w * n + gg;
                    if (vis[y] != stamp) { vis[y] = stamp; qu[tail++] = (int)y; }
                }
            }
        }
        total += N - tail;
        if (total > lim) return total;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: scan BASE n D seconds seed OUTPREFIX [TENURE]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int nb; if (fscanf(f, "%d", &nb) != 1) return 2; b = nb; h = b / 2;
    E = 0;
    for (int i = 0; i < 3 * h; i++) { if (fscanf(f, "%d %d", &eu[E], &ev[E]) != 2) return 2; E++; }
    fclose(f);
    n = atoi(argv[2]); D = atoi(argv[3]); double secs = atof(argv[4]); rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[6]; int tenure = argc > 7 ? atoi(argv[7]) : 6;
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
    long evals = 1; double t0 = now(); long iter = 0;
    static long tabu_until[MAXE]; for (int e = 0; e < E; e++) tabu_until[e] = -1;
    int nmoves = nfree * (n - 1);
    int *mv = malloc(sizeof(int) * nmoves * 2); int *cand = malloc(sizeof(int) * nmoves * 2);
    fprintf(stderr, "b=%d E=%d n=%d N=%ld D=%d nfree=%d init cost %ld\n", b, E, n, N, D, nfree, cur);
    while (cur > 0 && now() - t0 < secs) {
        iter++;
        /* build move list, shuffle */
        int m = 0;
        for (int i = 0; i < nfree; i++) for (int v = 0; v < n; v++) if (v != volt[freeidx[i]]) { mv[2*m] = freeidx[i]; mv[2*m+1] = v; m++; }
        for (int i = m - 1; i > 0; i--) { int j = rnd() % (i + 1); int t0_ = mv[2*i]; mv[2*i] = mv[2*j]; mv[2*j] = t0_; t0_ = mv[2*i+1]; mv[2*i+1] = mv[2*j+1]; mv[2*j+1] = t0_; }
        int nc = 0, found = 0;
        for (int i = 0; i < m && !found; i++) {
            if ((i & 127) == 0 && now() - t0 > secs) break;
            int e = mv[2*i], v = mv[2*i+1]; int old = volt[e];
            volt[e] = v; long c = cost_lim(cur); evals++;
            if (c < cur) { cur = c; found = 1; if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(volt)); } break; }
            if (c == cur && tabu_until[e] < iter) { cand[2*nc] = e; cand[2*nc+1] = v; nc++; }
            volt[e] = old;
        }
        if (!found) {
            if (nc == 0) { /* everything tabu: random free move */ int e = freeidx[rnd() % nfree]; volt[e] = rnd() % n; cur = cost(); evals++; }
            else { int k = rnd() % nc; int e = cand[2*k]; volt[e] = cand[2*k+1]; tabu_until[e] = iter + tenure; }
        }
        if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(volt)); }
        if (iter % 20 == 0) fprintf(stderr, "iter %ld cur %ld best %ld evals %ld t=%.1f\n", iter, cur, best, evals, now() - t0);
    }
    memcpy(volt, bestv, sizeof(volt));
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", outp); FILE *o = fopen(fn, "w");
    for (int i = 0; i < nfree; i++) fprintf(o, "%d %d\n", freeidx[i], volt[freeidx[i]]); fclose(o);
    printf("RESULT b=%d n=%d N=%ld D=%d best=%ld evals=%ld iters=%ld secs=%.1f\n", b, n, N, D, best, evals, iter, now() - t0);
    if (best == 0) {
        snprintf(fn, sizeof fn, "%s.edges", outp); o = fopen(fn, "w");
        fprintf(o, "%ld\n", N);
        for (int e = 0; e < E; e++) for (int g = 0; g < n; g++) fprintf(o, "%d %d\n", eu[e] * n + g, ev[e] * n + (g + volt[e]) % n);
        fclose(o);
    }
    return 0;
}
