/* liftab = liftd with abelian group Z_a x Z_c (env AB="a c", n = a*c): same cost and CLI. */
/* liftd = lift.c (squad r2/e16) with env DEG (base degree, default 3; director, beyond-d13). Base = bipartite DEG-regular multigraph (sides A=[0,h), B=[h,2h)), voltages in Z_n.
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
int b, h, E, n, D; long N; int AA = 1, CC = 1;
static inline int addg(int g, int s) { int gx = g / CC, gy = g % CC, sx = s / CC, sy = s % CC; int x = gx + sx; if (x >= AA) x -= AA; int y = gy + sy; if (y >= CC) y -= CC; return x * CC + y; }
static inline int ainv(int v) { int vx = v / CC, vy = v % CC; int x = vx ? AA - vx : 0; int y = vy ? CC - vy : 0; return x * CC + y; }
int eu[MAXE], ev[MAXE], volt[MAXE], isfree[MAXE];
int inc[MAXV][8], sgn[MAXV][8]; int DEG = 3;
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
                for (int k = 0; k < DEG; k++) {
                    int e = inc[w0][k], s = sgn[w0][k];
                    int w = s > 0 ? ev[e] : eu[e];
                    int sh = s > 0 ? volt[e] : ainv(volt[e]);
                    int gg = addg(g, sh);
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

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: lift BASE n D seconds seed OUTPREFIX [T0 T1 L]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int nb; if (fscanf(f, "%d", &nb) != 1) return 2; b = nb; h = b / 2;
    E = 0;
    if (getenv("DEG")) DEG = atoi(getenv("DEG"));
    for (int i = 0; i < DEG * h; i++) { if (fscanf(f, "%d %d", &eu[E], &ev[E]) != 2) return 2; E++; }
    fclose(f);
    { const char *ab = getenv("AB"); if (!ab || sscanf(ab, "%d %d", &AA, &CC) != 2) { fprintf(stderr, "set AB=\"a c\"\n"); return 5; } }
    n = AA * CC; if (n != atoi(argv[2])) { fprintf(stderr, "n must equal AA*CC\n"); return 6; }
     D = atoi(argv[3]); double secs = atof(argv[4]); rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 2.0, T1 = argc > 8 ? atof(argv[8]) : 0.05; long L = argc > 9 ? atol(argv[9]) : 20000;
    N = (long)b * n;
    vis = calloc(N, sizeof(int)); qu = malloc(N * sizeof(int));
    int dg[MAXV] = {0};
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e];
        inc[u][dg[u]] = e; sgn[u][dg[u]++] = 1;
        inc[v][dg[v]] = e; sgn[v][dg[v]++] = -1;
    }
    for (int u = 0; u < b; u++) if (dg[u] != DEG) { fprintf(stderr, "degree %d at %d\n", dg[u], u); return 3; }
    /* spanning tree (BFS in base) */
    int seen[MAXV] = {0}, bq[MAXV], bh = 0, bt = 0; int treeE[MAXE] = {0};
    seen[0] = 1; bq[bt++] = 0;
    while (bh < bt) { int x = bq[bh++]; for (int k = 0; k < DEG; k++) { int e = inc[x][k]; int y = sgn[x][k] > 0 ? ev[e] : eu[e];
        if (!seen[y]) { seen[y] = 1; treeE[e] = 1; bq[bt++] = y; } } }
    if (bt != b) { fprintf(stderr, "base disconnected\n"); return 4; }
    nfree = 0; for (int e = 0; e < E; e++) { isfree[e] = !treeE[e]; volt[e] = 0; if (isfree[e]) freeidx[nfree++] = e; }
    /* optional start */
    if (getenv("START")) { FILE *s = fopen(getenv("START"), "r"); int e, x; while (s && fscanf(s, "%d %d", &e, &x) == 2) volt[e] = x % n; if (s) fclose(s); }
    else for (int i = 0; i < nfree; i++) volt[freeidx[i]] = rnd() % n;
    long cur = cost(), best = cur; int bestv[MAXE]; memcpy(bestv, volt, sizeof(volt));
    long evals = 1; double t0 = now(); long pos = 0; double T = T0;
    fprintf(stderr, "b=%d h=%d E=%d n=%d N=%ld D=%d nfree=%d init cost %ld\n", b, h, E, n, N, D, nfree, cur);
    while (cur > 0 && now() - t0 < secs) {
        int e = freeidx[rnd() % nfree]; int old = volt[e]; int nv = rnd() % (n - 1); if (nv >= old) nv++;
        volt[e] = nv; long c = cost(); evals++;
        if (c <= cur || (double)(rnd() % 1000000) / 1e6 < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(volt)); }
        } else volt[e] = old;
        pos++; if (pos >= L) { pos = 0; /* restart from best with reheating */ memcpy(volt, bestv, sizeof(volt)); cur = best; }
        T = T0 * pow(T1 / T0, (double)pos / L);
    }
    memcpy(volt, bestv, sizeof(volt));
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", outp); FILE *o = fopen(fn, "w");
    for (int i = 0; i < nfree; i++) fprintf(o, "%d %d\n", freeidx[i], volt[freeidx[i]]); fclose(o);
    printf("RESULT b=%d n=%d N=%ld D=%d best=%ld evals=%ld secs=%.1f\n", b, n, N, D, best, evals, now() - t0);
    if (best == 0) {
        snprintf(fn, sizeof fn, "%s.edges", outp); o = fopen(fn, "w");
        fprintf(o, "%ld\n", 2 * N / 2 * 0 + N);
        for (int e = 0; e < E; e++) for (int g = 0; g < n; g++) fprintf(o, "%d %d\n", eu[e] * n + g, ev[e] * n + addg(g, volt[e]));
        fclose(o);
    }
    return 0;
}
