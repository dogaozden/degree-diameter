/* e13: non-abelian voltage-lift annealer. Base: bipartite cubic multigraph, file "2h" then 3h lines "a b" (a in [0,h), b in [h,2h)).
   Group: binary file from tools/groups.py: int32 N, then N*N uint16, row g: T[g*N+h] = g*h, identity 0.
   Lift vertex (u,g) -> u*N+g. Edge e=(a,b) voltage x: (a,g) ~ (b, g*x). Spanning-tree voltages = identity.
   Cost = sum over base u of #vertices of lift not within distance D of (u, identity) (exact: Gamma acts by left mult.)
   plus 1000 per duplicate lift edge (parallel base edges with equal voltage).
   Usage: nlift GROUP.bin BASE D seconds seed OUTPREFIX [T0 T1 L]   (START=file with "edgeidx volt" lines optional)
   Writes OUTPREFIX.best ("edgeidx volt" for free edges) and at cost 0 OUTPREFIX.edges ("n" then "u v" lines). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXE 256
#define MAXV 64
#define MAXN 1024
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
int b, h, E, N, D, M; /* M = group order */
int eu[MAXE], ev[MAXE], volt[MAXE], isfree[MAXE], freeidx[MAXE], nfree;
int inc[MAXV][3], sgn[MAXV][3];
uint16_t *T; int inv[MAXN];
int *vis, stamp = 0, *qu;

static inline int mul(int g, int h2) { return T[(long)g * M + h2]; }

long cost(void) {
    long total = 0;
    /* duplicate lift edges */
    for (int e = 0; e < E; e++) for (int f = e + 1; f < E; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && volt[e] == volt[f]) total += 1000;
    long NV = (long)b * M;
    for (int u = 0; u < b; u++) {
        stamp++;
        int head = 0, tail = 0; long src = (long)u * M;
        vis[src] = stamp; qu[tail++] = (int)src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                long x = qu[head]; int w0 = (int)(x / M), g = (int)(x % M);
                for (int k = 0; k < 3; k++) {
                    int e = inc[w0][k], s = sgn[w0][k];
                    long y;
                    if (s > 0) y = (long)ev[e] * M + mul(g, volt[e]);
                    else y = (long)eu[e] * M + mul(g, inv[volt[e]]);
                    if (vis[y] != stamp) { vis[y] = stamp; qu[tail++] = (int)y; }
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: nlift GROUP.bin BASE D seconds seed OUTPREFIX [T0 T1 L]\n"); return 1; }
    FILE *g = fopen(argv[1], "rb"); int32_t N32; if (!g || fread(&N32, 4, 1, g) != 1) return 2;
    M = N32; if (M > MAXN) { fprintf(stderr, "group too big\n"); return 2; }
    T = malloc((long)M * M * 2); if (fread(T, 2, (long)M * M, g) != (size_t)((long)M * M)) return 2; fclose(g);
    for (int x = 0; x < M; x++) for (int y = 0; y < M; y++) if (mul(x, y) == 0) inv[x] = y;
    FILE *f = fopen(argv[2], "r"); int nb; if (!f || fscanf(f, "%d", &nb) != 1) return 2; b = nb; h = b / 2;
    E = 0; for (int i = 0; i < 3 * h; i++) { if (fscanf(f, "%d %d", &eu[E], &ev[E]) != 2) return 2; E++; } fclose(f);
    D = atoi(argv[3]); double secs = atof(argv[4]); rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 3.0, T1 = argc > 8 ? atof(argv[8]) : 0.05; long L = argc > 9 ? atol(argv[9]) : 3000;
    N = b * M;
    vis = calloc(N + 1, sizeof(int)); qu = malloc((N + 1) * sizeof(int));
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
    if (getenv("START")) { FILE *s = fopen(getenv("START"), "r"); int e, x; while (s && fscanf(s, "%d %d", &e, &x) == 2) volt[e] = x % M; if (s) fclose(s); }
    else for (int i = 0; i < nfree; i++) volt[freeidx[i]] = rnd() % M;
    long cur = cost(), best = cur; int bestv[MAXE]; memcpy(bestv, volt, sizeof(volt));
    long evals = 1; double t0 = now(); long pos = 0; double Tm = T0;
    fprintf(stderr, "b=%d E=%d M=%d N=%d D=%d nfree=%d init cost %ld\n", b, E, M, N, D, nfree, cur);
    double asecs = getenv("TABU") ? secs * 0.4 : secs;
    while (cur > 0 && now() - t0 < asecs) {
        int e = freeidx[rnd() % nfree]; int old = volt[e]; int nv = rnd() % (M - 1); if (nv >= old) nv++;
        volt[e] = nv; long c = cost(); evals++;
        if (c <= cur || (double)(rnd() % 1000000) / 1e6 < exp(-(double)(c - cur) / Tm)) {
            cur = c; if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(volt)); }
        } else volt[e] = old;
        pos++; if (pos >= L) { pos = 0; memcpy(volt, bestv, sizeof(volt)); cur = best; }
        Tm = T0 * pow(T1 / T0, (double)pos / L);
    }
    if (getenv("TABU") && best > 0) { /* full-neighbourhood tabu search from the annealed best */
        static long tabu_until[MAXE][MAXN]; memset(tabu_until, 0, sizeof tabu_until);
        memcpy(volt, bestv, sizeof(volt)); cur = best; long it = 0; double tt0 = now();
        while (best > 0 && now() - tt0 < secs * 0.5) {
            long bc = -1; int be = -1, bv = -1;
            for (int i = 0; i < nfree; i++) { int e = freeidx[i]; int old = volt[e];
                for (int v = 0; v < M; v++) { if (v == old) continue;
                    volt[e] = v; long c = cost(); evals++;
                    int tb = tabu_until[e][v] > it && c >= best;
                    if (!tb && (bc < 0 || c < bc || (c == bc && rnd() % 2))) { bc = c; be = e; bv = v; }
                }
                volt[e] = old; }
            if (bc < 0) break;
            tabu_until[be][volt[be]] = it + 7 + rnd() % 5;
            volt[be] = bv; cur = bc; it++;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(volt)); }
        }
        fprintf(stderr, "tabu iters %ld best %ld\n", it, best);
    }
    memcpy(volt, bestv, sizeof(volt));
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", outp); FILE *o = fopen(fn, "w");
    for (int i = 0; i < nfree; i++) fprintf(o, "%d %d\n", freeidx[i], volt[freeidx[i]]); fclose(o);
    printf("RESULT b=%d M=%d N=%d D=%d best=%ld evals=%ld secs=%.1f\n", b, M, N, D, best, evals, now() - t0);
    if (best == 0) {
        snprintf(fn, sizeof fn, "%s.edges", outp); o = fopen(fn, "w");
        fprintf(o, "%d\n", N);
        for (int e = 0; e < E; e++) for (int gg = 0; gg < M; gg++)
            fprintf(o, "%d %d\n", eu[e] * M + gg, ev[e] * M + mul(gg, volt[e]));
        fclose(o);
    }
    return 0;
}
