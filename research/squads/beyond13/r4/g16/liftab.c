/* g16: voltage lifts of a DEG-regular bipartite base over NON-CYCLIC abelian groups Z_a x Z_b (a|b allowed, any).
   Lift vertex (u,g) -> u*n+g, g = i*b+j for (i,j) in Z_a x Z_b, n=a*b. Edge (x,y) with voltage s: (x,g)~(y,g+s).
   Spanning-tree voltages fixed 0. Cost = #ordered pairs at distance > D, from sources (u,0) for all base u
   (exact: translations by G are automorphisms). Writes OUT.best (free-edge voltages) and OUT.edges at cost 0.
   Usage: liftab BASE a b D seconds seed OUT [T0 T1 L]   START=file (lines "e g") optional. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXE 2048
#define MAXV 256
#define MAXD 8
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
int b, E, n, D, A1, A2, DEG; long N;
int eu[MAXE], ev[MAXE], volt[MAXE], treeE[MAXE];
int inc[MAXV][MAXD], sgn[MAXV][MAXD];
int *neg, *vis, stamp = 0, *qu;
int freeidx[MAXE], nfree;

/* bit-parallel cost: 64 sources per pass; nbr[] rebuilt from the voltages before each cost. cap = early abort */
static uint64_t *cur, *nxt; static int *nbr;
static void build_nbr(void) {
    for (int w = 0; w < b; w++) for (int g = 0; g < n; g++) {
        long v = (long)w * n + g; int gi = g / A2, gj = g - gi * A2;
        for (int k = 0; k < DEG; k++) {
            int e = inc[w][k], s = sgn[w][k]; int w2, sh;
            if (s > 0) { w2 = ev[e]; sh = volt[e]; } else { w2 = eu[e]; sh = neg[volt[e]]; }
            int si = sh / A2, sj = sh - si * A2;
            int hi = gi + si; if (hi >= A1) hi -= A1;
            int hj = gj + sj; if (hj >= A2) hj -= A2;
            nbr[v * DEG + k] = w2 * n + hi * A2 + hj;
        }
    }
}
long cost_cap(long cap) {
    long total = 0;
    for (int u0 = 0; u0 < b; u0 += 64) {
        int nb_ = b - u0 < 64 ? b - u0 : 64;
        uint64_t mask = nb_ == 64 ? ~0ULL : ((1ULL << nb_) - 1);
        for (long v = 0; v < N; v++) cur[v] = 0;
        for (int j = 0; j < nb_; j++) cur[(long)(u0 + j) * n] |= 1ULL << j;
        for (int lev = 0; lev < D; lev++) {
            for (long v = 0; v < N; v++) {
                uint64_t acc = cur[v]; const int *p = nbr + v * DEG;
                for (int k = 0; k < DEG; k++) acc |= cur[p[k]];
                nxt[v] = acc;
            }
            uint64_t *t = cur; cur = nxt; nxt = t;
        }
        long reached = 0;
        for (long v = 0; v < N; v++) reached += __builtin_popcountll(cur[v]);
        total += (long)nb_ * N - reached;
        if (total > cap) return total;
        (void)mask;
    }
    return total;
}
static inline long cost(void) { build_nbr(); return cost_cap(1L << 60); }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: liftab BASE a b D seconds seed OUT [T0 T1 L]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int nb; if (!f || fscanf(f, "%d", &nb) != 1) return 2; b = nb;
    E = 0; while (E < MAXE && fscanf(f, "%d %d", &eu[E], &ev[E]) == 2) E++;
    fclose(f);
    A1 = atoi(argv[2]); A2 = atoi(argv[3]); n = A1 * A2; D = atoi(argv[4]); double secs = atof(argv[5]);
    rs = strtoull(argv[6], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *outp = argv[7];
    double T0 = argc > 8 ? atof(argv[8]) : 2.0, T1 = argc > 9 ? atof(argv[9]) : 0.05; long L = argc > 10 ? atol(argv[10]) : 2000;
    N = (long)b * n;
    neg = malloc(sizeof(int) * n);
    for (int g = 0; g < n; g++) { int gi = g / A2, gj = g % A2; neg[g] = ((A1 - gi) % A1) * A2 + (A2 - gj) % A2; }
    cur = calloc(N, sizeof(uint64_t)); nxt = calloc(N, sizeof(uint64_t));
    int dg[MAXV] = {0};
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e];
        inc[u][dg[u]] = e; sgn[u][dg[u]++] = 1;
        inc[v][dg[v]] = e; sgn[v][dg[v]++] = -1;
    }
    DEG = dg[0]; nbr = malloc(sizeof(int) * N * DEG);
    for (int u = 0; u < b; u++) if (dg[u] != DEG) { fprintf(stderr, "not regular at %d\n", u); return 3; }
    int seen[MAXV] = {0}, bq[MAXV], bh = 0, bt = 0;
    seen[0] = 1; bq[bt++] = 0;
    while (bh < bt) { int x = bq[bh++]; for (int k = 0; k < DEG; k++) { int e = inc[x][k]; int y = sgn[x][k] > 0 ? ev[e] : eu[e];
        if (!seen[y]) { seen[y] = 1; treeE[e] = 1; bq[bt++] = y; } } }
    if (bt != b) { fprintf(stderr, "base disconnected\n"); return 4; }
    nfree = 0; for (int e = 0; e < E; e++) { volt[e] = 0; if (!treeE[e]) freeidx[nfree++] = e; }
    if (getenv("START")) { FILE *s = fopen(getenv("START"), "r"); int e, x; while (s && fscanf(s, "%d %d", &e, &x) == 2) volt[e] = x % n; if (s) fclose(s); }
    else for (int i = 0; i < nfree; i++) volt[freeidx[i]] = rnd() % n;
    long cur_c = cost(), best = cur_c; int bestv[MAXE]; memcpy(bestv, volt, sizeof(volt));
    long evals = 1; double t0 = now(); long pos = 0; double T = T0;
    fprintf(stderr, "b=%d E=%d DEG=%d G=Z%dxZ%d N=%ld D=%d nfree=%d init cost %ld\n", b, E, DEG, A1, A2, N, D, nfree, cur_c);
    while (cur_c > 0 && now() - t0 < secs) {
        int e = freeidx[rnd() % nfree]; int old = volt[e]; int nv = rnd() % (n - 1); if (nv >= old) nv++;
        volt[e] = nv; evals++;
        /* Metropolis: accept iff c <= cur_c - T ln(u); draw the threshold first so the cost can abort early */
        double uu = ((double)(rnd() % 1000000) + 0.5) / 1e6;
        long cap = cur_c + (long)floor(-T * log(uu));
        build_nbr(); long c = cost_cap(cap);
        if (c <= cap) {
            cur_c = c;
            if (cur_c < best) { best = cur_c; memcpy(bestv, volt, sizeof(volt)); }
        } else volt[e] = old;
        pos++; if (pos >= L) { pos = 0; memcpy(volt, bestv, sizeof(volt)); cur_c = best; }
        T = T0 * pow(T1 / T0, (double)pos / L);
    }
    memcpy(volt, bestv, sizeof(volt));
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", outp); FILE *o = fopen(fn, "w");
    for (int i = 0; i < nfree; i++) fprintf(o, "%d %d\n", freeidx[i], volt[freeidx[i]]); fclose(o);
    printf("RESULT G=Z%dxZ%d n=%d N=%ld D=%d best=%ld evals=%ld secs=%.1f\n", A1, A2, n, N, D, best, evals, now() - t0);
    if (best == 0) {
        snprintf(fn, sizeof fn, "%s.edges", outp); o = fopen(fn, "w");
        fprintf(o, "%ld\n", N);
        for (int e = 0; e < E; e++) for (int g = 0; g < n; g++) { int gi = g / A2, gj = g % A2, si = volt[e] / A2, sj = volt[e] % A2; int hi = (gi + si) % A1, hj = (gj + sj) % A2; fprintf(o, "%d %d\n", eu[e] * n + g, ev[e] * n + hi * A2 + hj); }
        fclose(o);
    }
    return 0;
}
