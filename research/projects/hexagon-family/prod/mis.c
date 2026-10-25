/* mis.c: ARW-style iterated local search for a maximum independent set in an explicit graph.
   Input: "n m" then m lines "u v" (edges = conflicts). Output: best set (vertex ids) to OUT.
   usage: mis GRAPH OUT SECONDS SEED [SEEDSET] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
static int n; static int *off, *adj; static int *inS, *tight, *pos, *sol, ns;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void add(int v) { inS[v] = 1; pos[v] = ns; sol[ns++] = v; for (int k = off[v]; k < off[v + 1]; k++) tight[adj[k]]++; }
static void rem(int v) { inS[v] = 0; int p = pos[v]; sol[p] = sol[--ns]; pos[sol[p]] = p; for (int k = off[v]; k < off[v + 1]; k++) tight[adj[k]]--; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int free_add(void) { int c = 0; int st = rnd() % n; for (int t = 0; t < n; t++) { int v = (st + t) % n; if (!inS[v] && tight[v] == 0) { add(v); c++; } } return c; }
static int two_improve(void) {   /* (1,2)-swaps */
    int improved = 0, *cand = malloc(sizeof(int) * n);
    for (int it = 0; it < ns; it++) {
        int x = sol[rnd() % ns], nc = 0;
        for (int k = off[x]; k < off[x + 1]; k++) { int v = adj[k]; if (!inS[v] && tight[v] == 1) cand[nc++] = v; }
        if (nc < 2) continue;
        for (int a = 0; a < nc && !improved; a++) for (int b = a + 1; b < nc; b++) {
            int u = cand[a], w = cand[b], conf = 0;
            for (int k = off[u]; k < off[u + 1]; k++) if (adj[k] == w) { conf = 1; break; }
            if (!conf) { rem(x); add(u); add(w); free_add(); improved = 1; break; }
        }
        if (improved) break;
    }
    free(cand); return improved;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); long m; if (fscanf(f, "%d %ld", &n, &m) != 2) return 1;
    int *eu = malloc(sizeof(int) * m), *ev = malloc(sizeof(int) * m); off = calloc(n + 1, sizeof(int));
    for (long e = 0; e < m; e++) { if (fscanf(f, "%d %d", &eu[e], &ev[e]) != 2) return 1; off[eu[e] + 1]++; off[ev[e] + 1]++; }
    fclose(f); for (int i = 0; i < n; i++) off[i + 1] += off[i];
    adj = malloc(sizeof(int) * 2 * m); int *fill = calloc(n, sizeof(int));
    for (long e = 0; e < m; e++) { adj[off[eu[e]] + fill[eu[e]]++] = ev[e]; adj[off[ev[e]] + fill[ev[e]]++] = eu[e]; }
    double tl = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    inS = calloc(n, sizeof(int)); tight = calloc(n, sizeof(int)); pos = calloc(n, sizeof(int)); sol = malloc(sizeof(int) * n); ns = 0;
    if (argc > 5) { FILE *g = fopen(argv[5], "r"); int v; while (g && fscanf(g, "%d", &v) == 1) if (!inS[v] && tight[v] == 0) add(v); if (g) fclose(g); }
    free_add();
    int best = ns, *bsol = malloc(sizeof(int) * n); memcpy(bsol, sol, sizeof(int) * ns);
    double t0 = now(), last = t0; long it = 0;
    while (now() - t0 < tl) {
        while (two_improve()) {}
        if (ns > best) { best = ns; memcpy(bsol, sol, sizeof(int) * ns); }
        else if (ns < best - 2 || (rnd() % 1000) < 5) { /* return to best */
            while (ns) rem(sol[ns - 1]); for (int i = 0; i < best; i++) add(bsol[i]); }
        /* perturb: force in 1 (sometimes 2) random non-solution vertices */
        int kk = (rnd() % 4 == 0) ? 2 : 1;
        for (int t = 0; t < kk; t++) { int v; do v = rnd() % n; while (inS[v]);
            for (int k = off[v]; k < off[v + 1]; k++) if (inS[adj[k]]) rem(adj[k]);
            add(v); }
        free_add(); it++;
        if (now() - last > 10) { fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d\n", now() - t0, it, ns, best); last = now(); }
    }
    FILE *o = fopen(argv[2], "w"); for (int i = 0; i < best; i++) fprintf(o, "%d\n", bsol[i]); fclose(o);
    printf("BEST %d\n", best); return 0;
}
