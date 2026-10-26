/* ktabu.c: k-fixed tabu search for a relaxed set T of W(11):
   T has no two points on an S-line (S = regular spread), and every point of T has at most one collinear neighbour in T.
   penalty f = sum_{v in T} max(0, nbT[v]-1) + sum_s max(0, cs[s]-1).  When f == 0 the current size is recorded and k is raised
   (greedy add).  Moves: remove the most-penalised point of T (random among conflicting, tabu-aware), add the best non-tabu point.
   usage: ktabu graph.txt sline.txt seed seconds outfile [startfile|-] [kstart] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
int n, *deg, **nb, **fb, *sl, nS;
int *inT, *nbT, *cs, *tabu_until, *Tlist, *pos, k;
long f;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static long dAdd(int u) {
    long d = 0; int nu = nbT[u]; if (nu > 1) d += nu - 1;
    for (int i = 0; i < deg[u]; i++) { int w = nb[u][i]; if (inT[w] && nbT[w] >= 1) d++; }
    if (cs[sl[u]] >= 1) d++;
    return d;
}
static long dRem(int v) {
    long d = 0; int nv = nbT[v]; if (nv > 1) d -= nv - 1;
    for (int i = 0; i < deg[v]; i++) { int w = nb[v][i]; if (inT[w] && nbT[w] >= 2) d--; }
    if (cs[sl[v]] >= 2) d--;
    return d;
}
static void addp(int v) {
    f += dAdd(v); inT[v] = 1; pos[v] = k; Tlist[k++] = v; cs[sl[v]]++;
    for (int i = 0; i < deg[v]; i++) nbT[nb[v][i]]++;
}
static void remp(int v) {
    f += dRem(v); inT[v] = 0; int p = pos[v]; Tlist[p] = Tlist[--k]; pos[Tlist[p]] = p; cs[sl[v]]--;
    for (int i = 0; i < deg[v]; i++) nbT[nb[v][i]]--;
}
int main(int argc, char **argv) {
    FILE *g = fopen(argv[1], "r"); if (fscanf(g, "%d", &n) != 1) return 1;
    deg = malloc(n * sizeof(int)); nb = malloc(n * sizeof(int *)); fb = malloc(n * sizeof(int *));
    for (int i = 0; i < n; i++) { if (fscanf(g, "%d", &deg[i]) != 1) return 1; nb[i] = malloc(deg[i] * sizeof(int)); fb[i] = malloc(deg[i] * sizeof(int));
        for (int j = 0; j < deg[i]; j++) if (fscanf(g, "%d %d", &nb[i][j], &fb[i][j]) != 2) return 1; }
    fclose(g);
    sl = malloc(n * sizeof(int)); FILE *s = fopen(argv[2], "r"); nS = 0;
    for (int i = 0; i < n; i++) { if (fscanf(s, "%d", &sl[i]) != 1) return 1; if (sl[i] + 1 > nS) nS = sl[i] + 1; } fclose(s);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[4]); const char *outf = argv[5];
    inT = calloc(n, sizeof(int)); nbT = calloc(n, sizeof(int)); cs = calloc(nS, sizeof(int)); tabu_until = calloc(n, sizeof(int));
    Tlist = malloc(n * sizeof(int)); pos = malloc(n * sizeof(int)); k = 0; f = 0;
    long it = 0; int best = 0;
    /* optional start set */
    if (argc > 6 && strcmp(argv[6], "-") != 0) {
        FILE *st = fopen(argv[6], "r"); int v;
        while (fscanf(st, "%d", &v) == 1) if (!inT[v] && dAdd(v) == 0) addp(v);
        fclose(st);
    }
    /* greedy fill to a feasible set */
    { int *perm = malloc(n * sizeof(int)); for (int i = 0; i < n; i++) perm[i] = i;
      for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
      for (int i = 0; i < n; i++) { int v = perm[i]; if (!inT[v] && dAdd(v) == 0) addp(v); } free(perm); }
    if (f == 0) { best = k; }
    int *cand = malloc(n * sizeof(int)); clock_t t0 = clock();
    int tt = 7;
    while (1) {
        if (f == 0) {
            if (k > best) { best = k;
                FILE *o = fopen(outf, "w"); fprintf(o, "%d\n", best); for (int i = 0; i < k; i++) fprintf(o, "%d\n", Tlist[i]); fclose(o);
                printf("size %d it %ld t %.1f\n", best, it, (double)(clock() - t0) / CLOCKS_PER_SEC); fflush(stdout); }
            /* raise k: add the best non-tabu point */
            long bd = 1L << 40; int bu = -1, cnt = 0;
            for (int u = 0; u < n; u++) if (!inT[u]) { long d = dAdd(u); if (d < bd) { bd = d; bu = u; cnt = 1; } else if (d == bd && rnd() % (++cnt) == 0) bu = u; }
            if (bu < 0) break;
            addp(bu);
            continue;
        }
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        it++;
        /* remove: choose among conflicting T points the one with max removal gain (min dRem), random ties, not tabu-blocked */
        int v = -1; long bd = 1L << 40; int cnt = 0;
        for (int i = 0; i < k; i++) { int x = Tlist[i]; long d = dRem(x);
            if (d < bd) { bd = d; v = x; cnt = 1; } else if (d == bd && rnd() % (++cnt) == 0) v = x; }
        if (rnd() % 100 < 10) v = Tlist[rnd() % k];   /* noise */
        remp(v); tabu_until[v] = it + tt + rnd() % 10;
        /* add: best non-tabu u (aspiration if it reaches f==0 would be nice; not needed) */
        int u = -1; bd = 1L << 40; cnt = 0;
        for (int x = 0; x < n; x++) { if (inT[x] || x == v) continue; if (tabu_until[x] > it) continue;
            long d = dAdd(x); if (d < bd) { bd = d; u = x; cnt = 1; } else if (d == bd && rnd() % (++cnt) == 0) u = x; }
        if (u < 0) u = v;
        addp(u); tabu_until[u] = it + 2;   /* small tabu on re-removing u is implicit via tabu of removed points */
    }
    printf("best %d iters %ld\n", best, it);
    return 0;
}
