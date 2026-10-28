/* rtabu.c: fixed-size tabu search for large relaxed sets of a graph (job d5-relax).
   A relaxed set T is a vertex set in which every vertex has at most one neighbour in T (the induced subgraph is a
   matching plus isolated vertices).  With the collinearity graph of W(q) this is a relaxed freed set of lines of
   Q(4,q) (D5_QUADRANGLE.md, section 7).  Option S adds the old condition "no collinear pair on a line of the regular
   spread", i.e. at most one point of T per spread line, so the two versions can be compared.
   penalty f = sum_{v in T} max(0, nbT[v] - 1)  [+ sum_s max(0, cs[s] - 1) with S]
   When f = 0 the set is recorded and k is raised by one (best add).  Otherwise one swap: remove the vertex of T whose
   removal lowers f most, then add the outside vertex that raises f least (both tabu-aware, random ties); random
   perturbation after a long stall.
   usage: rtabu ADJ seconds seed out [-S SPREADFILE] [-k kstart] [-i STARTSET] [-t target]
   ADJ: n, then per vertex: degree, neighbours.  out: size, then the vertices. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n, *deg, **nb, *sl = 0, nS = 0;
static int *inT, *nbT, *c1, *c2, *cs, *tabu, *Tl, *pos, k;
static long f;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }

static inline long dAdd(int u) {
    long d = (nbT[u] > 1 ? nbT[u] - 1 : 0) + c1[u];
    if (sl && cs[sl[u]] >= 1) d++;
    return d;
}
static inline long dRem(int v) {
    long d = -(nbT[v] > 1 ? nbT[v] - 1 : 0) - c2[v];
    if (sl && cs[sl[v]] >= 2) d--;
    return d;
}
static void addv(int v) {
    f += dAdd(v);
    for (int i = 0; i < deg[v]; i++) {
        int w = nb[v][i]; nbT[w]++;
        if (inT[w]) {
            if (nbT[w] == 1) for (int j = 0; j < deg[w]; j++) c1[nb[w][j]]++;
            else if (nbT[w] == 2) for (int j = 0; j < deg[w]; j++) c2[nb[w][j]]++;
        }
    }
    if (nbT[v] >= 1) for (int j = 0; j < deg[v]; j++) c1[nb[v][j]]++;
    if (nbT[v] >= 2) for (int j = 0; j < deg[v]; j++) c2[nb[v][j]]++;
    inT[v] = 1; pos[v] = k; Tl[k++] = v; if (sl) cs[sl[v]]++;
}
static void remv(int v) {
    f += dRem(v);
    if (nbT[v] >= 1) for (int j = 0; j < deg[v]; j++) c1[nb[v][j]]--;
    if (nbT[v] >= 2) for (int j = 0; j < deg[v]; j++) c2[nb[v][j]]--;
    inT[v] = 0; int p = pos[v]; Tl[p] = Tl[--k]; pos[Tl[p]] = p; if (sl) cs[sl[v]]--;
    for (int i = 0; i < deg[v]; i++) {
        int w = nb[v][i];
        if (inT[w]) {
            if (nbT[w] == 1) for (int j = 0; j < deg[w]; j++) c1[nb[w][j]]--;
            else if (nbT[w] == 2) for (int j = 0; j < deg[w]; j++) c2[nb[w][j]]--;
        }
        nbT[w]--;
    }
}
static long recompute(void) {
    long g = 0;
    for (int i = 0; i < k; i++) { int v = Tl[i]; if (nbT[v] > 1) g += nbT[v] - 1; }
    if (sl) for (int s = 0; s < nS; s++) if (cs[s] > 1) g += cs[s] - 1;
    return g;
}
static void save(const char *fn) {
    FILE *o = fopen(fn, "w"); fprintf(o, "%d\n", k);
    for (int i = 0; i < k; i++) fprintf(o, "%d\n", Tl[i]);
    fclose(o);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: rtabu ADJ seconds seed out [-S spread] [-k kstart] [-i start] [-t target]\n"); return 1; }
    FILE *g = fopen(argv[1], "r"); if (!g || fscanf(g, "%d", &n) != 1) return 1;
    deg = malloc(n * sizeof(int)); nb = malloc(n * sizeof(int *));
    for (int i = 0; i < n; i++) {
        if (fscanf(g, "%d", &deg[i]) != 1) return 1; nb[i] = malloc(deg[i] * sizeof(int));
        for (int j = 0; j < deg[i]; j++) if (fscanf(g, "%d", &nb[i][j]) != 1) return 1;
    }
    fclose(g);
    double secs = atof(argv[2]); rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();
    const char *outf = argv[4]; int kstart = 0, target = 1 << 30; const char *startf = 0;
    for (int a = 5; a + 1 < argc; a += 2) {
        if (!strcmp(argv[a], "-S")) {
            sl = malloc(n * sizeof(int)); FILE *s = fopen(argv[a + 1], "r");
            for (int i = 0; i < n; i++) { if (fscanf(s, "%d", &sl[i]) != 1) return 1; if (sl[i] + 1 > nS) nS = sl[i] + 1; }
            fclose(s);
        } else if (!strcmp(argv[a], "-k")) kstart = atoi(argv[a + 1]);
        else if (!strcmp(argv[a], "-i")) startf = argv[a + 1];
        else if (!strcmp(argv[a], "-t")) target = atoi(argv[a + 1]);
    }
    inT = calloc(n, sizeof(int)); nbT = calloc(n, sizeof(int)); c1 = calloc(n, sizeof(int)); c2 = calloc(n, sizeof(int));
    cs = calloc(nS + 1, sizeof(int)); tabu = calloc(n, sizeof(int)); Tl = malloc(n * sizeof(int)); pos = malloc(n * sizeof(int));
    k = 0; f = 0;
    if (startf) {
        FILE *st = fopen(startf, "r"); int m, v;
        if (fscanf(st, "%d", &m) == 1) while (fscanf(st, "%d", &v) == 1) if (!inT[v]) addv(v);
        fclose(st);
    }
    { /* greedy fill with zero-cost additions */
        int *perm = malloc(n * sizeof(int)); for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        if (f == 0) for (int i = 0; i < n; i++) { int v = perm[i]; if (!inT[v] && dAdd(v) == 0) addv(v); }
        free(perm);
    }
    int best = 0;
    if (f == 0) { best = k; save(outf); }
    while (k < kstart) { /* grow to kstart with best additions */
        int bu = -1; long bd = 1L << 40; int ties = 0;
        for (int u = 0; u < n; u++) if (!inT[u]) { long d = dAdd(u); if (d < bd) { bd = d; bu = u; ties = 1; } else if (d == bd && rnd() % (++ties) == 0) bu = u; }
        addv(bu);
    }
    clock_t t0 = clock(); long it = 0, lastimp = 0; long bestf = f;
    int *cand = malloc(n * sizeof(int));
    while (1) {
        it++;
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        if (f == 0) {
            if (k > best) {
                best = k; save(outf); lastimp = it;
                fprintf(stderr, "size %d at it %ld, %.1f s\n", best, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
                if (best >= target) break;
            }
            /* raise k: best addition */
            long bd = 1L << 40; int nc = 0;
            for (int u = 0; u < n; u++) if (!inT[u]) { long d = dAdd(u); if (d < bd) { bd = d; nc = 0; } if (d == bd) cand[nc++] = u; }
            addv(cand[rnd() % nc]); bestf = f;
            continue;
        }
        /* remove: largest decrease, non-tabu */
        long bd = 1L << 40; int nc = 0;
        for (int i = 0; i < k; i++) {
            int v = Tl[i]; if (tabu[v] > it) continue;
            long d = dRem(v); if (d < bd) { bd = d; nc = 0; } if (d == bd) cand[nc++] = v;
        }
        if (nc == 0) { int v = Tl[rnd() % k]; cand[0] = v; nc = 1; }
        int v = cand[rnd() % nc]; remv(v); tabu[v] = it + 7 + rnd() % 10;
        /* add: smallest increase, non-tabu (aspiration if it reaches 0) */
        bd = 1L << 40; nc = 0;
        for (int u = 0; u < n; u++) {
            if (inT[u] || u == v) continue;
            long d = dAdd(u);
            if (tabu[u] > it && f + d != 0) continue;
            if (d < bd) { bd = d; nc = 0; } if (d == bd) cand[nc++] = u;
        }
        int u = cand[rnd() % nc]; addv(u); tabu[u] = it + 3 + rnd() % 4;
        if (f < bestf) { bestf = f; lastimp = it; }
        if (it - lastimp > 200000) { /* perturb: random swaps */
            for (int r = 0; r < 3 + (int)(rnd() % 5); r++) {
                int vv = Tl[rnd() % k]; remv(vv); int uu; do uu = rnd() % n; while (inT[uu] || uu == vv); addv(uu);
            }
            lastimp = it; bestf = f;
        }
    }
    if (recompute() != f) fprintf(stderr, "INTERNAL: penalty drift %ld vs %ld\n", recompute(), f);
    printf("best %d  (iterations %ld, %.1f s)\n", best, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
