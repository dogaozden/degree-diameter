/* ncol_ils.c: large sets of pairwise NON-COLLINEAR points of H(q) (at most one point on every line), iterated local
   search in the style of Andrade-Resende-Werneck for maximum independent sets in the collinearity graph.
   (1,k)-swaps: remove x, insert one 1-tight point from every line through x that has one (points on different lines
   through x are never collinear: girth 12).  Perturbation: force-insert random points, then local search.
   usage: ncol_ils HEXFILE seconds seed [SEEDFILE] > out.txt   (writes the best set, one point index per line)
   card c2 (round 5): optional SEEDFILE (point indices, whitespace separated) is inserted first, when independent. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int q, N, Q1; static int32_t *lp, *pl;
static int *occ, *tight, *inS, *Slist, *Spos, nS;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void ins(int v) { inS[v] = 1; Spos[v] = nS; Slist[nS++] = v;
    for (int k = 0; k < Q1; k++) { int l = pl[(size_t)v * Q1 + k]; occ[l] = v; for (int t = 0; t < Q1; t++) { int u = lp[(size_t)l * Q1 + t]; if (u != v) tight[u]++; } } }
static void del(int v) { inS[v] = 0; int p = Spos[v], w = Slist[--nS]; Slist[p] = w; Spos[w] = p;
    for (int k = 0; k < Q1; k++) { int l = pl[(size_t)v * Q1 + k]; occ[l] = -1; for (int t = 0; t < Q1; t++) { int u = lp[(size_t)l * Q1 + t]; if (u != v) tight[u]--; } } }
static int try_swap(int x) {   /* (1,k)-swap at x; returns gain inserted - 1 if done, else 0 */
    int cand[32], nc = 0;
    for (int k = 0; k < Q1; k++) { int l = pl[(size_t)x * Q1 + k]; int c0 = -1, cnt = 0;
        for (int t = 0; t < Q1; t++) { int u = lp[(size_t)l * Q1 + t]; if (u != x && tight[u] == 1) { cnt++; if (rnd() % cnt == 0) c0 = u; } }
        if (c0 >= 0) cand[nc++] = c0; }
    if (nc < 2) return 0;
    del(x); int got = 0; for (int i = 0; i < nc; i++) if (tight[cand[i]] == 0) { ins(cand[i]); got++; }
    return got - 1;
}
static void local_search(void) {
    int improved = 1;
    while (improved) { improved = 0;
        for (int v = 0; v < N; v++) if (!inS[v] && tight[v] == 0) { ins(v); improved = 1; }
        for (int i = 0; i < nS; i++) { int x = Slist[i]; if (try_swap(x) > 0) { improved = 1; break; } }
    }
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1; q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    lp = malloc(4L * N * Q1); if (fread(lp, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    pl = malloc(4L * N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = lp[(size_t)l * Q1 + k]; pl[(size_t)p * Q1 + c[p]++] = l; }
    double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 2654435761ULL; for (int i = 0; i < 20; i++) rnd();
    const char *seedf = argc > 4 ? argv[4] : NULL;
    occ = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) occ[i] = -1;
    tight = calloc(N, sizeof(int)); inS = calloc(N, sizeof(int)); Slist = malloc(sizeof(int) * N); Spos = malloc(sizeof(int) * N); nS = 0;
    int *perm = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    if (seedf) { FILE *g = fopen(seedf, "r"); int v, ns = 0, sk = 0; if (!g) { fprintf(stderr, "no seed\n"); return 1; }
        while (fscanf(g, "%d", &v) == 1) { if (v < 0 || v >= N) continue; if (!inS[v] && tight[v] == 0) { ins(v); ns++; } else sk++; }
        fclose(g); fprintf(stderr, "seed: inserted %d, skipped %d\n", ns, sk); }
    for (int i = 0; i < N; i++) if (!inS[perm[i]] && tight[perm[i]] == 0) ins(perm[i]);
    local_search();
    int best = nS; int *bestS = malloc(sizeof(int) * N); memcpy(bestS, Slist, sizeof(int) * nS);
    fprintf(stderr, "greedy + LS: %d (bound %d)\n", nS, N / Q1);
    clock_t t0 = clock(); long it = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        /* perturb: force-insert 1 (sometimes 2) random non-solution points with small tightness */
        int kk = (rnd() % 4 == 0) ? 2 : 1;
        for (int z = 0; z < kk; z++) {
            int v; do { v = rnd() % N; } while (inS[v] || tight[v] > 2);
            for (int k = 0; k < Q1; k++) { int l = pl[(size_t)v * Q1 + k]; if (occ[l] >= 0) del(occ[l]); }
            ins(v);
        }
        local_search();
        if (nS > best) { best = nS; memcpy(bestS, Slist, sizeof(int) * nS); fprintf(stderr, "it %ld: %d\n", it, best); }
        else if (nS < best - 3 && rnd() % 2) { /* go back to the best */
            while (nS) del(Slist[nS - 1]); for (int i = 0; i < best; i++) ins(bestS[i]); }
    }
    for (int i = 0; i < best; i++) printf("%d\n", bestS[i]);
    fprintf(stderr, "best %d after %ld iterations\n", best, it);
    return 0;
}
