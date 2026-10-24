/* spreadpack.c: type-2 unit packings from a Hermitian spread. Session cell-14-7 (second), 2026-10-24.
   The hexagon lines of H(q) inside an elliptic hyperplane section E = Q(6,q) ∩ v^perp (here v = e0 + c e4, section
   X4 = -c X0) form a spread of q^3+1 pairwise opposite lines partitioning the points of E (checked below). Flags
   (p, spread line through p) then never conflict on the line side (line zones lie in the disjoint 2-balls of the spread
   lines), and they do not conflict on the point side when the points are pairwise opposite, i.e. pairwise
   non-orthogonal on the quadric (d(x,y) <= 4 iff B(x,y) = 0). So a packing is a partial ovoid inside E: found here by
   an iterated local search for independent sets in the orthogonality graph on the points of E (plateau swaps,
   (1,2)-swaps, perturbation). Then the gaps are filled with any flags whose zones are free.
   Usage: spreadpack GHFILE COORDFILE C SECONDS SEED OUTFLAGS     (C: X4 = -C*X0, -C*X0^2 - X3^2 must be anisotropic)
   Compile: gcc -O3 -march=native -o spreadpack spreadpack.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int P, q, Q1;
static int32_t *LP, *PL;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static int (*X)[7];
static inline int Bf(int a, int b) { const int *x = X[a], *y = X[b];
    long s = (long)x[0] * y[4] + (long)x[4] * y[0] + (long)x[1] * y[5] + (long)x[5] * y[1] + (long)x[2] * y[6] + (long)x[6] * y[2] - 2L * x[3] * y[3];
    s %= q; return (int)(s < 0 ? s + q : s); }
static int zoneP(int p, int l, int *out) { int c = 0; out[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue; for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) out[c++] = w; } }
    return c; }
static int zoneL(int p, int l, int *out) { int c = 0; out[c++] = l;
    for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (x == p) continue; for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) out[c++] = K; } }
    return c; }

static void addv(int v, int *inS, int *pos, int *S, int *ns, int *deg, int **adj, int *tau) {
    inS[v] = 1; pos[v] = *ns; S[(*ns)++] = v; for (int e = 0; e < deg[v]; e++) tau[adj[v][e]]++; }
static void remv(int v, int *inS, int *pos, int *S, int *ns, int *deg, int **adj, int *tau) {
    inS[v] = 0; int p = pos[v]; S[p] = S[--(*ns)]; pos[S[p]] = p; for (int e = 0; e < deg[v]; e++) tau[adj[v][e]]--; }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: spreadpack GHFILE COORDFILE C SECONDS SEED OUTFLAGS\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    X = malloc(sizeof(int) * 7 * P); f = fopen(argv[2], "r");
    for (int i = 0; i < P; i++) for (int k = 0; k < 7; k++) if (fscanf(f, "%d", &X[i][k]) != 1) { fprintf(stderr, "bad coords\n"); return 2; }
    fclose(f);
    int C = atoi(argv[3]); double secs = atof(argv[4]); rs ^= strtoull(argv[5], 0, 10) * 0x2545F4914F6CDD1DULL;
    /* points of E: X4 + C X0 = 0 */
    char *inE = calloc(P, 1); int nE = 0; int *Ep = malloc(sizeof(int) * P), *Eidx = malloc(sizeof(int) * P);
    for (int i = 0; i < P; i++) if ((X[i][4] + (long)C * X[i][0]) % q == 0) { inE[i] = 1; Eidx[i] = nE; Ep[nE++] = i; } else Eidx[i] = -1;
    /* spread: hexagon lines inside E */
    int nS = 0; int *spreadOf = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) spreadOf[i] = -1;
    int *Sl = malloc(sizeof(int) * P); long badcover = 0;
    for (int l = 0; l < P; l++) { int all = 1; for (int k = 0; k < Q1; k++) if (!inE[LP[l * Q1 + k]]) { all = 0; break; } if (!all) continue;
        Sl[nS++] = l; for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; if (spreadOf[p] >= 0) badcover++; spreadOf[p] = l; } }
    long uncovered = 0; for (int i = 0; i < nE; i++) if (spreadOf[Ep[i]] < 0) uncovered++;
    fprintf(stderr, "E: %d points; spread: %d lines; points of E on 0 or >1 spread lines: %ld, %ld\n", nE, nS, uncovered, badcover);
    if (uncovered || badcover) { fprintf(stderr, "not a spread of E\n"); return 1; }
    /* pairwise opposite spread lines? sample check via distance: two lines are at distance <= 4 iff a point of one is
       orthogonal to ... check exactly on a sample: lines l, l' opposite iff no point of l is collinear with a point of l' and
       no point of l is on l'; we test B on a 2x2 Gram matrix: opposite iff det != 0 */
    long nonopp = 0, tests = 0;
    for (int t = 0; t < 20000; t++) { int a = Sl[rndi(nS)], b = Sl[rndi(nS)]; if (a == b) continue; tests++;
        int x1 = LP[a * Q1], x2 = LP[a * Q1 + 1], y1 = LP[b * Q1], y2 = LP[b * Q1 + 1];
        long det = (long)Bf(x1, y1) * Bf(x2, y2) - (long)Bf(x1, y2) * Bf(x2, y1); if (det % q == 0) nonopp++; }
    fprintf(stderr, "spread lines: %ld of %ld sampled pairs not opposite (Gram test)\n", nonopp, tests);
    /* orthogonality graph on E: adjacency lists */
    int *deg = calloc(nE, sizeof(int)); int **adj = malloc(sizeof(int *) * nE);
    { int *tmp = malloc(sizeof(int) * nE);
      for (int i = 0; i < nE; i++) { int c = 0; for (int j = 0; j < nE; j++) if (j != i && Bf(Ep[i], Ep[j]) == 0) tmp[c++] = j;
          deg[i] = c; adj[i] = malloc(sizeof(int) * c); memcpy(adj[i], tmp, sizeof(int) * c); }
      free(tmp); }
    fprintf(stderr, "orthogonality graph on E: degree %d (first vertex)\n", deg[0]);
    if (getenv("DUMP")) {   /* DUMP=prefix: prefix.graph ("n m", then edges "i j", i<j, 0-based vertices of E) and
                               prefix.map (line i: hexagon point id of vertex i, its spread line id, its 7 coordinates) */
        char fn[512]; snprintf(fn, sizeof fn, "%s.graph", getenv("DUMP")); FILE *g = fopen(fn, "w"); long m2 = 0;
        for (int i = 0; i < nE; i++) m2 += deg[i]; fprintf(g, "%d %ld\n", nE, m2 / 2);
        for (int i = 0; i < nE; i++) for (int e = 0; e < deg[i]; e++) if (adj[i][e] > i) fprintf(g, "%d %d\n", i, adj[i][e]);
        fclose(g); snprintf(fn, sizeof fn, "%s.map", getenv("DUMP")); g = fopen(fn, "w");
        for (int i = 0; i < nE; i++) { int p = Ep[i]; fprintf(g, "%d %d", p, spreadOf[p]); for (int k = 0; k < 7; k++) fprintf(g, " %d", X[p][k]); fprintf(g, "\n"); }
        fclose(g); fprintf(stderr, "wrote %s.graph and .map\n", getenv("DUMP")); }
    /* iterated local search for a maximum independent set */
    int *inS = calloc(nE, sizeof(int)), *tau = calloc(nE, sizeof(int)), *S = malloc(sizeof(int) * nE), *pos = malloc(sizeof(int) * nE); int ns = 0;
    int *best = malloc(sizeof(int) * nE), nbest = 0;
    /* (functions, not macros: an argument like S[ns-1] must be evaluated once) */
    #define ADDV(v) addv((v), inS, pos, S, &ns, deg, adj, tau)
    #define REMV(v) remv((v), inS, pos, S, &ns, deg, adj, tau)
    int *order = malloc(sizeof(int) * nE); for (int i = 0; i < nE; i++) order[i] = i;
    for (int i = nE - 1; i > 0; i--) { int r = rndi(i + 1); int t = order[i]; order[i] = order[r]; order[r] = t; }
    for (int i = 0; i < nE; i++) { int v = order[i]; if (!inS[v] && tau[v] == 0) ADDV(v); }
    nbest = ns; memcpy(best, S, sizeof(int) * ns);
    fprintf(stderr, "greedy: %d\n", ns);
    clock_t c0 = clock(); long it = 0;
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < secs) {
        it++;
        /* add any free vertex */
        int v = rndi(nE);
        if (!inS[v] && tau[v] == 0) { ADDV(v); }
        else if (!inS[v] && tau[v] == 1) {   /* plateau swap: remove its unique neighbour in S */
            int u = -1; for (int e = 0; e < deg[v]; e++) if (inS[adj[v][e]]) { u = adj[v][e]; break; }
            REMV(u); ADDV(v);
            /* (1,2): try to add free vertices around u */
            for (int e = 0; e < deg[u]; e++) { int w = adj[u][e]; if (!inS[w] && tau[w] == 0) ADDV(w); }
        } else if (!inS[v] && tau[v] == 2 && rndi(50) == 0) {   /* occasional downhill move */
            for (int e = 0; e < deg[v]; e++) { int u = adj[v][e]; if (inS[u]) REMV(u); }
            ADDV(v);
        }
        if (ns > nbest) { nbest = ns; memcpy(best, S, sizeof(int) * ns); fprintf(stderr, "it %ld: %d\n", it, ns); }
        if (ns < nbest - 8) { while (ns) REMV(S[ns - 1]); for (int i = 0; i < nbest; i++) ADDV(best[i]); }
    }
    { long bad = 0; for (int i = 0; i < nbest; i++) for (int j = i + 1; j < nbest; j++) if (Bf(Ep[best[i]], Ep[best[j]]) == 0) bad++;
      fprintf(stderr, "partial ovoid in E: %d points (%ld iterations), orthogonal pairs inside: %ld\n", nbest, it, bad); }
    /* flags and gap filling */
    char *occP = calloc(P, 1), *occL = calloc(P, 1); int zp[512], zl[512]; long nfl = 0;
    f = fopen(argv[6], "w");
    for (int i = 0; i < nbest; i++) { int p = Ep[best[i]], l = spreadOf[p], n1 = zoneP(p, l, zp), n2 = zoneL(p, l, zl), ok = 1;
        for (int t = 0; t < n1; t++) if (occP[zp[t]]) ok = 0; for (int t = 0; t < n2; t++) if (occL[zl[t]]) ok = 0;
        if (!ok) { fprintf(stderr, "internal: conflict at %d\n", i); continue; }
        for (int t = 0; t < n1; t++) occP[zp[t]] = 1; for (int t = 0; t < n2; t++) occL[zl[t]] = 1; fprintf(f, "%d %d\n", p, l); nfl++; }
    long filled = 0;
    int *perm = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) perm[i] = i;
    for (int i = P - 1; i > 0; i--) { int r = rndi(i + 1); int t = perm[i]; perm[i] = perm[r]; perm[r] = t; }
    for (int ii = 0; ii < P; ii++) { int p = perm[ii]; if (occP[p]) continue;
        for (int a = 0; a < Q1; a++) { int l = PL[p * Q1 + a], n1 = zoneP(p, l, zp), n2 = zoneL(p, l, zl), ok = 1;
            for (int t = 0; t < n1 && ok; t++) if (occP[zp[t]]) ok = 0; for (int t = 0; t < n2 && ok; t++) if (occL[zl[t]]) ok = 0;
            if (!ok) continue;
            for (int t = 0; t < n1; t++) occP[zp[t]] = 1; for (int t = 0; t < n2; t++) occL[zl[t]] = 1;
            fprintf(f, "%d %d\n", p, l); nfl++; filled++; break; } }
    fclose(f);
    fprintf(stderr, "flags: %d from the spread + %ld filled = %ld\n", nbest, filled, nfl);
    return 0;
}
