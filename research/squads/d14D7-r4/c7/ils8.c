/* ils8.c: iterated local search for large partial ovoids of the elliptic section E: X4 = c*X0 + d*X3 of H(8)
   (GF(8) = GF(2)[t]/(t^3+t+1), characteristic 2), a port of research/cell147/units/spreadpack.c to GF(8).
   Points of E pairwise non-orthogonal (B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2 = 0 is the orthogonality) give
   flags (p, spread line through p) with disjoint zones, then greedy gap filling as in spreadpack.c.
   Usage: ils8 GHFILE COORDFILE C D SECONDS SEED OUTFLAGS [INITFLAGS]
   Output: OUTFLAGS lines "p l" (point id, line id, numbering of GHFILE). Compile: gcc -O3 -march=native -o ils8 ils8.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int P, q, Q1;
static int32_t *LP, *PL;
static int (*X)[7];
static int MUL[8][8];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static int gmul(int a, int b) {
    int r = 0;
    for (int i = 0; i < 3; i++) if ((b >> i) & 1) r ^= a << i;
    for (int bit = 4; bit >= 3; bit--) if ((r >> bit) & 1) r ^= 0xB << (bit - 3);
    return r;
}
static inline int Bf(int a, int b) {
    const int *x = X[a], *y = X[b];
    return MUL[x[0]][y[4]] ^ MUL[x[4]][y[0]] ^ MUL[x[1]][y[5]] ^ MUL[x[5]][y[1]] ^ MUL[x[2]][y[6]] ^ MUL[x[6]][y[2]];
}
static int zoneP(int p, int l, int *out) {
    int c = 0; out[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue;
        for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) out[c++] = w; } }
    return c;
}
static int zoneL(int p, int l, int *out) {
    int c = 0; out[c++] = l;
    for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (x == p) continue;
        for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) out[c++] = K; } }
    return c;
}

static int nE, *Ep, *Eidx, *deg, **adj, *tau, *S, *pos, ns;
static char *inS;
static void addv(int v) {
    inS[v] = 1; pos[v] = ns; S[ns++] = v;
    for (int e = 0; e < deg[v]; e++) tau[adj[v][e]]++;
}
static void remv(int v) {
    inS[v] = 0; int p = pos[v]; S[p] = S[--ns]; pos[S[p]] = p;
    for (int e = 0; e < deg[v]; e++) tau[adj[v][e]]--;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: ils8 GHFILE COORDFILE C D SECONDS SEED OUTFLAGS [INITFLAGS]\n"); return 2; }
    for (int a = 0; a < 8; a++) for (int b = 0; b < 8; b++) MUL[a][b] = gmul(a, b);
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d %d", &P, &q) != 2) { fprintf(stderr, "bad GH file\n"); return 2; }
    Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) { fprintf(stderr, "bad GH\n"); return 2; }
    fclose(f);
    { int *c = calloc(P, sizeof(int));
      for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; }
      free(c); }
    X = malloc(sizeof(int) * 7 * (size_t)P); f = fopen(argv[2], "r");
    for (int i = 0; i < P; i++) for (int k = 0; k < 7; k++) if (fscanf(f, "%d", &X[i][k]) != 1) { fprintf(stderr, "bad coords\n"); return 2; }
    fclose(f);
    int c = atoi(argv[3]), d = atoi(argv[4]);
    double secs = atof(argv[5]);
    rs ^= strtoull(argv[6], 0, 10) * 0x2545F4914F6CDD1DULL;
    for (int i = 0; i < 10; i++) rnd();
    /* points of E: X4 = c X0 + d X3 (GF(8), char 2) */
    Ep = malloc(sizeof(int) * P); Eidx = malloc(sizeof(int) * P); nE = 0;
    for (int i = 0; i < P; i++) {
        if (X[i][4] == (MUL[c][X[i][0]] ^ MUL[d][X[i][3]])) { Eidx[i] = nE; Ep[nE++] = i; } else Eidx[i] = -1;
    }
    /* hexagon lines inside E form the spread */
    int *spreadOf = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) spreadOf[i] = -1;
    int nS = 0; long badcover = 0;
    for (int l = 0; l < P; l++) {
        int all = 1; for (int k = 0; k < Q1; k++) if (Eidx[LP[l * Q1 + k]] < 0) { all = 0; break; }
        if (!all) continue;
        nS++;
        for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; if (spreadOf[p] >= 0) badcover++; spreadOf[p] = l; }
    }
    long uncovered = 0; for (int i = 0; i < nE; i++) if (spreadOf[Ep[i]] < 0) uncovered++;
    fprintf(stderr, "E: %d points; spread lines inside: %d; uncovered %ld, multiply covered %ld\n", nE, nS, uncovered, badcover);
    if (uncovered || badcover) { fprintf(stderr, "not a spread\n"); return 1; }
    /* orthogonality graph on E */
    deg = calloc(nE, sizeof(int)); adj = malloc(sizeof(int *) * nE);
    int *tmp = malloc(sizeof(int) * nE);
    for (int i = 0; i < nE; i++) {
        int cnt = 0;
        for (int j = 0; j < nE; j++) if (j != i && Bf(Ep[i], Ep[j]) == 0) tmp[cnt++] = j;
        deg[i] = cnt; adj[i] = malloc(sizeof(int) * (cnt ? cnt : 1)); memcpy(adj[i], tmp, sizeof(int) * cnt);
    }
    free(tmp);
    fprintf(stderr, "orthogonality graph on E: degree %d (first vertex)\n", deg[0]);
    /* ILS for a maximum independent set */
    inS = calloc(nE, 1); tau = calloc(nE, sizeof(int)); S = malloc(sizeof(int) * nE); pos = malloc(sizeof(int) * nE); ns = 0;
    int *best = malloc(sizeof(int) * nE), nbest = 0;
    int *order = malloc(sizeof(int) * nE);
    for (int i = 0; i < nE; i++) order[i] = i;
    for (int i = nE - 1; i > 0; i--) { int r = rndi(i + 1); int t = order[i]; order[i] = order[r]; order[r] = t; }
    if (argc > 8) {
        FILE *fi = fopen(argv[8], "r"); int a, b, nin = 0;
        while (fi && fscanf(fi, "%d %d", &a, &b) == 2) {
            if (a >= 0 && a < P && Eidx[a] >= 0 && !inS[Eidx[a]] && tau[Eidx[a]] == 0) { addv(Eidx[a]); nin++; } }
        if (fi) fclose(fi);
        fprintf(stderr, "INIT: %d points\n", nin);
    }
    for (int i = 0; i < nE; i++) { int v = order[i]; if (!inS[v] && tau[v] == 0) addv(v); }
    nbest = ns; memcpy(best, S, sizeof(int) * ns);
    fprintf(stderr, "greedy: %d\n", ns);
    int PERT = getenv("PERT") ? atoi(getenv("PERT")) : 0;      /* PERT=k: force a random vertex in with prob 1/k */
    int KDROP = getenv("KDROP") ? atoi(getenv("KDROP")) : 8;   /* restore the best when the size falls KDROP below it */
    clock_t c0 = clock(); long it = 0;
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < secs) {
        it++;
        if (PERT && rndi(PERT) == 0) {
            int w = rndi(nE);
            if (!inS[w]) { for (int e = 0; e < deg[w]; e++) { int u = adj[w][e]; if (inS[u]) remv(u); } addv(w); }
        }
        int v = rndi(nE);
        if (!inS[v] && tau[v] == 0) {
            addv(v);
        } else if (!inS[v] && tau[v] == 1) {       /* plateau swap, then refill around the removed vertex */
            int u = -1; for (int e = 0; e < deg[v]; e++) if (inS[adj[v][e]]) { u = adj[v][e]; break; }
            remv(u); addv(v);
            for (int e = 0; e < deg[u]; e++) { int w = adj[u][e]; if (!inS[w] && tau[w] == 0) addv(w); }
        } else if (!inS[v] && tau[v] == 2 && rndi(50) == 0) {  /* occasional downhill move */
            for (int e = 0; e < deg[v]; e++) { int u = adj[v][e]; if (inS[u]) remv(u); }
            addv(v);
        }
        if (ns > nbest) { nbest = ns; memcpy(best, S, sizeof(int) * ns); fprintf(stderr, "it %ld: %d (%.1fs)\n", it, ns, (double)(clock() - c0) / CLOCKS_PER_SEC); }
        if (ns < nbest - KDROP) { while (ns) remv(S[ns - 1]); for (int i = 0; i < nbest; i++) addv(best[i]); }
    }
    { long bad = 0; for (int i = 0; i < nbest; i++) for (int j = i + 1; j < nbest; j++) if (Bf(Ep[best[i]], Ep[best[j]]) == 0) bad++;
      fprintf(stderr, "partial ovoid in E: %d points (%ld iterations), orthogonal pairs inside: %ld\n", nbest, it, bad); }
    /* flags: the partial ovoid, then greedy gap filling with free zones */
    char *occP = calloc(P, 1), *occL = calloc(P, 1); int zp[512], zl[512]; long nfl = 0;
    FILE *fo = fopen(argv[7], "w");
    for (int i = 0; i < nbest; i++) {
        int p = Ep[best[i]], l = spreadOf[p], n1 = zoneP(p, l, zp), n2 = zoneL(p, l, zl), ok = 1;
        for (int t = 0; t < n1; t++) if (occP[zp[t]]) ok = 0;
        for (int t = 0; t < n2; t++) if (occL[zl[t]]) ok = 0;
        if (!ok) { fprintf(stderr, "internal: conflict at %d\n", i); continue; }
        for (int t = 0; t < n1; t++) occP[zp[t]] = 1;
        for (int t = 0; t < n2; t++) occL[zl[t]] = 1;
        fprintf(fo, "%d %d\n", p, l); nfl++;
    }
    long filled = 0, ovoidFlags = nfl;
    int *perm = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) perm[i] = i;
    for (int i = P - 1; i > 0; i--) { int r = rndi(i + 1); int t = perm[i]; perm[i] = perm[r]; perm[r] = t; }
    for (int ii = 0; ii < P; ii++) {
        int p = perm[ii]; if (occP[p]) continue;
        for (int a = 0; a < Q1; a++) {
            int l = PL[p * Q1 + a], n1 = zoneP(p, l, zp), n2 = zoneL(p, l, zl), ok = 1;
            for (int t = 0; t < n1 && ok; t++) if (occP[zp[t]]) ok = 0;
            for (int t = 0; t < n2 && ok; t++) if (occL[zl[t]]) ok = 0;
            if (!ok) continue;
            for (int t = 0; t < n1; t++) occP[zp[t]] = 1;
            for (int t = 0; t < n2; t++) occL[zl[t]] = 1;
            fprintf(fo, "%d %d\n", p, l); nfl++; filled++; break;
        }
    }
    fclose(fo);
    fprintf(stderr, "flags: %ld from the partial ovoid + %ld gap-filled = %ld\n", ovoidFlags, filled, nfl);
    printf("%ld\n", nfl);
    return 0;
}
