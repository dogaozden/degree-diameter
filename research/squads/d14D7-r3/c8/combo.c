/* combo.c: card c8 (round 3, wildcard) for the (14,7) flags problem.
   Candidate flags come from several elliptic sections E_C = Q(6,q) ∩ {X4 + C X0 = 0} of H(q): each point of E_C is
   paired with the hexagon line through it that lies inside E_C (its spread line; used only when the lines inside E_C
   form a spread). Plus the flags given in INFLAGS. A packing is a set of candidates whose point zones and line zones
   are pairwise disjoint (zones exactly as in pack.c, the scorer's criterion). Two candidates conflict iff a zone
   element is shared, so the packing is an independent set in the zone-conflict graph, which is searched by an
   iterated local search: greedy start, plateau swaps (a candidate with exactly one conflicting member replaces it,
   then the freed candidates are added), 2-conflict forced insertions with refill (1 in 50), restart from the best
   when 4 or more below it. conf[k] = number of occupied zone elements of candidate k (0 = free).
   Usage: combo GHFILE COORDFILE CLIST SECONDS SEED OUTFLAGS [INFLAGS]
   CLIST: comma-separated C values, e.g. 1,3,4,5,9. Compile: gcc -O2 -march=native -o combo combo.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int P, q, Q1, ZN;
static int32_t *LP, *PL;
static int (*X)[7];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static int zoneP(int p, int l, int *out) { int c = 0; out[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue; for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) out[c++] = w; } }
    return c; }
static int zoneL(int p, int l, int *out) { int c = 0; out[c++] = l;
    for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (x == p) continue; for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) out[c++] = K; } }
    return c; }

static int nc = 0, cap = 0;
static int *cp, *cl;                     /* candidate flag (point, line) */
static int32_t *zP, *zL;                 /* zones, nc x ZN */
static int *offP, *offL, *invP, *invL;   /* inverted index: element -> candidates whose zone contains it */
static int *ownP, *ownL;                 /* member owning a zone element, or -1 */
static int *conf;                        /* number of occupied zone elements of a candidate */
static int *memList, *memPos, nmem = 0;  /* current packing */
static int *bestSet, nbest = 0;
static char *inS;
static const char *OUTFN;
static void writeOut(void) { FILE *f = fopen(OUTFN, "w"); if (!f) return; for (int i = 0; i < nbest; i++) fprintf(f, "%d %d\n", cp[bestSet[i]], cl[bestSet[i]]); fclose(f); }

static void pushc(int p, int l) {
    if (nc == cap) { cap = cap ? 2 * cap : 1 << 16; cp = realloc(cp, sizeof(int) * cap); cl = realloc(cl, sizeof(int) * cap); }
    cp[nc] = p; cl[nc] = l; nc++; }

static void addc(int k) {   /* precondition: conf[k] == 0 */
    inS[k] = 1; memPos[k] = nmem; memList[nmem++] = k;
    const int32_t *z = zP + (size_t)k * ZN;
    for (int i = 0; i < ZN; i++) { int x = z[i]; ownP[x] = k; for (int j = offP[x]; j < offP[x + 1]; j++) conf[invP[j]]++; }
    z = zL + (size_t)k * ZN;
    for (int i = 0; i < ZN; i++) { int x = z[i]; ownL[x] = k; for (int j = offL[x]; j < offL[x + 1]; j++) conf[invL[j]]++; }
}
static void remc(int k) {
    inS[k] = 0; int pos = memPos[k]; int last = memList[--nmem]; memList[pos] = last; memPos[last] = pos;
    const int32_t *z = zP + (size_t)k * ZN;
    for (int i = 0; i < ZN; i++) { int x = z[i]; ownP[x] = -1; for (int j = offP[x]; j < offP[x + 1]; j++) conf[invP[j]]--; }
    z = zL + (size_t)k * ZN;
    for (int i = 0; i < ZN; i++) { int x = z[i]; ownL[x] = -1; for (int j = offL[x]; j < offL[x + 1]; j++) conf[invL[j]]--; }
}
/* after removing k: add every candidate (other than k) whose conflicts are now gone */
static void refill(int k) {
    const int32_t *z = zP + (size_t)k * ZN;
    for (int i = 0; i < ZN; i++) { int x = z[i]; for (int j = offP[x]; j < offP[x + 1]; j++) { int w = invP[j]; if (w != k && !inS[w] && conf[w] == 0) addc(w); } }
    z = zL + (size_t)k * ZN;
    for (int i = 0; i < ZN; i++) { int x = z[i]; for (int j = offL[x]; j < offL[x + 1]; j++) { int w = invL[j]; if (w != k && !inS[w] && conf[w] == 0) addc(w); } }
}
static void restore_best(void) {
    while (nmem) remc(memList[nmem - 1]);
    for (int i = 0; i < nbest; i++) addc(bestSet[i]);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: combo GHFILE COORDFILE CLIST SECONDS SEED OUTFLAGS [INFLAGS]\n"); return 2; }
    OUTFN = argv[6];
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1; ZN = q * q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    X = malloc(sizeof(int) * 7 * (size_t)P); f = fopen(argv[2], "r");
    for (int i = 0; i < P; i++) for (int k = 0; k < 7; k++) if (fscanf(f, "%d", &X[i][k]) != 1) { fprintf(stderr, "bad coords\n"); return 2; }
    fclose(f);

    int Cs[32], nCs = 0;
    { char *s = strdup(argv[3]); for (char *t = strtok(s, ","); t && nCs < 32; t = strtok(NULL, ",")) Cs[nCs++] = atoi(t); }
    double secs = atof(argv[4]); rs ^= strtoull(argv[5], 0, 10) * 0x2545F4914F6CDD1DULL;
    for (int i = 0; i < 10; i++) rnd();

    /* candidates from the elliptic sections */
    char *inE = malloc(P); int *spreadOf = malloc(sizeof(int) * P);
    for (int ci = 0; ci < nCs; ci++) {
        int C = Cs[ci], nE = 0;
        for (int p = 0; p < P; p++) { inE[p] = ((X[p][4] + C * X[p][0]) % q == 0); nE += inE[p]; spreadOf[p] = -1; }
        int ok = 1, nS = 0;
        for (int l = 0; l < P && ok; l++) {
            int all = 1; for (int k = 0; k < Q1; k++) if (!inE[LP[l * Q1 + k]]) { all = 0; break; }
            if (!all) continue;
            nS++;
            for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; if (spreadOf[p] >= 0) ok = 0; spreadOf[p] = l; }
        }
        for (int p = 0; p < P && ok; p++) if (inE[p] && spreadOf[p] < 0) ok = 0;
        fprintf(stderr, "C=%d: |E|=%d, hexagon lines inside=%d, spread=%s\n", C, nE, nS, ok ? "yes" : "no");
        if (!ok) continue;
        for (int p = 0; p < P; p++) if (inE[p]) pushc(p, spreadOf[p]);
    }
    int nin = 0; int *inIdx = malloc(sizeof(int) * 100000);
    if (argc > 7) { FILE *g = fopen(argv[7], "r"); int a, b; while (g && fscanf(g, "%d %d", &a, &b) == 2 && nin < 100000) { pushc(a, b); inIdx[nin++] = nc - 1; } if (g) fclose(g); }
    fprintf(stderr, "candidates: %d (input flags %d)\n", nc, nin);

    /* zones and inverted index */
    zP = malloc(sizeof(int32_t) * (size_t)nc * ZN); zL = malloc(sizeof(int32_t) * (size_t)nc * ZN);
    int *tmp = malloc(sizeof(int) * (ZN + 8));
    for (int k = 0; k < nc; k++) {
        if (zoneP(cp[k], cl[k], tmp) != ZN || zoneL(cp[k], cl[k], tmp) != ZN) { fprintf(stderr, "candidate %d is not an incident flag\n", k); return 2; }
        zoneP(cp[k], cl[k], tmp); for (int i = 0; i < ZN; i++) zP[(size_t)k * ZN + i] = tmp[i];
        zoneL(cp[k], cl[k], tmp); for (int i = 0; i < ZN; i++) zL[(size_t)k * ZN + i] = tmp[i];
    }
    offP = calloc(P + 1, sizeof(int)); offL = calloc(P + 1, sizeof(int));
    for (size_t i = 0; i < (size_t)nc * ZN; i++) { offP[zP[i] + 1]++; offL[zL[i] + 1]++; }
    for (int x = 0; x < P; x++) { offP[x + 1] += offP[x]; offL[x + 1] += offL[x]; }
    invP = malloc(sizeof(int) * (size_t)nc * ZN); invL = malloc(sizeof(int) * (size_t)nc * ZN);
    { int *cur = malloc(sizeof(int) * P);
      memcpy(cur, offP, sizeof(int) * P); for (int k = 0; k < nc; k++) for (int i = 0; i < ZN; i++) { int x = zP[(size_t)k * ZN + i]; invP[cur[x]++] = k; }
      memcpy(cur, offL, sizeof(int) * P); for (int k = 0; k < nc; k++) for (int i = 0; i < ZN; i++) { int x = zL[(size_t)k * ZN + i]; invL[cur[x]++] = k; }
      free(cur); }
    ownP = malloc(sizeof(int) * P); ownL = malloc(sizeof(int) * P);
    for (int x = 0; x < P; x++) { ownP[x] = -1; ownL[x] = -1; }
    conf = calloc(nc, sizeof(int)); inS = calloc(nc, 1); memList = malloc(sizeof(int) * nc); memPos = malloc(sizeof(int) * nc);
    bestSet = malloc(sizeof(int) * nc);

    /* start: input flags, then greedy over the candidates in random order */
    for (int i = 0; i < nin; i++) { int k = inIdx[i]; if (!inS[k] && conf[k] == 0) addc(k); else fprintf(stderr, "input flag %d not addable\n", i); }
    fprintf(stderr, "input packing: %d\n", nmem);
    { int *perm = malloc(sizeof(int) * nc); for (int k = 0; k < nc; k++) perm[k] = k;
      for (int i = nc - 1; i > 0; i--) { int r = rndi(i + 1); int t = perm[i]; perm[i] = perm[r]; perm[r] = t; }
      for (int i = 0; i < nc; i++) { int k = perm[i]; if (!inS[k] && conf[k] == 0) addc(k); }
      free(perm); }
    nbest = nmem; memcpy(bestSet, memList, sizeof(int) * nmem);
    fprintf(stderr, "greedy packing: %d\n", nbest);
    writeOut();

    /* iterated local search; candidates with few occupied zone elements are sampled */
    const int CMAX = 8;
    int *low = malloc(sizeof(int) * nc); int nlow = 0, left = 0;
    clock_t c0 = clock(); long it = 0, rebuilds = 0;
    for (;;) {
        if (left <= 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            nlow = 0; for (int k = 0; k < nc; k++) if (!inS[k] && conf[k] <= CMAX) low[nlow++] = k;
            left = 4000; rebuilds++;
            if (rebuilds % 500 == 0) fprintf(stderr, "t=%.0fs it=%ld members=%d best=%d low=%d\n", el, it, nmem, nbest, nlow);
        }
        left--; it++;
        if (nlow == 0) continue;
        int v = low[rndi(nlow)];
        if (inS[v] || conf[v] > CMAX) continue;
        if (conf[v] == 0) { addc(v); }
        else {
            int o[3], no = 0;
            const int32_t *z = zP + (size_t)v * ZN;
            for (int i = 0; i < ZN && no < 3; i++) { int u = ownP[z[i]]; if (u >= 0) { int d = 0; for (int t = 0; t < no; t++) if (o[t] == u) d = 1; if (!d) o[no++] = u; } }
            z = zL + (size_t)v * ZN;
            for (int i = 0; i < ZN && no < 3; i++) { int u = ownL[z[i]]; if (u >= 0) { int d = 0; for (int t = 0; t < no; t++) if (o[t] == u) d = 1; if (!d) o[no++] = u; } }
            if (no == 1) { int u = o[0]; remc(u); addc(v); refill(u); }
            else if (no == 2 && rndi(50) == 0) { int u0 = o[0], u1 = o[1]; remc(u0); remc(u1); addc(v); refill(u0); refill(u1); }
        }
        if (nmem > nbest) { nbest = nmem; memcpy(bestSet, memList, sizeof(int) * nmem); writeOut(); fprintf(stderr, "it %ld: best %d\n", it, nbest); }
        else if (nmem < nbest - 3) restore_best();
    }
    if (nmem < nbest) restore_best();
    fprintf(stderr, "done: %ld iterations, best %d\n", it, nbest);
    f = fopen(argv[6], "w"); if (!f) return 2;
    for (int i = 0; i < nbest; i++) fprintf(f, "%d %d\n", cp[bestSet[i]], cl[bestSet[i]]);
    fclose(f);
    printf("best %d\n", nbest);
    return 0;
}
