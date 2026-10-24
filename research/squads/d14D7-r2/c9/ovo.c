/* ovo.c (card c9): search for an ovoid of GH(q) = a perfect code of the collinearity graph (each point within
   collinearity distance 1 of exactly one chosen point). Exact cover by closed collinearity neighbourhoods, MRV branching.
   Usage: ovo GHFILE NODELIMIT. Prints the chosen points (one solution) or NONE/LIMIT. Compile: gcc -O2 -o ovo ovo.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int P, q, Q1, NS;
static int *LP, *PL, *nb, *nbn, *bc, *cov, *chosen; static int ncov = 0, nch = 0; static long nodes = 0, limit;
static int found = 0;
static void cover_pt(int z, int d) { /* d=+1 covers z (update blockers), d=-1 uncovers */
    ncov += d; cov[z] += d;
    for (int i = 0; i < nbn[z]; i++) bc[nb[z * NS + i]] += d; }
static void rec(void) {
    if (found) return;
    if (ncov == P) { found = 1; return; }
    if (++nodes > limit) return;
    int bestc = -1, bestn = 1 << 30;
    for (int c = 0; c < P; c++) { if (cov[c]) continue; int k = 0;
        for (int i = 0; i < nbn[c]; i++) { int x = nb[c * NS + i]; if (bc[x] == 0) k++; }
        if (k < bestn) { bestn = k; bestc = c; if (k <= 1) break; } }
    if (bestn == 0) return;
    int c = bestc; int cand[256], nc = 0;
    for (int i = 0; i < nbn[c]; i++) { int x = nb[c * NS + i]; if (bc[x] == 0) cand[nc++] = x; }
    for (int a = 0; a < nc && !found; a++) { int x = cand[a];
        /* choose row x: cover N[x] */
        for (int i = 0; i < nbn[x]; i++) cover_pt(nb[x * NS + i], 1);
        chosen[nch++] = x;
        rec();
        if (found) return;
        nch--; for (int i = 0; i < nbn[x]; i++) cover_pt(nb[x * NS + i], -1);
    }
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1; NS = 1 + q * Q1;
    limit = atol(argv[2]);
    LP = malloc(sizeof(int) * P * Q1); PL = malloc(sizeof(int) * P * Q1);
    for (int i = 0; i < P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2; fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    /* closed collinearity neighbourhood of each point x: nb[x*NS..], size NS = 1 + q(q+1) (with duplicates removed) */
    nb = malloc(sizeof(int) * P * NS); nbn = malloc(sizeof(int) * P); bc = calloc(P, sizeof(int)); cov = calloc(P, sizeof(int));
    chosen = malloc(sizeof(int) * P);
    int *mark = calloc(P, sizeof(int)); int stamp = 0;
    for (int x = 0; x < P; x++) { stamp++; int n = 0; nb[x * NS + n++] = x; mark[x] = stamp;
        for (int a = 0; a < Q1; a++) { int L = PL[x * Q1 + a]; for (int b = 0; b < Q1; b++) { int y = LP[L * Q1 + b]; if (mark[y] != stamp) { mark[y] = stamp; nb[x * NS + n++] = y; } } }
        nbn[x] = n; }
    rec();
    fprintf(stderr, "nodes %ld found %d\n", nodes, found);
    if (found) { printf("OVOID %d\n", nch); for (int i = 0; i < nch; i++) printf("%d\n", chosen[i]); return 0; }
    printf(nodes > limit ? "LIMIT\n" : "NONE\n"); return 1;
}
