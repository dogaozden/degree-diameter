/* union.c: exact-ish search for an independent set larger than 240 inside U = S4 u S8 (union of the two 240 starts).
 * Usage: union MAP FLAGS1 FLAGS2 BUDGET [MINSIZE]. Uses the B&B of lns.c (included). */
#define main lns_main
#include "lns.c"
#undef main

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: union MAP FLAGS1 FLAGS2 BUDGET [MINSIZE]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
    for (int i = 0; i < NV; i++) {
        if (fscanf(f, "%d %d", &hexid[i], &sline[i]) != 2) return 1;
        for (int c = 0; c < 7; c++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; x %= Q; if (x < 0) x += Q; X[i][c] = x; }
        if (hexid[i] > maxpt) maxpt = hexid[i];
    }
    fclose(f);
    pt2v = malloc(sizeof(int) * (maxpt + 1));
    for (int i = 0; i <= maxpt; i++) pt2v[i] = -1;
    for (int i = 0; i < NV; i++) pt2v[hexid[i]] = i;
    static int inU[NV];
    for (int a = 3; a <= 4; a++) {
        f = fopen(argv[a - 2 + 1 - 1 + 0 == 0 ? 2 : (a == 3 ? 2 : 3)], "r");
        if (!f) return 1;
        int p, l;
        while (fscanf(f, "%d %d", &p, &l) == 2) inU[pt2v[p]] = 1;
        fclose(f);
    }
    nf = 0;
    for (int v = 0; v < NV; v++) if (inU[v]) F[nf++] = v;
    if (nf > FMAX) { fprintf(stderr, "union too large %d\n", nf); return 1; }
    for (int i = 0; i < nf; i++) {
        memset(fadj[i], 0, sizeof fadj[i]);
        for (int j = 0; j < nf; j++) if (i != j && orth(F[i], F[j])) bset(fadj[i], j);
    }
    int minsize = argc > 5 ? atoi(argv[5]) : 240;
    budget = atoll(argv[4]);
    best = minsize; nbest = 0; nodes = 0; aborted = 0; ncur = 0;
    uint64_t P[W]; memset(P, 0, sizeof P);
    for (int i = 0; i < nf; i++) bset(P, i);
    double t0 = now();
    mis_rec(P, 0);
    printf("union size %d; search for independent set > %d: found %d (aborted=%d, nodes=%lld, %.1f s)\n",
           nf, minsize, nbest, aborted, nodes, now() - t0);
    if (nbest > minsize) {
        FILE *g = fopen("union_best.txt", "w");
        for (int i = 0; i < nbest; i++) { int v = F[bestF[i]]; fprintf(g, "%d %d\n", hexid[v], sline[v]); }
        fclose(g);
    }
    return 0;
}
