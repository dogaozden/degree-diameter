/* union2.c: independent set > MINSIZE inside U = S4 u {v not in S4 : v has at most K neighbours in S4}. Uses lns.c's B&B.
 * Usage: union2 MAP FLAGS K BUDGET MINSIZE */
#define main lns_main
#include "lns.c"
#undef main

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: union2 MAP FLAGS K BUDGET MINSIZE\n"); return 1; }
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
    static int inA[NV], cA[NV];
    static int A[NV]; int na = 0;
    f = fopen(argv[2], "r"); if (!f) return 1;
    int p, l;
    while (fscanf(f, "%d %d", &p, &l) == 2) { int v = pt2v[p]; if (!inA[v]) { inA[v] = 1; A[na++] = v; } }
    fclose(f);
    int K = atoi(argv[3]);
    for (int v = 0; v < NV; v++) if (!inA[v]) for (int i = 0; i < na; i++) if (orth(v, A[i])) cA[v]++;
    nf = 0;
    for (int v = 0; v < NV; v++) if (inA[v] || cA[v] <= K) { if (nf >= FMAX) { printf("too many candidates (> %d) for K=%d\n", FMAX, K); return 0; } F[nf++] = v; }
    for (int i = 0; i < nf; i++) {
        memset(fadj[i], 0, sizeof fadj[i]);
        for (int j = 0; j < nf; j++) if (i != j && orth(F[i], F[j])) bset(fadj[i], j);
    }
    int minsize = atoi(argv[5]);
    budget = atoll(argv[4]);
    best = minsize; nbest = 0; nodes = 0; aborted = 0; ncur = 0;
    uint64_t P[W]; memset(P, 0, sizeof P);
    for (int i = 0; i < nf; i++) bset(P, i);
    double t0 = now();
    mis_rec(P, 0);
    printf("K=%d candidates %d (S=%d); independent set > %d: found %d, aborted=%d, nodes=%lld, %.1f s\n",
           K, nf, na, minsize, nbest, aborted, nodes, now() - t0);
    if (nbest > minsize) {
        FILE *g = fopen("union2_best.txt", "w");
        for (int i = 0; i < nbest; i++) { int v = F[bestF[i]]; fprintf(g, "%d %d\n", hexid[v], sline[v]); }
        fclose(g);
    }
    return 0;
}
