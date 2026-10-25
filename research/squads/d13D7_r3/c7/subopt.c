/* subopt.c (squad round 3, card c7): exhaustive search over SUBSETS of a given clique K of the coset graph.
   For S subset of K (every subset of a clique is a clique) the score is F(S) = 11|S| + 122 - cov(S), cov(S) =
   #{d in E : n_d . S = F_11}.  Enumerates all removal sets J with |J| <= RMAX, prints the best F per |J|,
   and writes the best set to OUTPREFIX_best.txt (offset format "0 b c s f").
   usage: subopt OFFSETS RMAX OUTPREFIX */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NDIR 122
static int ndir = 0, dirN[NDIR][4];
static uint32_t M[NDIR][11];
static int k = 0, vs[32][4];
static void init_dirs(void) {
    for (int n = 1; n < 14641; n++) {
        int v[4] = {n % 11, (n / 11) % 11, (n / 121) % 11, n / 1331};
        int i = 0; while (i < 4 && v[i] == 0) i++;
        if (i == 4 || v[i] != 1) continue;
        if ((8 * v[0] * v[0] + 4 * v[1] * v[3] - v[2] * v[2]) % 11 != 0) continue;
        for (int q = 0; q < 4; q++) dirN[ndir][q] = v[q];
        ndir++;
    }
    if (ndir != NDIR) { fprintf(stderr, "bad direction count %d\n", ndir); exit(2); }
}
static int covS(uint32_t S) {
    int cov = 0;
    for (int d = 0; d < ndir; d++) {
        int ok = 1;
        for (int z = 0; z < 11; z++) if (!(S & M[d][z])) { ok = 0; break; }
        cov += ok;
    }
    return cov;
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: subopt OFFSETS RMAX OUTPREFIX\n"); return 1; }
    init_dirs();
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    char line[512];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#') continue;
        int a, b, c, e, ff;
        if (sscanf(line, "%d %d %d %d %d", &a, &b, &c, &e, &ff) != 5) continue;
        if (k >= 32) { fprintf(stderr, "too many\n"); return 1; }
        vs[k][0] = (((2 * a + e) % 11) + 11) % 11; vs[k][1] = ((b % 11) + 11) % 11;
        vs[k][2] = ((c % 11) + 11) % 11; vs[k][3] = ((ff % 11) + 11) % 11; k++;
    }
    fclose(f);
    int RMAX = atoi(argv[2]);
    memset(M, 0, sizeof M);
    for (int d = 0; d < ndir; d++) for (int i = 0; i < k; i++) {
        int r = 0; for (int q = 0; q < 4; q++) r += dirN[d][q] * vs[i][q];
        M[d][r % 11] |= (1u << i);
    }
    uint32_t full = (k == 32) ? 0xffffffffu : ((1u << k) - 1);
    printf("k = %d, cov(full) = %d\n", k, covS(full));
    int bestF[33]; uint32_t bestJ[33]; long cntbest[33]; int bestcov[33];
    for (int j = 0; j <= k; j++) { bestF[j] = -1000000; bestJ[j] = 0; cntbest[j] = 0; bestcov[j] = -1; }
    for (int j = 0; j <= RMAX && j <= k; j++) {
        /* Gosper's hack over j-subsets J of [k] */
        uint32_t J = (j == 0) ? 0 : ((1u << j) - 1);
        for (;;) {
            uint32_t S = full & ~J;
            int cov = covS(S);
            int F = 11 * (k - j) + 122 - cov;
            if (F > bestF[j]) { bestF[j] = F; bestJ[j] = J; cntbest[j] = 1; bestcov[j] = cov; }
            else if (F == bestF[j]) cntbest[j]++;
            if (j == 0) break;
            uint32_t c = J & -J, r = J + c;
            if (r == 0) break;
            J = (((r ^ J) >> 2) / c) | r;
            if (J > full) break;
        }
        printf("removed %2d: best F = %d (cov %d, |I| = %d), #subsets with best F = %ld, set size %d\n",
               j, bestF[j], bestcov[j], 122 - bestcov[j], cntbest[j], k - j);
        fflush(stdout);
    }
    /* write the overall best */
    int jb = 0; for (int j = 0; j <= RMAX && j <= k; j++) if (bestF[j] > bestF[jb]) jb = j;
    char path[1024]; snprintf(path, sizeof path, "%s_best.txt", argv[3]);
    FILE *g = fopen(path, "w");
    uint32_t S = full & ~bestJ[jb];
    fprintf(g, "# subopt best: F %d, removed %d, cov %d\n", bestF[jb], jb, bestcov[jb]);
    for (int i = 0; i < k; i++) if (S & (1u << i))
        fprintf(g, "0 %d %d %d %d\n", vs[i][1], vs[i][2], vs[i][0], vs[i][3]);
    fclose(g);
    printf("overall best F %d (removed %d) written to %s\n", bestF[jb], jb, path);
    return 0;
}
