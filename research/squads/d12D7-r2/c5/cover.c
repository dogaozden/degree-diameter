/* cover.c: which level-0 lines are within incidence distance 4 of a freed line (a candidate level-0 owner of a
   point-side hub). Input: hex_q9.bin, the .sol, and a miss list (vertex ids; lines are 66430 + l at level 0).
   Greedy max-coverage of the miss list by K candidate balls B4(M[p]), p freed. Prints coverage per greedy step.
   Usage: cover HEX SOL MISS K */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc < 5) return 2;
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0], N = hdr[1], Lc = hdr[2], Q1 = q + 1;
    int32_t *LP = malloc(sizeof(int32_t) * (size_t)Lc * Q1); if (fread(LP, 4, (size_t)Lc * Q1, f) != (size_t)Lc * Q1) return 1; fclose(f);
    /* point -> lines */
    int32_t *PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *pc = calloc(N, sizeof(int));
    for (int l = 0; l < Lc; l++) for (int t = 0; t < Q1; t++) { int p = LP[(size_t)l * Q1 + t]; PL[(size_t)p * Q1 + pc[p]++] = l; }
    for (int p = 0; p < N; p++) if (pc[p] != Q1) { fprintf(stderr, "bad incidence\n"); return 1; }
    int K, nn, qq, nv; char w[32];
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "d7hex %d %d %d %d %31s", &qq, &nn, &K, &nv, w) != 5) return 1;
    int32_t *fp = malloc(sizeof(int32_t) * K); for (int k = 0; k < K; k++) if (fscanf(f, "%d", &fp[k]) != 1) return 1;
    char tok[32]; int hm; if (fscanf(f, "%31s %d", tok, &hm) != 2) return 1; for (int e = 0; e < 2 * hm; e++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; }
    int32_t *M = malloc(sizeof(int32_t) * N); for (int p = 0; p < N; p++) if (fscanf(f, "%d", &M[p]) != 1) return 1; fclose(f);
    /* miss list */
    int *inS = calloc(Lc, sizeof(int)); int nS = 0; long v;
    f = fopen(argv[3], "r"); while (fscanf(f, "%ld", &v) == 1) { if (v >= N && v < N + Lc) { if (!inS[v - N]) { inS[v - N] = 1; nS++; } } else { fprintf(stderr, "non-line miss %ld ignored\n", v); } }
    fclose(f);
    int Kc = atoi(argv[4]);
    int *sidx = malloc(sizeof(int) * Lc); int ns = 0; for (int l = 0; l < Lc; l++) if (inS[l]) sidx[l] = ns++; else sidx[l] = -1;
    fprintf(stderr, "misses (lines) %d, freed %d\n", nS, K);
    /* ball of each freed line: list of S-lines within distance 4 (lines at distance 0,2,4) */
    int *vis_l = calloc(Lc, sizeof(int)), *vis_p = calloc(N, sizeof(int)); int stamp = 0;
    int32_t *frontL = malloc(sizeof(int32_t) * Lc), *frontP = malloc(sizeof(int32_t) * N), *nextL = malloc(sizeof(int32_t) * Lc);
    int32_t **cov = malloc(sizeof(int32_t *) * K); int *covn = calloc(K, sizeof(int));
    int64_t ballsz = 0;
    for (int k = 0; k < K; k++) {
        int L0 = M[fp[k]]; stamp++;
        int nfl = 1, nfp = 0, nnl = 0; frontL[0] = L0; vis_l[L0] = stamp;
        int32_t *buf = malloc(sizeof(int32_t) * 8000); int bn = 0;
        if (inS[L0]) buf[bn++] = L0;
        for (int d = 1; d <= 4; d++) {
            /* lines frontL -> points (distance d), then points -> lines (d+1) */
            nfp = 0;
            for (int i = 0; i < nfl; i++) { int l = frontL[i]; for (int t = 0; t < Q1; t++) { int p = LP[(size_t)l * Q1 + t]; if (vis_p[p] != stamp) { vis_p[p] = stamp; frontP[nfp++] = p; } } }
            if (d == 4) break;
            nnl = 0;
            for (int i = 0; i < nfp; i++) { int p = frontP[i]; for (int t = 0; t < Q1; t++) { int l = PL[(size_t)p * Q1 + t]; if (vis_l[l] != stamp) { vis_l[l] = stamp; nextL[nnl++] = l; if (inS[l]) buf[bn++] = l; } } }
            /* swap */
            int32_t *tmp = frontL; frontL = nextL; nextL = tmp; nfl = nnl;
            if (d == 3) break;
        }
        /* the loop above collects lines at distance 0, 2 (and 4 handled below) */
        /* lines at distance 4: from the points at distance 3 */
        free(buf);
        /* recompute cleanly: BFS with explicit distances */
        stamp++;
        int cnt = 0; int32_t *lst = malloc(sizeof(int32_t) * 8000);
        {
            int32_t *fl = malloc(sizeof(int32_t) * Lc); int nfl2 = 1; fl[0] = L0; vis_l[L0] = stamp;
            if (inS[L0]) lst[cnt++] = L0;
            int32_t *fpnt = malloc(sizeof(int32_t) * N);
            for (int d = 0; d < 4; d += 2) {
                /* fl: lines at distance d -> points at d+1 -> lines at d+2 */
                int nfp2 = 0;
                for (int i = 0; i < nfl2; i++) { int l = fl[i]; for (int t = 0; t < Q1; t++) { int p = LP[(size_t)l * Q1 + t]; if (vis_p[p] != stamp) { vis_p[p] = stamp; fpnt[nfp2++] = p; } } }
                int nl2 = 0;
                for (int i = 0; i < nfp2; i++) { int p = fpnt[i]; for (int t = 0; t < Q1; t++) { int l = PL[(size_t)p * Q1 + t]; if (vis_l[l] != stamp) { vis_l[l] = stamp; fl[nl2++] = l; if (inS[l]) lst[cnt++] = l; } } }
                /* fl now holds lines at distance d+2 (they are the next frontier) */
                nfl2 = nl2;
                if (d + 2 == 4) break;
            }
            free(fl); free(fpnt);
        }
        cov[k] = malloc(sizeof(int32_t) * (cnt + 1)); memcpy(cov[k], lst, sizeof(int32_t) * cnt); covn[k] = cnt; free(lst);
        ballsz += 0;
        free(frontL == NULL ? NULL : NULL);
    }
    /* greedy max coverage */
    char *covered = calloc(Lc, 1); int got = 0; char *used = calloc(K, 1);
    int32_t *sl = malloc(sizeof(int32_t) * (size_t)Kc);
    for (int step = 0; step < Kc; step++) {
        int best = -1, bestc = -1;
        for (int k = 0; k < K; k++) if (!used[k]) {
            int c = 0; for (int i = 0; i < covn[k]; i++) if (!covered[cov[k][i]]) c++;
            if (c > bestc) { bestc = c; best = k; }
        }
        if (best < 0 || bestc <= 0) break;
        used[best] = 1; sl[step] = best;
        for (int i = 0; i < covn[best]; i++) if (!covered[cov[best][i]]) { covered[cov[best][i]] = 1; got++; }
        printf("step %d: freed index %d (line %d, p %d): +%d, covered %d of %d\n", step + 1, best, M[fp[best]] , fp[best], bestc, got, nS);
    }
    /* stats: largest single ball coverage */
    int mx = 0; for (int k = 0; k < K; k++) if (covn[k] > mx) mx = covn[k];
    printf("max single ball coverage of misses: %d (ball B4 cap %d)\n", mx, 7381);
    return 0;
}
