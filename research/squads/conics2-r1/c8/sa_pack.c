/* Simulated annealing for weighted star packing in H(q).
   A star = (centre p, nonempty subset S of the q+1 lines through p); elements = p plus the other points of lines in S;
   weight |S|. Packing = point-disjoint stars. Maximising total weight gives a valid dual segment set G = union of lines.
   usage: sa_pack geom.txt iters T0 T1 seed outfile */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void){ return (rnd() >> 11) * (1.0/9007199254740992.0); }
int q, N, Lc, K1;
int *LP, *PL;           /* LP[l*(q+1)+j], PL[p*(q+1)+j] */
int M;                  /* number of candidate stars */
int *cp, *cmask, *cw, *eoff, *elem;   /* per candidate */
int *owner, *inP; int *Pl; int nP; int *posP;
int *cconf; int ncconf;
static int *mark; static int markstamp = 1;
int main(int argc, char **argv){
    if (argc < 7) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    double iters = atof(argv[2]), T0 = atof(argv[3]), T1 = atof(argv[4]);
    rs = (uint64_t)atoll(argv[5]) * 2654435761ULL + 88172645463325252ULL;
    if (fscanf(f, "%d %d %d", &q, &N, &Lc) != 3) return 1;
    K1 = q + 1;
    LP = malloc(sizeof(int) * Lc * K1);
    for (int l = 0; l < Lc; l++) for (int j = 0; j < K1; j++) if (fscanf(f, "%d", &LP[l*K1+j]) != 1) return 1;
    fclose(f);
    PL = malloc(sizeof(int) * N * K1);
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < Lc; l++) for (int j = 0; j < K1; j++) { int p = LP[l*K1+j]; PL[p*K1 + cnt[p]++] = l; }
    int nm = (1 << K1) - 1;
    M = N * nm;
    cp = malloc(sizeof(int)*M); cmask = malloc(sizeof(int)*M); cw = malloc(sizeof(int)*M); eoff = malloc(sizeof(int)*(M+1));
    int tot = 0;
    for (int p = 0; p < N; p++) for (int m = 1; m <= nm; m++) {
        int id = p*nm + (m-1); cp[id] = p; cmask[id] = m;
        int k = 0; for (int j = 0; j < K1; j++) if (m >> j & 1) k++;
        cw[id] = k; tot += 1 + k*q;
    }
    elem = malloc(sizeof(int)*tot); int pos = 0;
    for (int id = 0; id < M; id++) {
        eoff[id] = pos; int p = cp[id], m = cmask[id];
        elem[pos++] = p;
        for (int j = 0; j < K1; j++) if (m >> j & 1) {
            int l = PL[p*K1 + j];
            for (int t = 0; t < K1; t++) { int x = LP[l*K1+t]; if (x != p) elem[pos++] = x; }
        }
    }
    eoff[M] = pos;
    owner = malloc(sizeof(int)*N); for (int x = 0; x < N; x++) owner[x] = -1;
    inP = calloc(M, sizeof(int)); Pl = malloc(sizeof(int)*M); posP = malloc(sizeof(int)*M);
    nP = 0; int W = 0, bestW = 0;
    int *bestP = malloc(sizeof(int)*M); int nbest = 0;
    mark = calloc(M, sizeof(int)); cconf = malloc(sizeof(int)*64); 
    double lT0 = log(T0), lT1 = log(T1);
    long long it = 0, Nit = (long long)iters;
    for (it = 0; it < Nit; it++) {
        double T = exp(lT0 + (lT1 - lT0) * (double)it / (double)Nit);
        int s = rnd() % M;
        if (inP[s]) continue;
        /* conflicts */
        ncconf = 0; markstamp++;
        int bad = 0;
        for (int e = eoff[s]; e < eoff[s+1]; e++) {
            int o = owner[elem[e]];
            if (o >= 0 && mark[o] != markstamp) { mark[o] = markstamp; if (ncconf < 64) cconf[ncconf++] = o; else bad = 1; }
        }
        if (bad) continue;
        int delta = cw[s];
        for (int i = 0; i < ncconf; i++) delta -= cw[cconf[i]];
        if (delta >= 0 || urand() < exp(delta / T)) {
            for (int i = 0; i < ncconf; i++) {
                int c = cconf[i];
                for (int e = eoff[c]; e < eoff[c+1]; e++) owner[elem[e]] = -1;
                /* remove from P */
                int pp = posP[c]; int last = Pl[nP-1]; Pl[pp] = last; posP[last] = pp; nP--; inP[c] = 0;
                W -= cw[c];
            }
            for (int e = eoff[s]; e < eoff[s+1]; e++) owner[elem[e]] = s;
            posP[s] = nP; Pl[nP++] = s; inP[s] = 1; W += cw[s];
            if (W > bestW) {
                bestW = W; nbest = nP; memcpy(bestP, Pl, sizeof(int)*nP);
            }
        }
    }
    /* write lines of the best packing */
    FILE *o = fopen(argv[6], "w");
    char *lineon = calloc(Lc, 1); int nl = 0;
    for (int i = 0; i < nbest; i++) {
        int id = bestP[i]; int p = cp[id], m = cmask[id];
        for (int j = 0; j < K1; j++) if (m >> j & 1) { int l = PL[p*K1+j]; if (!lineon[l]) { lineon[l] = 1; nl++; } }
    }
    for (int l = 0; l < Lc; l++) if (lineon[l]) fprintf(o, "%d ", l);
    fprintf(o, "\n"); fclose(o);
    printf("best_weight %d stars %d lines %d iters %lld\n", bestW, nbest, nl, it);
    return 0;
}
