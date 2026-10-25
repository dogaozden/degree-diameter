/* pk.c (card c9): K points pairwise opposite in GH(q) (a partial ovoid), by swap annealing on closed collinearity
   neighbourhoods. Energy = sum over points of max(0, occ-1), occ = number of chosen closed neighbourhoods containing it.
   Usage: pk GHFILE K SECONDS SEED OUTPOINTS. Compile: gcc -O3 -march=native -lm -o pk pk.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int P, q, Q1, NS; static int *LP, *PL, *nb; static int *occ; static long cost = 0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static void add(int x) { for (int i = 0; i < NS; i++) if (occ[nb[x * NS + i]]++ > 0) cost++; }
static void rem(int x) { for (int i = 0; i < NS; i++) if (--occ[nb[x * NS + i]] > 0) cost--; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1; NS = 1 + q * Q1;
    LP = malloc(sizeof(int) * P * Q1); PL = malloc(sizeof(int) * P * Q1);
    for (int i = 0; i < P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2; fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    nb = malloc(sizeof(int) * P * NS); int *mark = calloc(P, sizeof(int)); int stamp = 0;
    for (int x = 0; x < P; x++) { stamp++; int n = 0; nb[x * NS + n++] = x; mark[x] = stamp;
        for (int a = 0; a < Q1; a++) { int L = PL[x * Q1 + a]; for (int b = 0; b < Q1; b++) { int y = LP[L * Q1 + b]; if (mark[y] != stamp) { mark[y] = stamp; nb[x * NS + n++] = y; } } }
        if (n != NS) { fprintf(stderr, "bad nbhd\n"); return 3; } }
    int K = atoi(argv[2]); double secs = atof(argv[3]); rs ^= strtoull(argv[4], 0, 10) * 0x2545F4914F6CDD1DULL;
    occ = calloc(P, sizeof(int)); char *inS = calloc(P, 1); int *S = malloc(sizeof(int) * K);
    for (int i = 0; i < K; i++) { int x; do x = rndi(P); while (inS[x]); inS[x] = 1; S[i] = x; add(x); }
    double T0 = getenv("T0") ? atof(getenv("T0")) : 0.6, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    clock_t c0 = clock(); long it = 0, best = cost;
    while (cost > 0) {
        it++;
        if ((it & 0xFFF) == 0) { double fr = (double)(clock() - c0) / CLOCKS_PER_SEC / secs; if (fr >= 1.0) break; }
        double frac = (double)(clock() - c0) / CLOCKS_PER_SEC / secs; if (frac > 1) frac = 1;
        double T = T0 * pow(T1 / T0, frac);
        int i = rndi(K), g = S[i], x = rndi(P); if (inS[x]) continue;
        long old = cost; rem(g); add(x); long d = cost - old;
        if (d <= 0 || rndu() < exp(-(double)d / T)) { inS[g] = 0; inS[x] = 1; S[i] = x; if (cost < best) best = cost; }
        else { rem(x); add(g); }
    }
    fprintf(stderr, "K=%d cost=%ld best=%ld iters=%ld\n", K, cost, best, it);
    if (cost == 0) { FILE *fo = fopen(argv[5], "w"); for (int i = 0; i < K; i++) fprintf(fo, "%d\n", S[i]); fclose(fo); printf("SOLVED %d\n", K); return 0; }
    printf("UNSOLVED %d cost %ld\n", K, cost); return 1;
}
