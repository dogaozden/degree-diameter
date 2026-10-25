/* sa8.c (c5 scratch): simulated annealing for K coverage sets minimising uncovered targets (bitsets from cov6).
   Usage: sa8 COV UFILE NC K MOVES T0 T1 SEED  -> best uncovered and the 0-based candidates. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
static int64_t NC, NU, W64; static uint64_t *cov;
static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static int K; static int64_t *S;
static int64_t cost(const int64_t *SS) {
    static uint64_t *all = NULL; if (!all) all = malloc(W64 * 8);
    memset(all, 0, W64 * 8);
    for (int s = 0; s < K; s++) { const uint64_t *c = cov + SS[s] * W64; for (int64_t w = 0; w < W64; w++) all[w] |= c[w]; }
    int64_t c = 0; for (int64_t w = 0; w < W64; w++) c += __builtin_popcountll(all[w]);
    return NU - c;
}
int main(int argc, char **argv) {
    if (argc < 9) return 2;
    NC = atoll(argv[3]); K = atoi(argv[4]); long long moves = atoll(argv[5]); double T0 = atof(argv[6]), T1 = atof(argv[7]);
    rng ^= (uint64_t)atoll(argv[8]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    FILE *fu = fopen(argv[2], "rb"); fseek(fu, 0, SEEK_END); NU = ftell(fu) / 4; fclose(fu); W64 = (NU + 63) / 64;
    cov = malloc(NC * W64 * 8); FILE *f = fopen(argv[1], "rb"); if (fread(cov, 8, NC * W64, f) != (size_t)(NC * W64)) return 1; fclose(f);
    S = malloc(K * 8); int64_t *best = malloc(K * 8);
    for (int s = 0; s < K; s++) S[s] = xr() % NC;
    int64_t cur = cost(S), bestc = cur; memcpy(best, S, K * 8);
    for (long long it = 0; it < moves; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)moves);
        int s = xr() % K; int64_t old = S[s]; int64_t c = xr() % NC;
        int dup = 0; for (int t = 0; t < K; t++) if (S[t] == c) { dup = 1; break; } if (dup) continue;
        S[s] = c; int64_t nc = cost(S); int64_t d = nc - cur;
        if (d <= 0 || ur() < exp(-d / T)) { cur = nc; if (cur < bestc) { bestc = cur; memcpy(best, S, K * 8); if (bestc == 0) break; } }
        else S[s] = old;
    }
    printf("SA best uncovered %lld; sets:", (long long)bestc); for (int s = 0; s < K; s++) printf(" %lld", (long long)best[s]); printf("\n");
    return 0;
}
