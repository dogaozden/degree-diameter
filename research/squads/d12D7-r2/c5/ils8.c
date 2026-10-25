/* ils8.c (c5 scratch): iterated local search for K coverage sets (cov6 output) minimising the uncovered targets.
   Usage: ils8 COV UFILE NC K ITERS SEED  -> prints best uncovered and the chosen candidate indices (0-based). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int64_t NC, NU, W64; static uint64_t *cov;
static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static int64_t uncovered(const int64_t *S, int K) {
    uint64_t *all = calloc(W64, 8);
    for (int s = 0; s < K; s++) for (int64_t w = 0; w < W64; w++) all[w] |= cov[S[s] * W64 + w];
    int64_t c = 0; for (int64_t w = 0; w < W64; w++) c += __builtin_popcountll(all[w]); free(all);
    return NU - c;
}
int main(int argc, char **argv) {
    if (argc < 7) return 2;
    NC = atoll(argv[3]); NU = 0; int K = atoi(argv[4]); long iters = atol(argv[5]); rng ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL;
    FILE *fu = fopen(argv[2], "rb"); fseek(fu, 0, SEEK_END); NU = ftell(fu) / 4; fclose(fu);
    W64 = (NU + 63) / 64;
    cov = malloc(NC * W64 * 8); FILE *f = fopen(argv[1], "rb"); if (fread(cov, 8, NC * W64, f) != (size_t)(NC * W64)) return 1; fclose(f);
    int64_t *S = malloc(K * 8); int64_t *best = malloc(K * 8);
    int64_t bestU = NU + 1;
    for (int64_t s = 0; s < K; s++) S[s] = xr() % NC;
    uint64_t *oth = malloc(W64 * 8);
    for (long rs = 0; rs < iters; rs++) {
        /* local search: for each slot, best replacement */
        int improved = 1;
        while (improved) {
            improved = 0;
            for (int s0 = 0; s0 < K; s0++) {
                int s = (int)(xr() % K);
                memset(oth, 0, W64 * 8);
                for (int t = 0; t < K; t++) if (t != s) for (int64_t w = 0; w < W64; w++) oth[w] |= cov[S[t] * W64 + w];
                int64_t curc = 0; for (int64_t w = 0; w < W64; w++) curc += __builtin_popcountll(oth[w] | cov[S[s] * W64 + w]);
                int64_t bc = curc, bi = -1;
                for (int64_t c = 0; c < NC; c++) {
                    int dup = 0; for (int t = 0; t < K; t++) if (S[t] == c) { dup = 1; break; } if (dup) continue;
                    int64_t cc = 0; for (int64_t w = 0; w < W64; w++) cc += __builtin_popcountll(oth[w] | cov[c * W64 + w]);
                    if (cc > bc) { bc = cc; bi = c; }
                }
                if (bi >= 0) { S[s] = bi; improved = 1; }
            }
        }
        int64_t U = uncovered(S, K);
        if (U < bestU) { bestU = U; memcpy(best, S, K * 8); printf("restart %ld: uncovered %lld  S =", rs, (long long)U); for (int s = 0; s < K; s++) printf(" %lld", (long long)S[s]); printf("\n"); fflush(stdout); }
        if (bestU == 0) break;
        /* perturb from the best: replace 2 random slots by random candidates */
        memcpy(S, best, K * 8);
        for (int p = 0; p < 2; p++) { int s = xr() % K; int64_t c; do { c = xr() % NC; } while (0); S[s] = c; }
    }
    printf("best uncovered %lld; sets (0-based candidate index):", (long long)bestU);
    for (int s = 0; s < K; s++) printf(" %lld", (long long)best[s]); printf("\n");
    return 0;
}
