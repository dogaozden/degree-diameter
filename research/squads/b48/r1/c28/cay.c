// cay.c: bipartite Cayley graphs Cay(G,S) on metacyclic G = Z_m x|_r Z_k (k even),
// |S| = 4, S inverse-closed and contained in the odd-parity coset (j odd), so the graph is bipartite.
// Cost = number of elements of G at distance > 8 from e (Cayley graph is vertex-transitive, so this is
// the whole diameter check). Element (a,j) is index a + m*j; (a,j)(c,l) = (a + r^j c, j + l).
// Usage: cay M K R SECONDS SEED [OUT_EDGES] [MODE: 0 pairs, 1 involutions, 2 both]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int M, K, R, N;
static int *PW, *AOF, *JOF, *INV, *ODD, *INVOL, *VIS, *Q;
static int nodd = 0, ninv = 0, stamp = 0;
static uint64_t rng_state;

static inline uint64_t rnd(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state;
}
static inline int mulg(int g, int h) {
    int a = AOF[g], j = JOF[g], c = AOF[h], l = JOF[h];
    int x = (int)((a + (long long)PW[j] * c) % M);
    int y = (j + l) % K;
    return x + M * y;
}
static int ball_cost(const int *S, int D) {
    stamp++;
    int head = 0, tail = 0;
    Q[tail++] = 0; VIS[0] = stamp;
    for (int d = 0; d < D; d++) {
        int end = tail;
        for (; head < end; head++) {
            int g = Q[head];
            for (int t = 0; t < 4; t++) {
                int h = mulg(g, S[t]);
                if (VIS[h] != stamp) { VIS[h] = stamp; Q[tail++] = h; }
            }
        }
    }
    return N - tail;
}
static int valid_set(const int *S) {
    for (int i = 0; i < 4; i++) {
        if (JOF[S[i]] % 2 == 0) return 0;
        for (int j = i + 1; j < 4; j++) if (S[i] == S[j]) return 0;
    }
    // inverse-closed
    for (int i = 0; i < 4; i++) {
        int found = 0;
        for (int j = 0; j < 4; j++) if (S[j] == INV[S[i]]) found = 1;
        if (!found) return 0;
    }
    return 1;
}
static void random_set(int *S, int mode) {
    for (;;) {
        int use_inv = (mode == 1) || (mode == 2 && (rnd() & 1));
        if (use_inv && ninv >= 4) {
            for (int i = 0; i < 4; i++) S[i] = INVOL[rnd() % ninv];
            if (valid_set(S)) return;
        } else {
            int x = ODD[rnd() % nodd], y = ODD[rnd() % nodd];
            S[0] = x; S[1] = INV[x]; S[2] = y; S[3] = INV[y];
            if (valid_set(S)) return;
        }
    }
}
static void mutate(int *S, int mode) {
    int T[4];
    for (;;) {
        memcpy(T, S, sizeof(T));
        int isinv = 1;
        for (int i = 0; i < 4; i++) if (INV[S[i]] != S[i]) isinv = 0;
        if (isinv) {
            T[rnd() % 4] = INVOL[rnd() % ninv];
        } else {
            int p = (int)(rnd() % 2);
            int x = ODD[rnd() % nodd];
            T[2 * p] = x; T[2 * p + 1] = INV[x];
        }
        if (valid_set(T)) { memcpy(S, T, sizeof(T)); return; }
        (void)mode;
    }
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: cay M K R SECONDS SEED [OUT] [MODE]\n"); return 1; }
    M = atoi(argv[1]); K = atoi(argv[2]); R = atoi(argv[3]);
    double secs = atof(argv[4]);
    rng_state = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[5]) * 2654435761ULL;
    const char *out = argc > 6 ? argv[6] : NULL;
    int mode = argc > 7 ? atoi(argv[7]) : 2;
    N = M * K;
    PW = malloc(sizeof(int) * K);
    PW[0] = 1 % M;
    for (int j = 1; j < K; j++) PW[j] = (int)((long long)PW[j - 1] * R % M);
    if (PW[K - 1] * (long long)R % M != 1 % M) {
        // not needed: check r^k = 1
    }
    if ((long long)PW[K - 1] * R % M != 1 % M) { fprintf(stderr, "r^k != 1 mod m\n"); return 1; }
    AOF = malloc(sizeof(int) * N); JOF = malloc(sizeof(int) * N); INV = malloc(sizeof(int) * N);
    ODD = malloc(sizeof(int) * N); INVOL = malloc(sizeof(int) * N);
    VIS = calloc(N, sizeof(int)); Q = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) { AOF[g] = g % M; JOF[g] = g / M; }
    for (int g = 0; g < N; g++) {
        int a = AOF[g], j = JOF[g];
        int jj = (K - j) % K;
        int x = (int)(((long long)(M - PW[jj]) * a) % M);
        INV[g] = x + M * jj;
    }
    for (int g = 0; g < N; g++) {
        if (JOF[g] % 2 == 1) {
            ODD[nodd++] = g;
            if (INV[g] == g) INVOL[ninv++] = g;
        }
    }
    // odd elements that are not involutions and order checks are handled by valid_set
    if (nodd < 2) { printf("RESULT ERROR no odd elements\n"); return 1; }
    int best[4] = {0, 0, 0, 0}, bestcost = N + 1, cur[4];
    clock_t t0 = clock();
    long long evals = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        random_set(cur, mode);
        int c = ball_cost(cur, 8); evals++;
        int stall = 0;
        while (stall < 400 && c > 0) {
            int T[4]; memcpy(T, cur, sizeof(T));
            mutate(T, mode);
            int ct = ball_cost(T, 8); evals++;
            if (ct <= c) { if (ct < c) stall = 0; else stall++; c = ct; memcpy(cur, T, sizeof(T)); }
            else stall++;
            if ((double)(clock() - t0) / CLOCKS_PER_SEC >= secs) break;
        }
        if (c < bestcost) { bestcost = c; memcpy(best, cur, sizeof(best)); }
        if (bestcost == 0) break;
    }
    printf("GROUP meta %d %d %d N=%d odd=%d invol=%d evals=%lld\n", M, K, R, N, nodd, ninv, evals);
    printf("S %d %d %d %d (a,j): (%d,%d) (%d,%d) (%d,%d) (%d,%d)\n", best[0], best[1], best[2], best[3],
           AOF[best[0]], JOF[best[0]], AOF[best[1]], JOF[best[1]], AOF[best[2]], JOF[best[2]], AOF[best[3]], JOF[best[3]]);
    int far = ball_cost(best, 8);
    printf("RESULT n=%d cost=%d miss=%.4f\n", N, far, (double)far / 1.0);
    if (out) {
        FILE *f = fopen(out, "w");
        fprintf(f, "%d\n", N);
        for (int g = 0; g < N; g++)
            for (int t = 0; t < 4; t++) {
                int h = mulg(g, best[t]);
                if (g < h) fprintf(f, "%d %d\n", g, h);
            }
        fclose(f);
    }
    return 0;
}
