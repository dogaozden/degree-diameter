/* kpack.c (card c9): fixed-size zone packing by simulated annealing with swap moves.
   A flag f = (p, l) has point zone {p} + points collinear with p off l (q^2 points) and line zone {l} + lines meeting
   l off p (q^2 lines); flags are compatible iff all zones of the chosen set are pairwise disjoint (same test as pack.c
   and t2design.c). Energy = sum over zone elements of max(0, occ-1). Usage: kpack GHFILE K SECONDS SEED OUTFLAGS
   Flag id f = p*(q+1) + a with l = PL[f]. Compile: gcc -O3 -march=native -lm -o kpack kpack.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int P, q, Q1, ZN, NF;
static int32_t *LP, *PL, *zP, *zL;
static uint16_t *occP, *occL;
static long cost = 0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void addF(int f) { const int32_t *a = zP + (size_t)f * ZN, *b = zL + (size_t)f * ZN;
    for (int i = 0; i < ZN; i++) { if (occP[a[i]]++ > 0) cost++; if (occL[b[i]]++ > 0) cost++; } }
static void remF(int f) { const int32_t *a = zP + (size_t)f * ZN, *b = zL + (size_t)f * ZN;
    for (int i = 0; i < ZN; i++) { if (--occP[a[i]] > 0) cost--; if (--occL[b[i]] > 0) cost--; } }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: kpack GHFILE K SECONDS SEED OUTFLAGS\n"); return 2; }
    FILE *fi = fopen(argv[1], "r"); if (!fi || fscanf(fi, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1; ZN = q * q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(fi, "%d", &LP[i]) != 1) return 2;
    fclose(fi);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    NF = P * Q1;
    zP = malloc(sizeof(int32_t) * (size_t)NF * ZN); zL = malloc(sizeof(int32_t) * (size_t)NF * ZN);
    for (int f = 0; f < NF; f++) {
        int p = f / Q1, l = PL[f], n1 = 0, n2 = 0;
        int32_t *a = zP + (size_t)f * ZN, *b = zL + (size_t)f * ZN;
        a[n1++] = p;
        for (int x = 0; x < Q1; x++) { int L = PL[p * Q1 + x]; if (L == l) continue;
            for (int y = 0; y < Q1; y++) { int w = LP[L * Q1 + y]; if (w != p) a[n1++] = w; } }
        b[n2++] = l;
        for (int x = 0; x < Q1; x++) { int y0 = LP[l * Q1 + x]; if (y0 == p) continue;
            for (int y = 0; y < Q1; y++) { int K = PL[y0 * Q1 + y]; if (K != l) b[n2++] = K; } }
        if (n1 != ZN || n2 != ZN) { fprintf(stderr, "zone size error\n"); return 3; }
    }
    occP = calloc(P, 2); occL = calloc(P, 2);
    int K = atoi(argv[2]); double secs = atof(argv[3]); rs ^= strtoull(argv[4], 0, 10) * 0x2545F4914F6CDD1DULL;
    for (int i = 0; i < 10; i++) rnd();
    int *S = malloc(sizeof(int) * K); char *inS = calloc(NF, 1);
    for (int i = 0; i < K; i++) { int f; do f = rndi(NF); while (inS[f]); inS[f] = 1; S[i] = f; addF(f); }
    int M = getenv("MCM") ? atoi(getenv("MCM")) : 24; double NZ = getenv("NZ") ? atof(getenv("NZ")) : 0.15;
    clock_t c0 = clock(); long it = 0; long best = cost; int *cf = malloc(sizeof(int) * K);
    while (cost > 0) {
        it++;
        if ((it & 0x3FF) == 0) { double fr = (double)(clock() - c0) / CLOCKS_PER_SEC / secs; if (fr >= 1.0) break; }
        int nc = 0;
        for (int i = 0; i < K; i++) { int f = S[i]; const int32_t *a = zP + (size_t)f * ZN, *b = zL + (size_t)f * ZN; int ov = 0;
            for (int j = 0; j < ZN; j++) { ov += occP[a[j]] > 1; ov += occL[b[j]] > 1; } if (ov) cf[nc++] = i; }
        if (nc == 0) break;
        int i = cf[rndi(nc)], g = S[i];
        remF(g); inS[g] = 0;
        int bf = -1; long bc = 1L << 30; int nb = 0;
        if (rndu() < NZ) { do bf = rndi(NF); while (inS[bf]); }
        else for (int m = 0; m < M; m++) { int f = rndi(NF); if (inS[f]) continue;
            const int32_t *a = zP + (size_t)f * ZN, *b = zL + (size_t)f * ZN; long c = 0;
            for (int j = 0; j < ZN; j++) { c += occP[a[j]] > 0; c += occL[b[j]] > 0; }
            if (c < bc) { bc = c; bf = f; nb = 1; } else if (c == bc && rndi(++nb) == 0) bf = f; }
        if (bf < 0) { bf = g; }
        addF(bf); inS[bf] = 1; S[i] = bf;
        if (cost < best) best = cost;
    }
    fprintf(stderr, "K=%d cost=%ld best=%ld iterations=%ld\n", K, cost, best, it);
    if (cost == 0) {
        FILE *fo = fopen(argv[5], "w");
        for (int i = 0; i < K; i++) { int f = S[i]; fprintf(fo, "%d %d\n", f / Q1, PL[f]); }
        fclose(fo); printf("SOLVED %d\n", K); return 0;
    }
    printf("UNSOLVED %d cost %ld\n", K, cost); return 1;
}
