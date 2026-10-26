/* Tabu search over Haar graphs H(G,S), |S| = d, diameter <= 5 cost (same cost as haar5: uncovered elements of
   (S^-1 S)^2 plus of (S S^-1)^2). Best-improvement over all single swaps (position i, new element g), tabu on
   re-adding removed elements, aspiration on new global best, random tie-breaking (plateau moves), restart from the
   best set with random perturbation after STALL steps without improvement.
   usage: tabu TABLE d CPU_S WALL_S SEED TMIN TMAX STALL OUT [INIT "i0 i1 ..."] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int N, d;
static uint16_t *MT;
static int *INV;
static uint32_t *stamp;
static uint32_t ep = 0;
static int *TT;
static inline int mul(int x, int y) { return MT[(size_t)x * N + y]; }
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static double cpu(void) { struct timespec t; clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static void newep(void) { ep++; if (ep == 0) { memset(stamp, 0, sizeof(uint32_t) * N); ep = 1; } }

static int side_cost(const int *S, int sideB) {
    int nt = 0;
    newep();
    for (int i = 0; i < d; i++) for (int j = 0; j < d; j++) {
        int t = sideB ? mul(S[i], INV[S[j]]) : mul(INV[S[i]], S[j]);
        if (stamp[t] != ep) { stamp[t] = ep; TT[nt++] = t; }
    }
    newep();
    int cov = 0;
    for (int i = 0; i < nt; i++) {
        const uint16_t *row = MT + (size_t)TT[i] * N;
        for (int j = 0; j < nt; j++) { int g = row[TT[j]]; if (stamp[g] != ep) { stamp[g] = ep; cov++; } }
    }
    return N - cov;
}
static int cost(const int *S) { return side_cost(S, 0) + side_cost(S, 1); }

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: tabu TABLE d CPU_S WALL_S SEED TMIN TMAX STALL OUT [INIT]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 2; }
    if (fread(&N, 4, 1, f) != 1) return 2;
    MT = malloc((size_t)N * N * 2);
    if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul(x, y) == 0) { INV[x] = y; break; }
    stamp = calloc(N, sizeof(uint32_t));
    TT = malloc(sizeof(int) * 4096);
    d = atoi(argv[2]);
    double cpub = atof(argv[3]), wallb = atof(argv[4]);
    rs = (uint64_t)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345; if (!rs) rs = 1;
    for (int k = 0; k < 10; k++) rnd();
    int tmin = atoi(argv[6]), tmax = atoi(argv[7]), stall = atoi(argv[8]);
    const char *out = argv[9];
    int S[64], bestS[64], kpert = 3;
    char *inS = calloc(N, 1);
    int *tabu = calloc(N, sizeof(int));
    if (argc > 10) {
        char *p = argv[10]; char *e;
        for (int i = 0; i < d; i++) { S[i] = (int)strtol(p, &e, 10); p = e; }
    } else {
        S[0] = 0;
        for (int i = 1; i < d; i++) { int g; do g = rndint(N); while (inS[g] || g == 0); S[i] = g; inS[g] = 1; }
        /* note: inS marks only elements 1..d-1 here; 0 handled below */
    }
    memset(inS, 0, N);
    for (int i = 0; i < d; i++) inS[S[i]] = 1;
    int cur = cost(S), best = cur;
    memcpy(bestS, S, sizeof S);
    long step = 0, lastimp = 0;
    double t0 = wall(), c0 = cpu();
    fprintf(stderr, "start cost=%d\n", cur);
    while (best > 0) {
        if (cpu() - c0 > cpub || wall() - t0 > wallb) break;
        int bv = 1 << 30, bi = -1, bg = -1, nties = 0;
        for (int i = 0; i < d; i++) {
            int a = S[i];
            for (int g = 0; g < N; g++) {
                if (inS[g]) continue;
                int istabu = tabu[g] > step;
                S[i] = g; int v = cost(S); S[i] = a;
                if (istabu && !(v < best)) continue;
                if (v < bv) { bv = v; bi = i; bg = g; nties = 1; }
                else if (v == bv) { nties++; if (rndint(nties) == 0) { bi = i; bg = g; } }
            }
        }
        if (bi < 0) break;
        int a = S[bi];
        inS[a] = 0; S[bi] = bg; inS[bg] = 1;
        tabu[a] = (int)(step + tmin + rndint(tmax - tmin + 1));
        cur = bv; step++;
        if (cur < best) { best = cur; memcpy(bestS, S, sizeof S); lastimp = step; }
        if (step % 500 == 0) fprintf(stderr, "step %ld cur=%d best=%d cpu=%.1f\n", step, cur, best, cpu() - c0);
        if (step - lastimp > stall) {
            /* restart from best set, perturb */
            memset(inS, 0, N);
            memcpy(S, bestS, sizeof S);
            for (int i = 0; i < d; i++) inS[S[i]] = 1;
            for (int k = 0; k < kpert; k++) {
                int i = rndint(d), g;
                do g = rndint(N); while (inS[g]);
                inS[S[i]] = 0; S[i] = g; inS[g] = 1;
            }
            memset(tabu, 0, sizeof(int) * N);
            cur = cost(S);
            lastimp = step;
        }
    }
    printf("RESULT tabu table=%s d=%d seed=%s best=%d steps=%ld cpu=%.1f wall=%.1f S= ", argv[1], d, argv[5], best, step, cpu() - c0, wall() - t0);
    for (int i = 0; i < d; i++) printf("%d ", bestS[i]);
    printf("\n");
    if (best == 0) {
        FILE *o = fopen(out, "w");
        for (int i = 0; i < d; i++) fprintf(o, "%d ", bestS[i]);
        fprintf(o, "\n"); fclose(o);
    }
    return 0;
}
