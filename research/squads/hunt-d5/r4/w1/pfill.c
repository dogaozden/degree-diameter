/* pfill: pattern-then-fill annealer for Haar graphs H(G,S), cost = |G \ (S^-1 S)^2| + |G \ (S S^-1)^2| (as haar5).
 * G = Z_53 x|_16 Z_26 read from a haar5-format table (int32 N, uint16 N*N, identity 0); element index = a*26 + j.
 * usage: pfill TABLE.bin d K SECONDS SEED CYC MODE [j_1 ... j_{d-1}]
 *   MODE = pat : S = {e} + one element per j_i (j_i fixed, a_i free in Z_53); e in S.
 *   MODE = free: every non-identity element free (baseline, same SA schedule).
 *   CYC = seconds per anneal cycle (temperature T0 -> T1 geometric within a cycle, restart from random each cycle).
 * prints "RESULT best=<c> cycles=<n> evals=<e> S= <indices>" and "BEST <c> S <indices>" on improvement (pat mode, final).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int N; static uint16_t *T; static int inv_[2000];
static int AA[2000], JJ[2000], MR[26][53], JA[26][26];
static inline int MUL(int x, int y) {   /* (a,j)(b,l) = (a + 16^j b, j + l) */
    int a = AA[x] + MR[JJ[x]][AA[y]]; if (a >= 53) a -= 53;
    int j = JA[JJ[x]][JJ[y]]; return a * 26 + j; }
static int stampA[2000], stampP[2000], gen = 0;
static int d, Jp[32], mode_pat;
static int L[32][2000], nL[32];   /* candidate elements per position (position 0 is e) */
static double now(void){ struct timespec t; clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&t); return t.tv_sec+1e-9*t.tv_nsec; }  /* CPU seconds */
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static long long evals = 0;

static int cost(const int *S){
    evals++;
    int c = 0;
    static int A[2000], P[2000];
    for (int side = 0; side < 2; side++) {
        gen++;
        int nA = 0;
        for (int i = 0; i < d; i++) for (int j = 0; j < d; j++) {
            int x = side == 0 ? MUL(inv_[S[i]], S[j]) : MUL(S[i], inv_[S[j]]);
            if (stampA[x] != gen) { stampA[x] = gen; A[nA++] = x; }
        }
        int nP = 0; int g2 = gen;
        gen++;
        for (int i = 0; i < nA; i++) for (int j = 0; j < nA; j++) {
            int x = MUL(A[i], A[j]);
            if (stampP[x] != gen) { stampP[x] = gen; nP++; }
        }
        c += N - nP;
        (void)g2;
    }
    return c;
}

int main(int argc, char **argv){
    if (argc < 8){ fprintf(stderr, "usage: pfill TABLE d K SECONDS SEED CYC MODE [j...]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("table"); return 2; }
    if (fread(&N, 4, 1, f) != 1) return 2;
    T = malloc(2*(size_t)N*N); if (fread(T, 2, (size_t)N*N, f) != (size_t)N*N) { fprintf(stderr, "short\n"); return 2; }
    fclose(f);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (T[(size_t)x*N+y] == 0) inv_[x] = y;
    for (int x = 0; x < N; x++) { AA[x] = x / 26; JJ[x] = x % 26; }
    { int r = 16, rp = 1; for (int j = 0; j < 26; j++) { for (int b = 0; b < 53; b++) MR[j][b] = rp * b % 53; rp = rp * r % 53; } }
    for (int j = 0; j < 26; j++) for (int l = 0; l < 26; l++) JA[j][l] = (j + l) % 26;
    { unsigned long long q = 12345; for (int t = 0; t < 200000; t++) { q = q*6364136223846793005ULL + 1442695040888963407ULL;
        int x = (q >> 20) % N, y = (q >> 40) % N; if (T[(size_t)x*N+y] != MUL(x,y)) { fprintf(stderr, "group check failed\n"); return 2; } } }
    d = atoi(argv[2]); int K = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 2654435761ULL + 1; for (int i=0;i<10;i++) rnd();
    double cyc = atof(argv[6]);
    mode_pat = strcmp(argv[7], "pat") == 0;
    int m = 53, k = 26;  /* Z53 x| Z26 */
    (void)K;
    if (mode_pat) {
        if (argc < 8 + d - 1) { fprintf(stderr, "need d-1 j values\n"); return 2; }
        for (int i = 1; i < d; i++) Jp[i] = atoi(argv[7 + i]);
        for (int i = 1; i < d; i++) { nL[i] = 0; for (int a = 0; a < m; a++) L[i][nL[i]++] = a*k + Jp[i]; }
    } else {
        for (int i = 1; i < d; i++) { nL[i] = 0; for (int g = 1; g < N; g++) L[i][nL[i]++] = g; }
    }
    if (!mode_pat && strcmp(argv[7], "eval") == 0) {   /* cost of sets read from stdin, one per line */
        int S2[32];
        while (1) { int ok = 1; for (int i = 0; i < d; i++) if (scanf("%d", &S2[i]) != 1) { ok = 0; break; }
            if (!ok) break; printf("%d\n", cost(S2)); }
        return 0;
    }
    int bestAll = 1 << 30; int bestS[32]; long long cycles = 0;
    double t0 = now(); int S[32];
    while (now() - t0 < secs) {
        cycles++;
        /* random init */
        S[0] = 0;
        for (int i = 1; i < d; i++) {
            int ok; do { S[i] = L[i][rnd() % nL[i]]; ok = 1; for (int j = 0; j < i; j++) if (S[j]==S[i]) ok = 0; } while (!ok);
        }
        int cur = cost(S), best = cur; int bS[32]; memcpy(bS, S, sizeof S);
        double c0 = now(), T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
        double tnow = now();
        while (1) {
            tnow = now(); double frac = (tnow - c0) / cyc; if (frac >= 1.0) break;
            double temp = T0 * pow(T1/T0, frac);
            int i = 1 + rnd() % (d - 1);
            int g = L[i][rnd() % nL[i]];
            int dup = 0; for (int j = 0; j < d; j++) if (S[j] == g) { dup = 1; break; }
            if (dup) continue;
            int old = S[i]; S[i] = g;
            int c = cost(S);
            if (c <= cur || exp((cur - c) / temp) > (rnd() % 1000000) / 1e6) {
                cur = c;
                if (cur < best) { best = cur; memcpy(bS, S, sizeof S); }
            } else S[i] = old;
            if (best == 0) break;
        }
        if (best < bestAll) { bestAll = best; memcpy(bestS, bS, sizeof bS); }
        if (bestAll == 0) break;
    }
    printf("RESULT best=%d cycles=%lld evals=%lld time=%.1f mode=%s", bestAll, cycles, evals, now()-t0, argv[7]);
    if (mode_pat) { printf(" pat="); for (int i = 1; i < d; i++) printf("%d,", Jp[i]); }
    printf("\nBEST %d S", bestAll); for (int i = 0; i < d; i++) printf(" %d", bestS[i]); printf("\n");
    /* verify */
    printf("CHECK %d\n", cost(bestS));
    return 0;
}
