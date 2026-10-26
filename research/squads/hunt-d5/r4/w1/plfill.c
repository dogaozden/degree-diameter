/* plfill: pattern-restricted exact LNS (replace 2 elements, j-values fixed) for Haar graphs of Z53 x|16 Z26, d = 9.
 * cost = |G \ (S^-1 S)^2| + |G \ (S S^-1)^2| (same as haar5). Element index a*26 + j; identity 0 stays in S.
 * usage: plfill TABLE START_SET STEPS SEED [CPU_LIMIT]
 *   Each step: evaluates every pair of positions (i,k) and every pair of new a-values (53^2) with j_i, j_k fixed
 *   (C(8,2)*53^2 = 78,652 sets), moves to the best set (plateau moves to a random equal-cost set allowed).
 * prints one line per step: "STEP t cur best_nbhd evals cpu" and a final "RESULT best=<c> S= ...".
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int N; static uint16_t *T; static int inv_[2000];
static int stampA[2000], stampP[2000], gen = 0;
static int AA[2000], JJ[2000], MR[26][53], JA[26][26];
static inline int MUL(int x, int y) { int a = AA[x] + MR[JJ[x]][AA[y]]; if (a >= 53) a -= 53; return a * 26 + JA[JJ[x]][JJ[y]]; }
static const int d = 9;
static long long evals = 0;
static double cpu(void){ struct timespec t; clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }

static int cost(const int *S) {
    evals++;
    int c = 0; static int A[2000];
    for (int side = 0; side < 2; side++) {
        gen++; int nA = 0;
        for (int i = 0; i < d; i++) for (int j = 0; j < d; j++) {
            int x = side == 0 ? MUL(inv_[S[i]], S[j]) : MUL(S[i], inv_[S[j]]);
            if (stampA[x] != gen) { stampA[x] = gen; A[nA++] = x; }
        }
        gen++; int nP = 0;
        for (int i = 0; i < nA; i++) for (int j = 0; j < nA; j++) {
            int x = MUL(A[i], A[j]);
            if (stampP[x] != gen) { stampP[x] = gen; nP++; }
        }
        c += N - nP;
    }
    return c;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: plfill TABLE START_SET STEPS SEED [CPU_LIMIT]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("table"); return 2; }
    if (fread(&N, 4, 1, f) != 1) return 2;
    T = malloc(2 * (size_t)N * N); if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (T[(size_t)x*N+y] == 0) inv_[x] = y;
    for (int x = 0; x < N; x++) { AA[x] = x / 26; JJ[x] = x % 26; }
    { int r = 16, rp = 1; for (int j = 0; j < 26; j++) { for (int b = 0; b < 53; b++) MR[j][b] = rp * b % 53; rp = rp * r % 53; } }
    for (int j = 0; j < 26; j++) for (int l = 0; l < 26; l++) JA[j][l] = (j + l) % 26;
    { unsigned long long q = 12345; for (int t = 0; t < 100000; t++) { q = q*6364136223846793005ULL + 1442695040888963407ULL;
        int x = (q >> 20) % N, y = (q >> 40) % N; if (T[(size_t)x*N+y] != MUL(x,y)) { fprintf(stderr, "group check failed\n"); return 2; } } }
    int S[32]; int nread = 0;
    { char *p = argv[2]; /* comma or space separated */
      for (char *tok = strtok(p, " ,"); tok && nread < d; tok = strtok(NULL, " ,")) S[nread++] = atoi(tok); }
    if (nread != d || S[0] != 0) { fprintf(stderr, "start set must have 9 indices with identity 0 first\n"); return 2; }
    int steps = atoi(argv[3]); rs ^= (unsigned long long)atoll(argv[4]) * 2654435761ULL + 7; for (int i = 0; i < 10; i++) rnd();
    double lim = argc > 5 ? atof(argv[5]) : 1e9;
    int J[32]; for (int i = 0; i < d; i++) J[i] = S[i] % 26;
    int cur = cost(S), best = cur; int bestS[32]; memcpy(bestS, S, sizeof S);
    printf("START cost %d\n", cur);
    double t0 = cpu();
    for (int t = 1; t <= steps && best > 0 && cpu() - t0 < lim; t++) {
        int bc = 1 << 30; int nb = 0; static int cand[200000][2]; static int candA[200000][2];  /* (i,k) pairs and (a,b) values */
        int W[32];
        (void)W;
        for (int i = 1; i < d; i++) for (int k = i + 1; k < d; k++) for (int a = 0; a < 53; a++) for (int b = 0; b < 53; b++) {
            int gi = a * 26 + J[i], gk = b * 26 + J[k];
            if (gi == 0 || gk == 0) continue;
            int T2[32]; memcpy(T2, S, sizeof S); T2[i] = gi; T2[k] = gk;
            int dup = 0; for (int u = 0; u < d && !dup; u++) for (int v = u + 1; v < d; v++) if (T2[u] == T2[v]) { dup = 1; break; }
            if (dup) continue;
            int c = cost(T2);
            if (c < bc) { bc = c; nb = 0; }
            if (c == bc && nb < 200000) { cand[nb][0] = i * 100 + k; candA[nb][0] = gi; candA[nb][1] = gk; nb++; }
        }
        /* move: strictly better if any; else random plateau move (may be the current set: skip if equal) */
        int pick = rnd() % nb;
        if (bc <= cur) {
            int i = cand[pick][0] / 100, k = cand[pick][0] % 100;
            S[i] = candA[pick][0]; S[k] = candA[pick][1]; cur = bc;
            if (cur < best) { best = cur; memcpy(bestS, S, sizeof S); }
        }
        printf("STEP %d cur=%d nbhd_best=%d ties=%d evals=%lld cpu=%.1f\n", t, cur, bc, nb, evals, cpu() - t0);
        fflush(stdout);
    }
    printf("RESULT best=%d evals=%lld cpu=%.1f S=", best, evals, cpu() - t0);
    for (int i = 0; i < d; i++) printf(" %d", bestS[i]); printf("\nCHECK %d\n", cost(bestS));
    return 0;
}
