/* ctrlpat: pattern-aware cubic controllers for route-chart lifts (hunt-d5), for charts that are pencil-complete and
   diagonal-complete but not universal (q = 2: (6,5)).  Controller = 3 perfect matchings pi_0, pi_1, pi_2 : A -> B
   (colour c joins u to m + pi_c(u)).  A same-side ordered pair (s,t) is covered if t = s (chart diagonal; set DIAG4=1
   to require a nonsingular 4-cycle instead; DIAG4A=1 / DIAG4B=1 for one side only), or t is at distance 2 (pencil), or some colour walk s -c1- . -c2- . -c3- .
   -c4- t with consecutive colours distinct has a pattern c1c2c3c4 that is nonsingular for the side of s.
   cost = uncovered ordered same-side pairs.
   Usage: ctrlpat m CHART seconds seed [OUT]     CHART: chartq output (lines "SINGA abcd", "SINGB abcd")
   OUT: "2m" then lines "u v c" (colour c), A = 0..m-1, B = m..2m-1, written at cost 0.
   Env T0 (1.0), COOL (steps per e-fold, 3e5). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
static int m, pi[3][256], ipi[3][256], singA[81], singB[81], DIAG4 = 0, D4A = 0, D4B = 0;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int nbr(int x, int c) { return x < m ? m + pi[c][x] : ipi[c][x - m]; }
static int cost(void) {
    int bad = 0; static int cov[512];
    for (int s = 0; s < 2 * m; s++) {
        int *sing = s < m ? singA : singB; int lo = s < m ? 0 : m;
        for (int t = lo; t < lo + m; t++) cov[t] = 0;
        if (!(DIAG4 || (s < m ? D4A : D4B))) cov[s] = 1;
        for (int c1 = 0; c1 < 3; c1++) { int x1 = nbr(s, c1);
            for (int c2 = 0; c2 < 3; c2++) { if (c2 == c1) continue; int x2 = nbr(x1, c2); cov[x2] = 1;
                for (int c3 = 0; c3 < 3; c3++) { if (c3 == c2) continue; int x3 = nbr(x2, c3);
                    for (int c4 = 0; c4 < 3; c4++) { if (c4 == c3) continue; int x4 = nbr(x3, c4);
                        if (!sing[c1 * 27 + c2 * 9 + c3 * 3 + c4]) cov[x4] = 1; } } } }
        for (int t = lo; t < lo + m; t++) if (!cov[t]) bad++;
    }
    return bad;
}
static int okvert(int u) { return pi[0][u] != pi[1][u] && pi[0][u] != pi[2][u] && pi[1][u] != pi[2][u]; }
int main(int argc, char **argv) {
    m = atoi(argv[1]); double secs = atof(argv[3]); rs ^= strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL;
    const char *out = argc > 5 ? argv[5] : NULL; DIAG4 = getenv("DIAG4") ? atoi(getenv("DIAG4")) : 0; D4A = getenv("DIAG4A") ? atoi(getenv("DIAG4A")) : 0; D4B = getenv("DIAG4B") ? atoi(getenv("DIAG4B")) : 0;
    FILE *f = fopen(argv[2], "r"); char line[512];
    while (fgets(line, sizeof line, f)) { int a, b, c, d;
        if (sscanf(line, "SINGA %1d%1d%1d%1d", &a, &b, &c, &d) == 4) singA[a * 27 + b * 9 + c * 3 + d] = 1;
        if (sscanf(line, "SINGB %1d%1d%1d%1d", &a, &b, &c, &d) == 4) singB[a * 27 + b * 9 + c * 3 + d] = 1; }
    fclose(f);
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, COOL = getenv("COOL") ? atof(getenv("COOL")) : 3e5;
    for (int i = 0; i < 30; i++) rnd();
    for (;;) { for (int c = 0; c < 3; c++) { for (int i = 0; i < m; i++) pi[c][i] = i; for (int i = m - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = pi[c][i]; pi[c][i] = pi[c][j]; pi[c][j] = t; } }
        int ok = 1; for (int u = 0; u < m; u++) ok &= okvert(u); if (ok) break; }
    for (int c = 0; c < 3; c++) for (int u = 0; u < m; u++) ipi[c][pi[c][u]] = u;
    int cur = cost(), best = cur, bp[3][256]; memcpy(bp, pi, sizeof pi);
    double t0 = now(); long step = 0;
    while (best > 0 && now() - t0 < secs) {
        step++; double T = T0 * exp(-(double)(step % (long)(4 * COOL)) / COOL) + 0.03;
        int c = rnd() % 3, u1 = rnd() % m, u2 = rnd() % m; if (u1 == u2) continue;
        int t = pi[c][u1]; pi[c][u1] = pi[c][u2]; pi[c][u2] = t;
        if (!okvert(u1) || !okvert(u2)) { pi[c][u2] = pi[c][u1]; pi[c][u1] = t; continue; }
        ipi[c][pi[c][u1]] = u1; ipi[c][pi[c][u2]] = u2;
        int cc = cost();
        if (cc <= cur || rnd01() < exp(-(cc - cur) / T)) { cur = cc; if (cc < best) { best = cc; memcpy(bp, pi, sizeof pi); fprintf(stderr, "t=%.1f step=%ld best=%d\n", now() - t0, step, best); } }
        else { pi[c][u2] = pi[c][u1]; pi[c][u1] = t; ipi[c][pi[c][u1]] = u1; ipi[c][pi[c][u2]] = u2; }
    }
    printf("RESULT ctrlpat m=%d best=%d steps=%ld time=%.1f\n", m, best, step, now() - t0);
    if (best == 0 && out) { FILE *o = fopen(out, "w"); fprintf(o, "%d\n", 2 * m);
        for (int c = 0; c < 3; c++) for (int u = 0; u < m; u++) fprintf(o, "%d %d %d\n", u, m + bp[c][u], c); fclose(o); }
    return best == 0 ? 0 : 1;
}
