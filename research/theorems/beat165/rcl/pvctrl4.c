/* Annealing version of pvctrl.c. Controllers as permutation-voltage lifts: vertices (v, g), v in base [0,2k)
   (v<k: side A), g in group (table); sigma_t(v,g) = (pi_t(v), phi_t[v] * g), t in {a, b}; pi_t swaps sides.
   Objective = (# same-side vertices at distance > 4 from the 2k base sources) + 50 * (# base vertices without a
   label-reduced closed walk of length 4). Moves: one voltage, or a transposition in pi_a / pi_b (same side).
   Metropolis acceptance, temperature falling linearly from T0 to 0 over each run.
   usage: pvctrl4 TABLE k seed runs steps T0  -> prints controllers with objective 0 as "CTRL k=.. m=.. pa .. pb .. fa .. fb .." */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int m, T[256][256], inv_[256], e, k, nb;
static int pa[32], pb[32], fa[32], fb[32], pai[32], pbi[32];
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int stepv(int t, int x) { int v = x / m, g = x % m;   /* t: 0 a, 1 A, 2 b, 3 B */
    switch (t) { case 0: return pa[v] * m + T[fa[v]][g];
                 case 1: { int w = pai[v]; return w * m + T[inv_[fa[w]]][g]; }
                 case 2: return pb[v] * m + T[fb[v]][g];
                 default: { int w = pbi[v]; return w * m + T[inv_[fb[w]]][g]; } } }
static int objective(void) {
    for (int v = 0; v < nb; v++) { pai[pa[v]] = v; pbi[pb[v]] = v; }
    int N = nb * m, miss = 0, no4 = 0; static int dist[8192], q[8192];
    for (int v = 0; v < nb; v++) {
        int s = v * m + e; for (int i = 0; i < N; i++) dist[i] = -1; int h = 0, tl = 0; dist[s] = 0; q[tl++] = s;
        while (h < tl) { int x = q[h++]; if (dist[x] >= 4) continue; for (int t = 0; t < 4; t++) { int y = stepv(t, x); if (dist[y] < 0) { dist[y] = dist[x] + 1; q[tl++] = y; } } }
        int side = v < k ? 0 : 1;
        for (int w = 0; w < nb; w++) if ((w < k ? 0 : 1) == side) for (int g = 0; g < m; g++) if (dist[w * m + g] < 0) miss++;
        int found = 0;
        for (int t1 = 0; t1 < 4 && !found; t1++) { int x1 = stepv(t1, s);
          for (int t2 = 0; t2 < 4 && !found; t2++) { if (t2 == (t1 ^ 1)) continue; int x2 = stepv(t2, x1);
            for (int t3 = 0; t3 < 4 && !found; t3++) { if (t3 == (t2 ^ 1)) continue; int x3 = stepv(t3, x2);
              for (int t4 = 0; t4 < 4; t4++) { if (t4 == (t3 ^ 1)) continue; if (stepv(t4, x3) == s) { found = 1; break; } } } } }
        if (!found) no4++;
    }
    return miss + 50 * no4; }
static void randperm_swap(int *p) {
    int x[32], y[32]; for (int i = 0; i < k; i++) { x[i] = k + i; y[i] = i; }
    for (int i = k - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = x[i]; x[i] = x[j]; x[j] = t; j = rnd() % (i + 1); t = y[i]; y[i] = y[j]; y[j] = t; }
    for (int i = 0; i < k; i++) { p[i] = x[i]; p[k + i] = y[i]; } }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[16384]; m = 0;
    while (fgets(line, sizeof line, f)) { if (strlen(line) < 2) continue; char *p = line; int j = 0; while (*p) { while (*p == ' ') p++; if (*p == '\n' || !*p) break; T[m][j++] = strtol(p, &p, 10); } m++; }
    for (int i = 0; i < m; i++) { int ok = 1; for (int j = 0; j < m; j++) if (T[i][j] != j) { ok = 0; break; } if (ok) { e = i; break; } }
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (T[i][j] == e) inv_[i] = j;
    k = atoi(argv[2]); nb = 2 * k; rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    int runs = atoi(argv[4]); long steps = atol(argv[5]); double T0 = atof(argv[6]); int found = 0, bestall = 1 << 30;
    for (int r = 0; r < runs; r++) {
        randperm_swap(pa); randperm_swap(pb);
        for (int v = 0; v < nb; v++) { fa[v] = rnd() % m; fb[v] = rnd() % m; }
        int c = objective(), best = c;
        for (long it = 0; it < steps && c > 0; it++) {
            double temp = T0 * (1.0 - (double)it / steps);
            int spa[32], spb[32], sfa[32], sfb[32]; memcpy(spa, pa, sizeof pa); memcpy(spb, pb, sizeof pb); memcpy(sfa, fa, sizeof fa); memcpy(sfb, fb, sizeof fb);
            int w = rnd() % 10;
            if (w == 0 && k > 1) { int *p = rnd() & 1 ? pa : pb; int side = rnd() & 1; int i = side * k + rnd() % k, j = side * k + rnd() % k; int t = p[i]; p[i] = p[j]; p[j] = t; }
            else if (w < 5) fa[rnd() % nb] = rnd() % m; else fb[rnd() % nb] = rnd() % m;
            int c2 = objective();
            if (c2 <= c || (temp > 0 && urand() < exp((c - c2) / temp))) { c = c2; if (c < best) best = c; }
            else { memcpy(pa, spa, sizeof pa); memcpy(pb, spb, sizeof pb); memcpy(fa, sfa, sizeof fa); memcpy(fb, sfb, sizeof fb); }
        }
        if (best < bestall) bestall = best;
        if (c == 0) { found++; printf("CTRL k=%d m=%d pa", k, m); for (int v = 0; v < nb; v++) printf(" %d", pa[v]); printf(" pb"); for (int v = 0; v < nb; v++) printf(" %d", pb[v]);
            printf(" fa"); for (int v = 0; v < nb; v++) printf(" %d", fa[v]); printf(" fb"); for (int v = 0; v < nb; v++) printf(" %d", fb[v]); printf("\n"); fflush(stdout);
            if (found >= 5) break; }
        printf("run %d best %d end %d\n", r, best, c); fflush(stdout);
    }
    printf("done m=%d k=%d best objective %d, found %d\n", m, k, bestall, found);
    return 0; }
