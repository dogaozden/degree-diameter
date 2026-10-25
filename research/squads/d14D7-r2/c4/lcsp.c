/* lcsp.c (card c4): choose one line through each point of a pairwise-opposite point set so that the chosen lines are
   pairwise opposite (distance 6 in the incidence graph of H(q)); then the flag set has disjoint point and line zones.
   Usage: lcsp GHFILE PTSFILE SECONDS SEED OUTFLAGS     (PTSFILE: one hexagon point index per line)
   Conflict between candidate lines = distance <= 4 (BFS in the line graph). Min-conflicts tabu over the choice. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
static int P, q, Q1;
static int32_t *LP, *PL;
static unsigned long long rs = 0x2545F4914F6CDD1DULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lcsp GHFILE PTSFILE SECONDS SEED OUTFLAGS\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    rs ^= strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[3]);
    /* read points */
    int *pts = malloc(sizeof(int) * P); int S = 0; f = fopen(argv[2], "r"); int a;
    while (f && fscanf(f, "%d", &a) == 1) pts[S++] = a; if (f) fclose(f);
    int C = S * Q1;                       /* candidate c = s*Q1 + a : line PL[pts[s]*Q1+a] */
    int *cl = malloc(sizeof(int) * C);
    for (int s = 0; s < S; s++) for (int b = 0; b < Q1; b++) cl[s * Q1 + b] = PL[pts[s] * Q1 + b];
    /* candidate line index -> candidate id (line may be a candidate for at most one point since points are non-collinear) */
    int *lineCand = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) lineCand[i] = -1;
    for (int c = 0; c < C; c++) lineCand[cl[c]] = c;
    /* conflicts: candidates c, d of different points with d(line_c, line_d) <= 4 */
    int *mark = calloc(P, sizeof(int)); int stamp = 0;
    int **adj = malloc(sizeof(int*) * C); int *deg = calloc(C, sizeof(int));
    int *buf = malloc(sizeof(int) * 20000);
    long totalConf = 0;
    for (int c = 0; c < C; c++) {
        stamp++; int L1 = cl[c]; int nb = 0;
        mark[L1] = stamp;
        /* distance 2 lines: meet L1 */
        int d2[512]; int n2 = 0;
        for (int i = 0; i < Q1; i++) { int x = LP[L1 * Q1 + i]; for (int j = 0; j < Q1; j++) { int M = PL[x * Q1 + j]; if (M == L1 || mark[M] == stamp) continue; mark[M] = stamp; d2[n2++] = M; } }
        for (int t = 0; t < n2; t++) { int M = d2[t];
            for (int i = 0; i < Q1; i++) { int y = LP[M * Q1 + i]; for (int j = 0; j < Q1; j++) { int N = PL[y * Q1 + j]; if (mark[N] == stamp) continue; mark[N] = stamp; } } }
        /* now mark[] == stamp exactly on lines within distance 4 (incl. L1); collect candidate conflicts */
        for (int d = 0; d < C; d++) { if (d / Q1 == c / Q1) continue; if (mark[cl[d]] == stamp) buf[nb++] = d; }
        adj[c] = malloc(sizeof(int) * (nb + 1)); memcpy(adj[c], buf, sizeof(int) * nb); deg[c] = nb; totalConf += nb;
    }
    fprintf(stderr, "points %d candidates %d avg conflicts per candidate %.1f\n", S, C, (double)totalConf / C);
    /* min-conflicts tabu over choices val[s] in 0..q */
    int *val = malloc(sizeof(int) * S); int *cnt = calloc(C, sizeof(int)); long *tabu = calloc(S * Q1, sizeof(long));
    for (int s = 0; s < S; s++) val[s] = rnd() % Q1;
    for (int c = 0; c < C; c++) cnt[c] = 0;
    /* cnt[c] = number of conflicting candidates that are currently chosen */
    #define CHOSEN(c) (val[(c) / Q1] == (c) % Q1)
    for (int c = 0; c < C; c++) if (CHOSEN(c)) for (int i = 0; i < deg[c]; i++) cnt[adj[c][i]]++;
    long conf = 0; for (int s = 0; s < S; s++) conf += cnt[s * Q1 + val[s]]; conf /= 2;
    fprintf(stderr, "initial conflicts %ld\n", conf);
    long it = 0; long bestConf = conf; clock_t c0 = clock();
    int *bestVal = malloc(sizeof(int) * S); memcpy(bestVal, val, sizeof(int) * S);
    int *vs = malloc(sizeof(int) * S);
    while (conf > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC; if (el > secs) break;
        it++;
        int nv = 0; for (int s = 0; s < S; s++) if (cnt[s * Q1 + val[s]] > 0) vs[nv++] = s;
        int s = vs[rnd() % nv];
        int bestA = -1, bc = 1 << 30, nbst = 0;
        for (int a = 0; a < Q1; a++) { int c = s * Q1 + a; if (a == val[s]) continue; int v = cnt[c];
            if (tabu[s * Q1 + a] > it && conf + v - cnt[s * Q1 + val[s]] >= bestConf) continue;
            if (v < bc) { bc = v; bestA = a; nbst = 1; } else if (v == bc && (rnd() % (++nbst)) == 0) bestA = a; }
        if (bestA < 0) continue;
        int old = val[s]; int co = s * Q1 + old, cn = s * Q1 + bestA;
        conf += cnt[cn] - cnt[co];
        for (int i = 0; i < deg[co]; i++) cnt[adj[co][i]]--;
        val[s] = bestA;
        for (int i = 0; i < deg[cn]; i++) cnt[adj[cn][i]]++;
        tabu[s * Q1 + old] = it + 5 + (long)(rnd() % 10);
        if (conf < bestConf) { bestConf = conf; memcpy(bestVal, val, sizeof(int) * S); }
        if (it % 20000 == 0) fprintf(stderr, "it %ld conf %ld best %ld (%.1fs)\n", it, conf, bestConf, (double)(clock() - c0) / CLOCKS_PER_SEC);
    }
    /* verify on bestVal */
    long c2 = 0; for (int c = 0; c < C; c++) { int s1 = c / Q1, a1 = c % Q1; if (bestVal[s1] != a1) continue; for (int i = 0; i < deg[c]; i++) { int d = adj[c][i]; if (bestVal[d / Q1] == d % Q1) c2++; } }
    fprintf(stderr, "best conflicts %ld (recheck %ld) after %ld iterations\n", bestConf, c2 / 2, it);
    f = fopen(argv[5], "w");
    for (int s = 0; s < S; s++) fprintf(f, "%d %d\n", pts[s], cl[s * Q1 + bestVal[s]]);
    fclose(f);
    printf("%ld %d\n", bestConf, S);
    return bestConf == 0 ? 0 : 1;
}
