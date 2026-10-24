/* povoid_ils2.c: povoid_ils.c with the bilinear form computed in GF(q) for every q that hexgen2.c supports (p, p^2
   for odd p with alpha^2 = least non-square; 2^e with x^2+x+1 / x^3+x+1), plus a start-up check on 20 random points
   that B(x,y) = 0 iff distance <= 4 in the incidence graph (job cell-13-7, for (10,7) at q = 8).
   usage: povoid_ils2 HEXFILE seconds seed [init_file] > out.txt   (writes best set, one point index per line) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
int q, N; uint8_t *co; static int FA[32][32], FM[32][32], FN[32];
static void field(void) { int p = 2; while (q % p) p++; int e = 0, t = q; while (t % p == 0) { t /= p; e++; }
    if (p == 2) { int poly = (e == 2) ? 7 : 11;
        for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { FA[x][y] = x ^ y; int r = 0, a = x, b = y;
            while (b) { if (b & 1) r ^= a; b >>= 1; a <<= 1; if (e > 1 && (a & q)) a ^= poly; } FM[x][y] = (e == 1) ? (x & y) : r; } }
    else { int nr = 0; if (e == 2) for (int c = 2; c < p && !nr; c++) { int sq = 0; for (int u = 1; u < p; u++) if (u * u % p == c) sq = 1; if (!sq) nr = c; }
        for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { int a = x % p, b = x / p, c = y % p, d = y / p;
            FA[x][y] = (a + c) % p + p * ((b + d) % p); FM[x][y] = (a * c + b * d % p * nr) % p + p * ((a * d + b * c) % p); } }
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) if (FA[x][y] == 0) FN[x] = y; }
static inline int B(int a, int b) { const uint8_t *x = co + 7L * a, *y = co + 7L * b;
    int s = FA[FA[FA[FA[FA[FM[x[0]][y[4]]][FM[x[4]][y[0]]]][FM[x[1]][y[5]]]][FM[x[5]][y[1]]]][FM[x[2]][y[6]]]][FM[x[6]][y[2]]];
    int t = FM[x[3]][y[3]]; t = FA[t][t]; return FA[s][FN[t]]; }
static uint64_t rs; static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int *tight, *inR, *R, m;
static void add(int r) { inR[r] = 1; R[m++] = r; for (int x = 0; x < N; x++) if (x != r && B(x, r) == 0) tight[x]++; }
static void del(int r) { inR[r] = 0; for (int i = 0; i < m; i++) if (R[i] == r) { R[i] = R[--m]; break; } for (int x = 0; x < N; x++) if (x != r && B(x, r) == 0) tight[x]--; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1; q = hdr[0]; N = hdr[1];
    int32_t *lp = malloc(4L * N * (q + 1)); if (fread(lp, 4, (size_t)N * (q + 1), f) != (size_t)N * (q + 1)) return 1;
    co = malloc(7L * N); if (fread(co, 1, 7L * N, f) != 7L * N) return 1; fclose(f); field();
    { /* criterion check: B(x,y) = 0 iff distance <= 4, for 20 random points */
      int Q1 = q + 1; int32_t *pl = malloc(4L * N * Q1); int *c = calloc(N, sizeof(int));
      for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = lp[(size_t)l * Q1 + k]; pl[(size_t)p * Q1 + c[p]++] = l; }
      uint8_t *dist = malloc(2L * N); int32_t *qu = malloc(8L * N); long bad = 0;
      for (int tt = 0; tt < 20; tt++) { int s0 = (int)((tt * 7919L) % N); memset(dist, 255, 2L * N); int h = 0, t = 0; dist[s0] = 0; qu[t++] = s0;
          while (h < t) { int x = qu[h++]; if (dist[x] >= 4) continue; const int32_t *nb = (x < N) ? &pl[(size_t)x * Q1] : &lp[(size_t)(x - N) * Q1]; int off = (x < N) ? N : 0;
              for (int k = 0; k < Q1; k++) { int y = nb[k] + off; if (dist[y] == 255) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
          for (int y = 0; y < N; y++) if ((dist[y] <= 4) != (B(s0, y) == 0)) bad++; }
      fprintf(stderr, "criterion B = 0 iff distance <= 4: %s (%ld mismatches)\n", bad ? "FAILS" : "holds", bad); if (bad) return 1;
      free(pl); free(c); free(dist); free(qu); }
    double secs = atof(argv[2]); rs = 88172645463325252ULL ^ (uint64_t)atoll(argv[3]) * 2654435761ULL; for (int i = 0; i < 20; i++) rnd();
    tight = calloc(N, sizeof(int)); inR = calloc(N, sizeof(int)); R = malloc(sizeof(int) * N); m = 0;
    if (argc > 4) { FILE *g = fopen(argv[4], "r"); char buf[128]; while (fgets(buf, sizeof buf, g)) { int v; if (buf[0] != '#' && sscanf(buf, "%d", &v) == 1 && !inR[v] && tight[v] == 0) add(v); } fclose(g); }
    /* greedy fill */
    int *perm = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < N; i++) { int x = perm[i]; if (!inR[x] && tight[x] == 0) add(x); }
    int best = m; int *bestR = malloc(sizeof(int) * N); memcpy(bestR, R, sizeof(int) * m);
    fprintf(stderr, "start %d\n", m);
    clock_t t0 = clock(); long it = 0; int *cand = malloc(sizeof(int) * N);
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        /* try (1,2)-swaps: for a random r in R, collect 1-tight points orthogonal to r, find two non-orthogonal ones */
        int improved = 0;
        for (int tries = 0; tries < m && !improved; tries++) {
            int r = R[rnd() % m]; int nc = 0;
            for (int x = 0; x < N; x++) if (!inR[x] && tight[x] == 1 && B(x, r) == 0) cand[nc++] = x;
            for (int a = 0; a < nc && !improved; a++) for (int b = a + 1; b < nc; b++) if (B(cand[a], cand[b]) != 0) {
                del(r); add(cand[a]); add(cand[b]);
                /* fill free */
                for (int x = 0; x < N; x++) if (!inR[x] && tight[x] == 0) add(x);
                improved = 1; break; }
        }
        if (m > best) { best = m; memcpy(bestR, R, sizeof(int) * m); fprintf(stderr, "it %ld: %d\n", it, best); }
        if (!improved) {
            /* perturb: force in 1-2 random points (prefer low tightness), drop conflicts, refill */
            int k = 1 + (rnd() % 2);
            for (int t = 0; t < k; t++) {
                int x, lim = 2; long tr = 0; do { x = rnd() % N; if (++tr % 200000 == 0) lim++; } while (inR[x] || tight[x] > lim);   /* lim grows: no infinite loop when every outside point has tightness > 2 */
                for (int i = m - 1; i >= 0; i--) if (B(R[i], x) == 0) del(R[i]);
                add(x);
            }
            for (int i = 0; i < N; i++) { int x = perm[(i + rnd()) % N]; if (!inR[x] && tight[x] == 0) add(x); }
            if (m < best - 6) { /* restart from best */ while (m) del(R[m - 1]); for (int i = 0; i < best; i++) add(bestR[i]); }
        }
    }
    fprintf(stderr, "final best %d after %ld iterations\n", best, it);
    printf("# partial ovoid of Q(6,%d), %d points (povoid_ils seed %s)\n", q, best, argv[3]);
    for (int i = 0; i < best; i++) printf("%d\n", bestR[i]);
    return 0;
}
