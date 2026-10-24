/* povoid_ils.c: iterated local search (ARW-style (1,2)-swaps + random perturbation) for a large partial ovoid of
   Q(6,q) inside H(q): points pairwise non-orthogonal (= pairwise opposite in H(q)).
   usage: povoid_ils HEXFILE seconds seed [init_file] > out.txt   (writes best set, one point index per line) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
int q, N; uint8_t *co;
static inline int B(int a, int b) { const uint8_t *x = co + 7L * a, *y = co + 7L * b;
    int s = x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]; s %= q; if (s < 0) s += q; return s; }
static uint64_t rs; static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int *tight, *inR, *R, m;
static void add(int r) { inR[r] = 1; R[m++] = r; for (int x = 0; x < N; x++) if (x != r && B(x, r) == 0) tight[x]++; }
static void del(int r) { inR[r] = 0; for (int i = 0; i < m; i++) if (R[i] == r) { R[i] = R[--m]; break; } for (int x = 0; x < N; x++) if (x != r && B(x, r) == 0) tight[x]--; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1; q = hdr[0]; N = hdr[1];
    fseek(f, 12 + 4L * N * (q + 1), SEEK_SET); co = malloc(7L * N); if (fread(co, 1, 7L * N, f) != 7L * N) return 1; fclose(f);
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
