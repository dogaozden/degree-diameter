/* wsa.c: min-conflict annealing for perfect whisker sets. Each A-point picks one candidate whisker; cost = number
   of free points covered more than once (counted with multiplicity). Cost 0 = perfect cover.
   Usage: wsa instance.txt seconds seed outW.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); double secs = atof(argv[2]); rs ^= (uint64_t)atoi(argv[3]) * 0x9E3779B97F4A7C15ULL;
    int q, nf, na; if (fscanf(f, "%d %d %d", &q, &nf, &na) != 3) return 1;
    int *no = malloc(sizeof(int) * na), *st = malloc(sizeof(int) * (na + 1)); int cap = na * 16, tot = 0;
    int *lid = malloc(sizeof(int) * cap), *pts = malloc(sizeof(int) * (long)cap * q);
    st[0] = 0;
    for (int a = 0; a < na; a++) {
        if (fscanf(f, "%d", &no[a]) != 1) return 1;
        for (int j = 0; j < no[a]; j++) { if (fscanf(f, "%d", &lid[tot]) != 1) return 1; for (int t = 0; t < q; t++) if (fscanf(f, "%d", &pts[(long)tot * q + t]) != 1) return 1; tot++; }
        st[a + 1] = tot;
    }
    int *cov = calloc(nf, sizeof(int)), *ch = malloc(sizeof(int) * na); long cost = 0;
    for (int a = 0; a < na; a++) { ch[a] = st[a] + rnd() % no[a]; for (int t = 0; t < q; t++) { int r = pts[(long)ch[a] * q + t]; if (cov[r]++) cost++; } }
    long best = cost; int *bch = malloc(sizeof(int) * na); for (int a = 0; a < na; a++) bch[a] = ch[a];
    clock_t t0 = clock(); double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = 0.05, T = T0; long it = 0;
    while (cost > 0) {
        if ((it & 0xFFFFF) == 0) { double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break; T = T0 * pow(T1 / T0, el / secs);
            if ((it & 0x3FFFFFF) == 0) fprintf(stderr, "t=%.0f cost=%ld best=%ld T=%.3f\n", el, cost, best, T); }
        it++;
        int a = rnd() % na; if (no[a] < 2) continue;
        int c = st[a] + rnd() % no[a]; if (c == ch[a]) continue;
        int d = 0; int o = ch[a];
        for (int t = 0; t < q; t++) { int r = pts[(long)o * q + t]; if (cov[r] >= 2) d--; }
        for (int t = 0; t < q; t++) { int r = pts[(long)c * q + t]; cov[r]++; }   /* tentative to handle shared points */
        for (int t = 0; t < q; t++) { int r = pts[(long)o * q + t]; cov[r]--; }
        long nc = cost;
        /* recompute delta exactly: cost = sum max(cov-1,0) */
        d = 0;
        for (int t = 0; t < q; t++) { int r = pts[(long)c * q + t]; if (cov[r] >= 2) d++; }   /* new excess from c (approx; o, c disjoint off the A-point) */
        for (int t = 0; t < q; t++) { int r = pts[(long)o * q + t]; if (cov[r] >= 1) d--; }
        nc = cost + d;
        if (d <= 0 || (double)(rnd() >> 11) / 9007199254740992.0 < exp(-d / T)) { ch[a] = c; cost = nc; if (cost < best) { best = cost; for (int b = 0; b < na; b++) bch[b] = ch[b]; } }
        else { for (int t = 0; t < q; t++) { cov[pts[(long)o * q + t]]++; cov[pts[(long)c * q + t]]--; } }
    }
    if (cost == 0) for (int b = 0; b < na; b++) bch[b] = ch[b], best = 0;
    fprintf(stderr, "final best cost %ld after %ld moves\n", best, it);
    /* output: whiskers of the best state with no overcovered point (drop A-points touching overcovered points) */
    for (int r = 0; r < nf; r++) cov[r] = 0;
    for (int a = 0; a < na; a++) for (int t = 0; t < q; t++) cov[pts[(long)bch[a] * q + t]]++;
    FILE *g = fopen(argv[4], "w"); int kept = 0;
    int *used = calloc(nf, sizeof(int));
    for (int a = 0; a < na; a++) { int okk = 1; for (int t = 0; t < q; t++) if (used[pts[(long)bch[a] * q + t]]) okk = 0;
        if (okk) { for (int t = 0; t < q; t++) used[pts[(long)bch[a] * q + t]] = 1; fprintf(g, "%d\n", lid[bch[a]]); kept++; } }
    fclose(g);
    printf("cost %ld, kept whiskers %d of %d\n", best, kept, na);
    return 0;
}
