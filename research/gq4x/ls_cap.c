/* Tabu search for a large point set meeting every line in at most CAP points ("partial CAP-ovoid").

   usage: ls_cap INSTANCE CAP K SECONDS SEED [OUT]
     INSTANCE: first line "n m", then m lines "k p1 ... pk" (points 0..n-1).
   Looks for a set of exactly K points with no line holding more than CAP of them (cost 0), by swap moves that
   minimise cost = sum over lines of max(0, count - CAP). Prints the best cost seen; on success writes the points
   (one per line) to OUT (default stdout) and exits 0. Exit 1 if time runs out.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n, m, CAP, K;
static int *lsz, **lpts;        /* lines */
static int *pdeg, **plines;     /* lines through each point */
static int *cnt, *in, *addc, *remc, *tabu;
static unsigned long long rs;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void line_change(int L, int d) {  /* cnt[L] += d, update addc/remc of its points */
    int old = cnt[L], nw = old + d;
    int a0 = old >= CAP, a1 = nw >= CAP;   /* adding a point to L costs 1 iff cnt >= CAP */
    int r0 = old > CAP, r1 = nw > CAP;     /* removing a point from L saves 1 iff cnt > CAP */
    cnt[L] = nw;
    if (a0 != a1 || r0 != r1)
        for (int i = 0; i < lsz[L]; i++) { int p = lpts[L][i]; addc[p] += a1 - a0; remc[p] += r1 - r0; }
}
static void flip(int p, int d) { in[p] += d; for (int i = 0; i < pdeg[p]; i++) line_change(plines[p][i], d); }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    CAP = atoi(argv[2]); K = atoi(argv[3]); double secs = atof(argv[4]); rs = 0x9E3779B97F4A7C15ULL * (atoi(argv[5]) + 1);
    if (fscanf(f, "%d %d", &n, &m) != 2) return 2;
    lsz = malloc(m * sizeof(int)); lpts = malloc(m * sizeof(int *)); pdeg = calloc(n, sizeof(int));
    for (int j = 0; j < m; j++) {
        if (fscanf(f, "%d", &lsz[j]) != 1) return 2;
        lpts[j] = malloc(lsz[j] * sizeof(int));
        for (int i = 0; i < lsz[j]; i++) { if (fscanf(f, "%d", &lpts[j][i]) != 1) return 2; pdeg[lpts[j][i]]++; }
    }
    fclose(f);
    plines = malloc(n * sizeof(int *)); int *fill = calloc(n, sizeof(int));
    for (int p = 0; p < n; p++) plines[p] = malloc(pdeg[p] * sizeof(int));
    for (int j = 0; j < m; j++) for (int i = 0; i < lsz[j]; i++) { int p = lpts[j][i]; plines[p][fill[p]++] = j; }
    cnt = calloc(m, sizeof(int)); in = calloc(n, sizeof(int)); addc = calloc(n, sizeof(int));
    remc = calloc(n, sizeof(int)); tabu = calloc(n, sizeof(int));
    /* greedy start then random fill to K */
    int *perm = malloc(n * sizeof(int)), size = 0;
    for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < n && size < K; i++) if (addc[perm[i]] == 0) { flip(perm[i], 1); size++; }
    for (int i = 0; i < n && size < K; i++) if (!in[perm[i]]) { flip(perm[i], 1); size++; }
    long cost = 0; for (int j = 0; j < m; j++) if (cnt[j] > CAP) cost += cnt[j] - CAP;
    long best = cost; double t0 = now(), tend = t0 + secs; long it = 0;
    int *viol = malloc(m * sizeof(int)), *cand = malloc(n * sizeof(int));
    while (cost > 0) {
        if ((it & 1023) == 0 && now() > tend) break;
        it++;
        /* pick a random violated line */
        int nv = 0; for (int j = 0; j < m; j++) if (cnt[j] > CAP) viol[nv++] = j;
        int L = viol[rnd() % nv];
        /* remove: a point of S on L, prefer max remc, non-tabu */
        int u = -1, bu = -1000000, nc = 0;
        for (int i = 0; i < lsz[L]; i++) { int p = lpts[L][i]; if (!in[p]) continue;
            int s = remc[p] - (tabu[p] > it ? 1000 : 0);
            if (s > bu) { bu = s; nc = 0; } if (s == bu) cand[nc++] = p; }
        u = cand[rnd() % nc];
        flip(u, -1); cost -= remc[u] + 0; /* recompute exactly below */
        /* add: a point not in S with min addc, non-tabu, != u */
        int ba = 1000000; nc = 0;
        for (int p = 0; p < n; p++) { if (in[p] || p == u) continue;
            int s = addc[p] + (tabu[p] > it ? 1000 : 0);
            if (s < ba) { ba = s; nc = 0; } if (s == ba) cand[nc++] = p; }
        int v = cand[rnd() % nc];
        flip(v, 1);
        tabu[u] = it + 7 + rnd() % 10; tabu[v] = it + 3 + rnd() % 5;
        cost = 0; for (int j = 0; j < m; j++) if (cnt[j] > CAP) cost += cnt[j] - CAP;
        if (cost < best) { best = cost; fprintf(stderr, "it %ld t %.1f best cost %ld\n", it, now() - t0, best); }
    }
    fprintf(stderr, "K=%d final cost %ld best %ld iters %ld time %.1f\n", K, cost, best, it, now() - t0);
    if (cost == 0) {
        FILE *o = argc > 6 ? fopen(argv[6], "w") : stdout;
        for (int p = 0; p < n; p++) if (in[p]) fprintf(o, "%d\n", p);
        if (o != stdout) fclose(o);
        return 0;
    }
    return 1;
}
