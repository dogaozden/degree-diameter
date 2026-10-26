/* c7: simulated annealing over 2-switches of cubic bipartite graphs.
 * Bipartition: A = 0..h-1, B = h..n-1 (h = n/2). Moves replace edges (a,b),(c,d)
 * by (a,d),(c,b), which keeps degree 3 and bipartiteness.
 * Cost = number of unordered pairs at distance > D, computed with bitset balls:
 *   R_k(v) = R_{k-1}(v) | OR_{u in N(v)} R_{k-1}(u).
 * Usage: sa_bip n D iters T0 T1 seed init(0=Haar,1=random) outfile
 * Writes outfile (edge list, 0-based, first line n) as soon as cost hits 0,
 * otherwise writes the best state found at the end.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN/64)

static int n, h, D, W;
static int nb[MAXN][3];
static int ea[MAXN*3/2], eb[MAXN*3/2], m;
static uint64_t curb[MAXN*MAXW], nxtb[MAXN*MAXW];
static int bestnb[MAXN][3];
static uint64_t rs;

static uint64_t rnd(void) { rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27; return rs * 2685821657736338717ULL; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int irand(int k) { return (int)(rnd() % (uint64_t)k); }

static void replace_nb(int v, int old, int nw) {
    for (int k = 0; k < 3; k++) if (nb[v][k] == old) { nb[v][k] = nw; return; }
    fprintf(stderr, "replace failed v=%d old=%d\n", v, old); exit(2);
}
static int has_edge(int a, int b) {
    return nb[a][0] == b || nb[a][1] == b || nb[a][2] == b;
}

static long cost_of(void) {
    for (int v = 0; v < n; v++) for (int w = 0; w < W; w++) curb[v*W+w] = 0;
    for (int v = 0; v < n; v++) curb[v*W + (v>>6)] |= 1ULL << (v & 63);
    for (int step = 0; step < D; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) {
                uint64_t x = curb[v*W+w] | curb[nb[v][0]*W+w] | curb[nb[v][1]*W+w] | curb[nb[v][2]*W+w];
                nxtb[v*W+w] = x;
            }
        }
        memcpy(curb, nxtb, sizeof(uint64_t) * n * W);
    }
    long unreached = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(curb[v*W+w]);
        unreached += n - c;
    }
    return unreached / 2;
}

static void write_graph(const char *fn, int (*g)[3]) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror("fopen"); return; }
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++) for (int k = 0; k < 3; k++)
        if (g[v][k] > v) fprintf(f, "%d %d\n", v, g[v][k]);
    fclose(f);
}

static void init_haar(void) {
    /* H(Z_h, {0,a,b}) with random distinct nonzero a<b */
    int a, b;
    do { a = 1 + irand(h-1); b = 1 + irand(h-1); } while (a == b);
    m = 0;
    for (int i = 0; i < h; i++) {
        int sh[3] = {0, a, b};
        for (int k = 0; k < 3; k++) {
            int j = (i + sh[k]) % h;
            ea[m] = i; eb[m] = h + j; m++;
        }
    }
    for (int v = 0; v < n; v++) for (int k = 0; k < 3; k++) nb[v][k] = -1;
    for (int e = 0; e < m; e++) {
        int a2 = ea[e], b2 = eb[e];
        for (int k = 0; k < 3; k++) if (nb[a2][k] < 0) { nb[a2][k] = b2; break; }
        for (int k = 0; k < 3; k++) if (nb[b2][k] < 0) { nb[b2][k] = a2; break; }
    }
}

static void init_random(void) {
    /* three random perfect matchings A->B, repaired so no pair repeats */
    static int p[3][MAXN/2];
    for (int k = 0; k < 3; k++) for (int i = 0; i < h; i++) p[k][i] = i;
    for (int k = 0; k < 3; k++) {
        for (int i = h-1; i > 0; i--) { int j = irand(i+1); int t = p[k][i]; p[k][i] = p[k][j]; p[k][j] = t; }
    }
    for (int iter = 0; iter < 100000000; iter++) {
        int bad = -1;
        for (int k = 1; k < 3 && bad < 0; k++)
            for (int i = 0; i < h; i++) {
                int conflict = 0;
                for (int l = 0; l < k; l++) if (p[l][i] == p[k][i]) conflict = 1;
                if (conflict) { bad = i; break; }
            }
        if (bad < 0) break;
        int k = 1 + irand(2);
        int j = irand(h), t = p[k][bad]; p[k][bad] = p[k][j]; p[k][j] = t;
    }
    m = 0;
    for (int k = 0; k < 3; k++) for (int i = 0; i < h; i++) { ea[m] = i; eb[m] = h + p[k][i]; m++; }
    for (int v = 0; v < n; v++) for (int k = 0; k < 3; k++) nb[v][k] = -1;
    for (int e = 0; e < m; e++) {
        int a2 = ea[e], b2 = eb[e];
        for (int k = 0; k < 3; k++) if (nb[a2][k] < 0) { nb[a2][k] = b2; break; }
        for (int k = 0; k < 3; k++) if (nb[b2][k] < 0) { nb[b2][k] = a2; break; }
    }
}

/* switch edges i=(a,b), j=(c,d) into (a,d), (c,b) */
static void do_switch(int i, int j, int a, int b, int c, int d) {
    replace_nb(a, b, d); replace_nb(b, a, c); replace_nb(d, c, a); replace_nb(c, d, b);
    ea[i] = a; eb[i] = d; ea[j] = c; eb[j] = b;
}
static void undo_switch(int i, int j, int a, int b, int c, int d) {
    replace_nb(a, d, b); replace_nb(d, a, c); replace_nb(b, c, a); replace_nb(c, b, d);
    ea[i] = a; eb[i] = b; ea[j] = c; eb[j] = d;
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: sa_bip n D iters T0 T1 seed init outfile\n"); return 1; }
    n = atoi(argv[1]); D = atoi(argv[2]);
    long iters = atol(argv[3]);
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    rs = strtoull(argv[6], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    int init = atoi(argv[7]);
    const char *outfn = argv[8];
    if (n > MAXN || (n & 1) || n < 8) { fprintf(stderr, "bad n\n"); return 1; }
    h = n / 2; W = (n + 63) / 64;
    if (init == 0) init_haar(); else init_random();

    long cur = cost_of();
    long best = cur;
    memcpy(bestnb, nb, sizeof(nb));
    fprintf(stderr, "n=%d D=%d init cost=%ld\n", n, D, cur);
    time_t t0 = time(NULL);
    for (long it = 0; it < iters && cur > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = irand(m), j = irand(m);
        if (i == j) continue;
        int a = ea[i], b = eb[i], c = ea[j], d = eb[j];
        if (a == c || b == d || has_edge(a, d) || has_edge(c, b)) continue;
        do_switch(i, j, a, b, c, d);
        long nc = cost_of();
        long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(bestnb, nb, sizeof(nb));
            }
        } else {
            undo_switch(i, j, a, b, c, d);
        }
        if (it % 5000 == 0)
            fprintf(stderr, "it=%ld T=%.3f cur=%ld best=%ld t=%lds\n", it, T, cur, best, (long)(time(NULL)-t0));
    }
    if (best == 0) {
        memcpy(nb, bestnb, sizeof(nb));
        /* rebuild edge list from best nb */
        write_graph(outfn, bestnb);
        fprintf(stderr, "FOUND valid n=%d, wrote %s\n", n, outfn);
    } else {
        write_graph(outfn, bestnb);
    }
    printf("n=%d D=%d best_unordered_unreached=%ld final_cur=%ld\n", n, D, best, cur);
    return best == 0 ? 0 : 3;
}
