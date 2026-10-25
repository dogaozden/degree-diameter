/* nbw.c: non-backtracking walk counts in a base graph built on the split Cayley hexagon H(q).
 * For a lift over a group of order m, a pair (v, w) of base vertices can be covered (every fibre element of w within
 * distance D of (v, e)) only if there are at least m reduced walks v -> w of length <= D with the right parity, since a
 * walk and its reduction have the same voltage. So min_{v,w} W(v,w) bounds m for every voltage assignment.
 * Designs (extra edges on top of the incidence graph, points 0..N-1, lines N..2N-1):
 *   m2   two random bijections sigma1, sigma2: points -> lines
 *   par  one random bijection sigma, doubled (two parallel edges)
 *   inc2 two of the q+1 incidences at each vertex doubled (a random 2-factor of the incidence graph, doubled)
 *   m1   one random bijection (degree q+2)
 * Usage: nbw HEXBIN design D nsrc seed     (prints a histogram of W over sampled sources, per target type) */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int q, N, NV; static int *deg, *nb; static int MAXD = 32;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void add_edge(int a, int b) { nb[a * MAXD + deg[a]++] = b; nb[b * MAXD + deg[b]++] = a; }
static void shuffle(int *a, int n) { for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1), t = a[i]; a[i] = a[j]; a[j] = t; } }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: nbw HEXBIN design D nsrc seed\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int L; fread(&q, 4, 1, f); fread(&N, 4, 1, f); fread(&L, 4, 1, f);
    int *lp = malloc(sizeof(int) * L * (q + 1)); fread(lp, 4, L * (q + 1), f); fclose(f);
    const char *design = argv[2]; int D = atoi(argv[3]), nsrc = atoi(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    NV = 2 * N; deg = calloc(NV, sizeof(int)); nb = malloc(sizeof(int) * NV * MAXD);
    for (int l = 0; l < L; l++) for (int i = 0; i <= q; i++) add_edge(lp[l * (q + 1) + i], N + l);
    int *perm = malloc(sizeof(int) * N);
    if (!strcmp(design, "m2") || !strcmp(design, "m1") || !strcmp(design, "par")) {
        int k = strcmp(design, "m2") ? 1 : 2;
        for (int r = 0; r < k; r++) { for (int i = 0; i < N; i++) perm[i] = i; shuffle(perm, N); for (int i = 0; i < N; i++) add_edge(i, N + perm[i]); if (!strcmp(design, "par")) for (int i = 0; i < N; i++) add_edge(i, N + perm[i]); }
    } else if (!strcmp(design, "inc2")) {
        /* a 2-factor: union of two perfect matchings of the incidence graph, found greedily from random line orders */
        for (int r = 0; r < 2; r++) {
            /* random perfect matching via repeated augmenting (simple Hopcroft-Karp-free: random greedy + augment) */
            int *mp = malloc(sizeof(int) * N), *ml = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) mp[i] = ml[i] = -1;
            int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i; shuffle(ord, N);
            int *par = malloc(sizeof(int) * NV), *qq = malloc(sizeof(int) * NV);
            for (int ii = 0; ii < N; ii++) {
                int p = ord[ii]; /* BFS for an augmenting path from the free point p (Kuhn), avoiding edges already doubled */
                for (int i = 0; i < N; i++) par[i] = -2;           /* par[l] = point from which line l was reached */
                int h = 0, t = 0; qq[t++] = p; int end = -1;
                while (h < t && end < 0) {
                    int x = qq[h++];
                    for (int j = 0; j < q + 1 && end < 0; j++) { int y = nb[x * MAXD + j], l = y - N; if (par[l] != -2) continue;
                        int dup = 0; for (int jj = q + 1; jj < deg[x]; jj++) if (nb[x * MAXD + jj] == y) dup = 1; if (dup) continue;
                        par[l] = x; if (ml[l] < 0) end = l; else qq[t++] = ml[l]; }
                }
                if (end < 0) { fprintf(stderr, "no augmenting path\n"); return 1; }
                for (int l = end;;) { int x = par[l], prev = mp[x]; mp[x] = l; ml[l] = x; if (x == p) break; l = prev; }
            }
            for (int i = 0; i < N; i++) add_edge(i, N + mp[i]);
            free(mp); free(ml); free(ord); free(par); free(qq);
        }
    } else { fprintf(stderr, "unknown design\n"); return 2; }
    /* NB walk counts by arc DP from each sampled source */
    int maxdeg = 0; for (int v = 0; v < NV; v++) if (deg[v] > maxdeg) maxdeg = deg[v];
    int64_t *cur = calloc((size_t)NV * MAXD, 8), *nxt = calloc((size_t)NV * MAXD, 8), *W = calloc(NV, 8);
    /* arc (x, j): last step went to nb[x][j] from x. Count walks ending at head with its tail */
    /* reverse index: for arc x->y (slot j at x), the reverse arc slot at y */
    int *rev = malloc(sizeof(int) * NV * MAXD);
    for (int x = 0; x < NV; x++) for (int j = 0; j < deg[x]; j++) { int y = nb[x * MAXD + j]; int jj; /* parallel arcs: pair the k-th copy */
            int kth = 0; for (int t = 0; t < j; t++) if (nb[x * MAXD + t] == y) kth++;
            for (jj = 0; jj < deg[y]; jj++) if (nb[y * MAXD + jj] == x && kth-- == 0) break; rev[x * MAXD + j] = jj; }
    long hist[3][200] = {{0}}; int64_t mn[3] = {INT64_MAX, INT64_MAX, INT64_MAX};
    for (int s = 0; s < nsrc; s++) {
        int v0 = (int)(rnd() % NV); if (s == 0) v0 = 0; if (s == 1) v0 = N;
        memset(W, 0, 8 * NV); W[v0] = 1;
        memset(cur, 0, 8 * (size_t)NV * MAXD);
        for (int j = 0; j < deg[v0]; j++) cur[v0 * MAXD + j] = 1; /* arcs leaving v0, length 1 */
        for (int len = 1; len <= D; len++) {
            memset(nxt, 0, 8 * (size_t)NV * MAXD);
            for (int x = 0; x < NV; x++) for (int j = 0; j < deg[x]; j++) { int64_t c = cur[x * MAXD + j]; if (!c) continue;
                    int y = nb[x * MAXD + j];
                    W[y] += ((len & 1) == ((y < N) != (v0 < N))) ? c : 0;
                    if (len < D) { int r = rev[x * MAXD + j]; for (int k = 0; k < deg[y]; k++) if (k != r) nxt[y * MAXD + k] += c; } }
            int64_t *t = cur; cur = nxt; nxt = t;
        }
        for (int w = 0; w < NV; w++) {
            if (w == v0) continue;
            int type = (v0 < N) == (w < N) ? ((v0 < N) ? 0 : 2) : 1; /* 0 point-point, 1 mixed, 2 line-line */
            int64_t c = W[w]; if (c < mn[type]) mn[type] = c; int b = c < 199 ? (int)c : 199; hist[type][b]++;
        }
    }
    const char *nm[3] = {"point-point", "point-line", "line-line"};
    printf("q=%d design=%s D=%d sources=%d maxdeg=%d\n", q, design, D, nsrc, maxdeg);
    for (int t = 0; t < 3; t++) {
        long tot = 0; for (int b = 0; b < 200; b++) tot += hist[t][b]; if (!tot) continue;
        printf("%s: min W = %lld; quantiles:", nm[t], (long long)mn[t]);
        long acc = 0; double qs[] = {0.0001, 0.001, 0.01, 0.1, 0.5}; int qi = 0;
        for (int b = 0; b < 200 && qi < 5; b++) { acc += hist[t][b]; while (qi < 5 && acc >= qs[qi] * tot) { printf(" %g%%:%d", qs[qi] * 100, b); qi++; } }
        printf("\n");
    }
    return 0;
}
