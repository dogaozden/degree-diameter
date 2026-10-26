/* tsa (card c7): cage-style tree completion for the (3,7) bipartite search. Derived from research/d3D7/sa3.c.
   Fixed part: the Moore tree of depth 5 around an edge uv: 126 vertices, 125 tree edges (frozen, never switched).
   Each vertex at depth < 5 gets 2 children, so leaves (depth 5) have 2 free stubs; the (n-126)/2 extra vertices per
   colour have 3 free stubs. A random simple completion (matching of colour-A stubs to colour-B stubs) is made first;
   then only the free edges are switched (edge switch keeps the graph cubic, bipartite and simple).
   Cost = ordered pairs at distance > D (D = 7)  +  LAMBDA * girth deficiency.
   Girth deficiency (only if R > 0): sum over x of (3*2^R - 2 - |B_R(x)|), zero iff girth > 2R for the bipartite cubic
   graph (R = 4: girth >= 10; R = 5: girth 12).
   Vertex labels: colour A = 0..n/2-1, colour B = n/2..n-1 (edges (a, b) with a in A, b in B).
   Usage: tsa n seed seconds [T0 T1 out.edges]     env: D (7), R (0), LAMBDA (0)
   Prints "FOUND" and stops when the distance cost reaches 0; writes out.edges whenever the best distance cost improves. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 512
#define W ((MAXN + 63) / 64)
static int n, m, D = 7, R = 0, nb[MAXN][3], ea[MAXN * 3 / 2], eb[MAXN * 3 / 2], ne, ntree;
static double LAMBDA = 0.0;
static uint64_t ra[MAXN][W], rb[MAXN][W];
static int nw;

static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static double cost(long *dist, long *def) {
    uint64_t (*cur)[W] = ra, (*nx)[W] = rb;
    for (int x = 0; x < n; x++) { memset(cur[x], 0, nw * 8); cur[x][x >> 6] |= 1ULL << (x & 63); }
    long sumR = 0;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) {
            const uint64_t *a = cur[nb[x][0]], *b = cur[nb[x][1]], *c = cur[nb[x][2]], *s = cur[x];
            for (int w = 0; w < nw; w++) nx[x][w] = s[w] | a[w] | b[w] | c[w];
        }
        uint64_t (*tmp)[W] = cur; cur = nx; nx = tmp;
        if (R && t + 1 == R)
            for (int x = 0; x < n; x++) for (int w = 0; w < nw; w++) sumR += __builtin_popcountll(cur[x][w]);
    }
    long reached = 0;
    for (int x = 0; x < n; x++) for (int w = 0; w < nw; w++) reached += __builtin_popcountll(cur[x][w]);
    *dist = (long)n * n - reached;
    *def = R ? (long)n * (3L * (1L << R) - 2) - sumR : 0;
    return (double)*dist + LAMBDA * (double)*def;
}

static void rebuild(void) {
    int dg[MAXN] = {0};
    for (int i = 0; i < ne; i++) { nb[ea[i]][dg[ea[i]]++] = eb[i]; nb[eb[i]][dg[eb[i]]++] = ea[i]; }
}
static int adj(int a, int b) { return nb[a][0] == b || nb[a][1] == b || nb[a][2] == b; }

/* Fixed Moore tree around edge (u,v) plus random completion of the free stubs. */
static void build(int k) {
    int tcol[130], tdep[130], ntv = 2, tE[130][2], nte = 0, q[130], qh = 0, qt = 0;
    int fid[130], fcol[MAXN] = {0}, fdeg[MAXN] = {0}, cA = 0, cB = 0;
    tcol[0] = 0; tdep[0] = 0; tcol[1] = 1; tdep[1] = 0;
    tE[nte][0] = 0; tE[nte][1] = 1; nte++;
    q[qt++] = 0; q[qt++] = 1;
    while (qh < qt) {
        int x = q[qh++];
        if (tdep[x] >= 5) continue;
        for (int j = 0; j < 2; j++) {
            int y = ntv++;
            tcol[y] = 1 - tcol[x]; tdep[y] = tdep[x] + 1;
            tE[nte][0] = x; tE[nte][1] = y; nte++;
            q[qt++] = y;
        }
    }
    /* ntv = 126, nte = 125 for depth 5 */
    for (int x = 0; x < ntv; x++) { fid[x] = tcol[x] == 0 ? cA++ : m + cB++; fcol[fid[x]] = tcol[x]; }
    for (; cA < m; cA++) fcol[cA] = 0;
    for (; cB < m; cB++) fcol[m + cB] = 1;
    ne = 0;
    for (int e = 0; e < nte; e++) {
        int f1 = fid[tE[e][0]], f2 = fid[tE[e][1]];
        int a = fcol[f1] == 0 ? f1 : f2, b = fcol[f1] == 0 ? f2 : f1;
        ea[ne] = a; eb[ne] = b; ne++; fdeg[f1]++; fdeg[f2]++;
    }
    ntree = ne;
    (void)k;
    for (;;) {
        int As[MAXN], Bs[MAXN], na = 0, nbs = 0;
        for (int x = 0; x < n; x++) for (int f = fdeg[x]; f < 3; f++) { if (fcol[x] == 0) As[na++] = x; else Bs[nbs++] = x; }
        for (int i = nbs - 1; i > 0; i--) { int j = xr() % (i + 1); int t = Bs[i]; Bs[i] = Bs[j]; Bs[j] = t; }
        ne = ntree;
        for (int i = 0; i < na; i++) { ea[ne] = As[i]; eb[ne] = Bs[i]; ne++; }
        int ok = 1;
        for (int i = 0; i < ne && ok; i++) for (int j = i + 1; j < ne; j++) if (ea[i] == ea[j] && eb[i] == eb[j]) { ok = 0; break; }
        if (ok) break;
    }
    rebuild();
}

static void save(const char *path) {
    FILE *f = fopen(path, "w"); fprintf(f, "%d\n", n);
    for (int i = 0; i < ne; i++) fprintf(f, "%d %d\n", ea[i], eb[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: tsa n seed seconds [T0] [T1] [out.edges]\n"); return 2; }
    n = atoi(argv[1]); m = n / 2;
    if (n % 2 || n < 126 || n > MAXN) { fprintf(stderr, "n must be even, 126 <= n <= %d\n", MAXN); return 2; }
    rng ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[3]), T0 = argc > 4 ? atof(argv[4]) : 2.0, T1 = argc > 5 ? atof(argv[5]) : 0.05;
    const char *out = argc > 6 ? argv[6] : "best.edges";
    if (getenv("D")) D = atoi(getenv("D"));
    if (getenv("R")) R = atoi(getenv("R"));
    if (getenv("LAMBDA")) LAMBDA = atof(getenv("LAMBDA"));
    nw = (n + 63) / 64;
    build((n - 126) / 2);
    long dist, def;
    double c = cost(&dist, &def);
    long bestd = dist;
    save(out);
    printf("n %d tree_edges %d free_edges %d start dist %ld def %ld\n", n, ntree, ne - ntree, dist, def);
    fflush(stdout);
    clock_t st = clock(); double cyc = 20.0; long it = 0;
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC;
        if (el > secs) break;
        double fr = fmod(el, cyc) / cyc, T = T0 * pow(T1 / T0, fr);
        int i = ntree + xr() % (ne - ntree), j = ntree + xr() % (ne - ntree);
        if (i == j) continue;
        int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
        if (a1 == a2 || b1 == b2 || adj(a1, b2) || adj(a2, b1)) continue;
        eb[i] = b2; eb[j] = b1;
        for (int k = 0; k < 3; k++) { if (nb[a1][k] == b1) nb[a1][k] = b2; if (nb[a2][k] == b2) nb[a2][k] = b1;
                                      if (nb[b1][k] == a1) nb[b1][k] = a2; if (nb[b2][k] == a2) nb[b2][k] = a1; }
        long d2, f2; double c2 = cost(&d2, &f2); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) {
            c = c2; dist = d2; def = f2;
            if (dist < bestd) {
                bestd = dist; save(out);
                printf("t=%.1f it=%ld best dist %ld (def %ld)\n", el, it, bestd, def); fflush(stdout);
                if (bestd == 0) { printf("FOUND\n"); break; }
            }
        } else {
            eb[i] = b1; eb[j] = b2;
            for (int k = 0; k < 3; k++) { if (nb[a1][k] == b2) nb[a1][k] = b1; if (nb[a2][k] == b1) nb[a2][k] = b2;
                                          if (nb[b1][k] == a2) nb[b1][k] = a1; if (nb[b2][k] == a1) nb[b2][k] = a2; }
        }
    }
    printf("end best dist %ld its %ld\n", bestd, it);
    return 0;
}
