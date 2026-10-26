/* safz: annealing over bipartite graphs with max degree 3 in which some edges are frozen. Moves switch two free edges
   (a1 b1, a2 b2) -> (a1 b2, a2 b1), so every degree is kept. Cost = ordered pairs at distance > D (env D, default 7).
   Usage: safz IN seed seconds T0 T1 OUT     IN: "n" then lines "u v f" (f = 1 frozen, 0 free).  Prints FOUND on cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXN 512
#define W 8
static int n, D = 7, nb[MAXN][3], deg[MAXN], col[MAXN], ne, eu[MAXN * 2], ev[MAXN * 2], fz[MAXN * 2], fr[MAXN * 2], nf;
static uint64_t ra[MAXN][W], rb[MAXN][W]; static int nw;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static long cost(void) {
    uint64_t (*cur)[W] = ra, (*nx)[W] = rb;
    for (int x = 0; x < n; x++) { memset(cur[x], 0, nw * 8); cur[x][x >> 6] |= 1ULL << (x & 63); }
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) { const uint64_t *a = cur[nb[x][0]], *b = cur[nb[x][1]], *c = cur[nb[x][2]], *s = cur[x];
            for (int w = 0; w < nw; w++) nx[x][w] = s[w] | a[w] | b[w] | c[w]; }
        uint64_t (*tmp)[W] = cur; cur = nx; nx = tmp;
    }
    long r = 0; for (int x = 0; x < n; x++) for (int w = 0; w < nw; w++) r += __builtin_popcountll(cur[x][w]);
    return (long)n * n - r;
}
static void rebuild(void) {
    for (int x = 0; x < n; x++) { deg[x] = 0; nb[x][0] = nb[x][1] = nb[x][2] = x; }
    for (int i = 0; i < ne; i++) { nb[eu[i]][deg[eu[i]]++] = ev[i]; nb[ev[i]][deg[ev[i]]++] = eu[i]; }
}
static int adj(int a, int b) { for (int j = 0; j < deg[a]; j++) if (nb[a][j] == b) return 1; return 0; }
static void save(const char *p) { FILE *f = fopen(p, "w"); fprintf(f, "%d\n", n); for (int i = 0; i < ne; i++) fprintf(f, "%d %d\n", eu[i], ev[i]); fclose(f); }
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: safz IN seed seconds T0 T1 OUT\n"); return 2; }
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d", &n) != 1) return 2;
    int a, b, z; ne = 0; while (fscanf(f, "%d %d %d", &a, &b, &z) == 3) { eu[ne] = a; ev[ne] = b; fz[ne] = z; ne++; } fclose(f);
    nw = (n + 63) / 64; rebuild();
    for (int i = 0; i < n; i++) col[i] = -1; col[0] = 0; int q[MAXN], h = 0, t = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int j = 0; j < deg[x]; j++) if (col[nb[x][j]] < 0) { col[nb[x][j]] = 1 - col[x]; q[t++] = nb[x][j]; } }
    for (int i = 0; i < ne; i++) { if (col[eu[i]] == 1) { int s = eu[i]; eu[i] = ev[i]; ev[i] = s; } if (!fz[i]) fr[nf++] = i; }
    rng ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; xr();
    double secs = atof(argv[3]), T0 = atof(argv[4]), T1 = atof(argv[5]), cyc = 20.0;
    long c = cost(), best = c; save(argv[6]); printf("n=%d free=%d start %ld\n", n, nf, c); fflush(stdout);
    clock_t st = clock(); long it = 0;
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, fmod(el, cyc) / cyc);
        int i = fr[xr() % nf], j = fr[xr() % nf];
        int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
        if (a1 == a2 || b1 == b2 || adj(a1, b2) || adj(a2, b1)) continue;
        ev[i] = b2; ev[j] = b1;
        for (int k = 0; k < 3; k++) { if (nb[a1][k] == b1) nb[a1][k] = b2; if (nb[a2][k] == b2) nb[a2][k] = b1;
            if (nb[b1][k] == a1) nb[b1][k] = a2; if (nb[b2][k] == a2) nb[b2][k] = a1; }
        long c2 = cost(); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) { c = c2;
            if (c < best) { best = c; save(argv[6]); printf("t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout); if (!best) { printf("FOUND\n"); break; } } }
        else { ev[i] = b1; ev[j] = b2;
            for (int k = 0; k < 3; k++) { if (nb[a1][k] == b2) nb[a1][k] = b1; if (nb[a2][k] == b1) nb[a2][k] = b2;
                if (nb[b1][k] == a2) nb[b1][k] = a1; if (nb[b2][k] == a1) nb[b2][k] = a2; } }
    }
    printf("end best %ld its %ld\n", best, it); return 0;
}
