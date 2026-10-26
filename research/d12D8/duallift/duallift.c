/* Duality-hop lift of the split Cayley hexagon H(q), q = 3^e (job own-12-8, 2026-10-26).
   L levels, each a copy of the incidence graph I(H) (hexagon edges inside a level, voltage 0). delta is a duality of H
   (points -> lines). Every point x carries two hop edges  (x, j) ~ (delta(x), j + t1(x))  and  (x, j) ~ (delta(x), j + t2(x))
   (t1 != t2 in Z_L), so every vertex has degree q+1+2 and the graph is a Z_L-cover of I(H) + the double matching x~delta(x).
   Order L * 2N(q). The level shift j -> j+1 is an automorphism, so sources (s, 0) suffice.
   Usage: duallift HEX DELTA L VOLT check STEP [T]      bit-parallel BFS (depth <= D=8) from base vertices 0, STEP, 2STEP, ...:
                                                          prints the number of (source, target) pairs at distance > 8.
          duallift HEX DELTA L VOLT edges OUT           writes the edge list ("n" then "u v"); vertex (y, j) = j*2n + y.
   VOLT: text file with n lines "t1 t2", or "rand:SEED". (build: cc -O3 -march=native -fopenmp -o duallift duallift.c) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
static int q, n, nl, L; static long N1, nv; static int *LP, *PL, *dl, *idl, *t1, *t2;
static int nbrs(long x, long *o) {
    long j = x / N1; int y = x % N1, m = 0;
    if (y < n) { for (int i = 0; i <= q; i++) o[m++] = j * N1 + n + PL[(long)y * (q + 1) + i];
        o[m++] = ((j + t1[y]) % L) * N1 + n + dl[y]; o[m++] = ((j + t2[y]) % L) * N1 + n + dl[y]; }
    else { int l = y - n; for (int i = 0; i <= q; i++) o[m++] = j * N1 + LP[(long)l * (q + 1) + i];
        int x0 = idl[l]; o[m++] = ((j - t1[x0] + L) % L) * N1 + x0; o[m++] = ((j - t2[x0] + L) % L) * N1 + x0; }
    return m;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d", &q, &n, &nl) != 3) return 2;
    LP = malloc(sizeof(int) * (long)nl * (q + 1)); PL = malloc(sizeof(int) * (long)n * (q + 1)); int *pc = calloc(n, sizeof(int));
    for (long l = 0; l < nl; l++) for (int i = 0; i <= q; i++) { int p; if (fscanf(f, "%d", &p) != 1) return 2; LP[l * (q + 1) + i] = p; PL[(long)p * (q + 1) + pc[p]++] = l; }
    fclose(f);
    dl = malloc(sizeof(int) * n); idl = malloc(sizeof(int) * n); f = fopen(argv[2], "r");
    for (int i = 0; i < n; i++) if (fscanf(f, "%d", &dl[i]) != 1) return 3; fclose(f);
    for (int i = 0; i < n; i++) idl[dl[i]] = i;
    L = atoi(argv[3]); t1 = malloc(sizeof(int) * n); t2 = malloc(sizeof(int) * n);
    if (!strncmp(argv[4], "rand:", 5)) { srand(atoi(argv[4] + 5)); for (int i = 0; i < n; i++) { t1[i] = rand() % L; do t2[i] = rand() % L; while (t2[i] == t1[i]); } }
    else { f = fopen(argv[4], "r"); for (int i = 0; i < n; i++) if (fscanf(f, "%d %d", &t1[i], &t2[i]) != 2) return 4; fclose(f); }
    for (int i = 0; i < n; i++) if (t1[i] == t2[i] || t1[i] < 0 || t2[i] < 0 || t1[i] >= L || t2[i] >= L) { printf("bad voltages at %d\n", i); return 5; }
    N1 = 2L * n; nv = (long)L * N1;
    if (!strcmp(argv[5], "edges")) {
        FILE *o = fopen(argv[6], "w"); fprintf(o, "%ld\n", nv); long nb[32];
        for (long x = 0; x < nv; x++) { int m = nbrs(x, nb); for (int i = 0; i < m; i++) if (nb[i] > x) fprintf(o, "%ld %ld\n", x, nb[i]); }
        fclose(o); return 0;
    }
    if (!strcmp(argv[5], "diag")) {   /* BFS from (s,0); misses tabulated by hexagon distance d(s,w) [and d(s, delta^2 w)], class of w */
        long s0 = atol(argv[6]); int8_t *d = malloc(nv); memset(d, -1, nv); long *qq = malloc(nv * 8), h = 0, t = 0; long nb[32];
        d[s0] = 0; qq[t++] = s0;
        while (h < t) { long x = qq[h++]; if (d[x] >= 9) continue; int m = nbrs(x, nb); for (int i = 0; i < m; i++) if (d[nb[i]] < 0) { d[nb[i]] = d[x] + 1; qq[t++] = nb[i]; } }
        int8_t *dh = malloc(N1); memset(dh, -1, N1); h = t = 0; dh[s0] = 0; qq[t++] = s0;   /* hexagon distances (level 0 only) */
        while (h < t) { long x = qq[h++]; int m = nbrs(x, nb); for (int i = 0; i < q + 1; i++) if (dh[nb[i]] < 0) { dh[nb[i]] = dh[x] + 1; qq[t++] = nb[i]; } }
        long tab[8][2] = {{0}}, lev[64] = {0}; long tot = 0;
        for (long x = 0; x < nv; x++) if (d[x] < 0 || d[x] > 8) { int y = x % N1; tab[dh[y]][y >= n]++; lev[x / N1 < 64 ? x / N1 : 63]++; tot++; }
        printf("source %ld (%s): %ld far vertices\n d_H(s,w)  w point  w line\n", s0, s0 < n ? "point" : "line", tot);
        for (int k = 0; k <= 6; k++) printf("   %d      %6ld  %6ld\n", k, tab[k][0], tab[k][1]);
        printf(" by level:"); for (int j = 0; j < L && j < 64; j++) printf(" %ld", lev[j]); printf("\n");
        return 0;
    }
    int step = atoi(argv[6]); int T = argc > 7 ? atoi(argv[7]) : 1; omp_set_num_threads(T);
    long nsrc = (N1 + step - 1) / step; long *src = malloc(nsrc * 8); for (long i = 0; i < nsrc; i++) src[i] = i * step;
    /* adjacency table (faster than recomputing): */
    int deg = q + 3; long *adj = malloc(nv * deg * 8); long nb[32];
    for (long x = 0; x < nv; x++) { int m = nbrs(x, nb); if (m != deg) { printf("degree %d at %ld\n", m, x); return 6; } memcpy(adj + x * deg, nb, deg * 8); }
    uint64_t *vis = malloc(nv * 8), *fr = malloc(nv * 8), *nx = malloc(nv * 8);
    long miss = 0, worst = 0, worst_s = -1; int maxlev = 0;
    for (long k0 = 0; k0 < nsrc; k0 += 64) {
        int ns = nsrc - k0 < 64 ? nsrc - k0 : 64; uint64_t full = ns == 64 ? ~0ULL : (1ULL << ns) - 1;
        memset(vis, 0, nv * 8); memset(fr, 0, nv * 8);
        for (int k = 0; k < ns; k++) { vis[src[k0 + k]] |= 1ULL << k; fr[src[k0 + k]] |= 1ULL << k; }
        for (int lev = 1; lev <= 8; lev++) {
            #pragma omp parallel for schedule(static)
            for (long x = 0; x < nv; x++) { uint64_t a = 0; const long *p = adj + x * deg; for (int i = 0; i < deg; i++) a |= fr[p[i]]; nx[x] = a & ~vis[x]; }
            #pragma omp parallel for schedule(static)
            for (long x = 0; x < nv; x++) vis[x] |= nx[x];
            uint64_t *tmp = fr; fr = nx; nx = tmp;
        }
        long cnt[64] = {0};
        for (long x = 0; x < nv; x++) { uint64_t u = ~vis[x] & full; while (u) { cnt[__builtin_ctzll(u)]++; u &= u - 1; } }
        for (int k = 0; k < ns; k++) { miss += cnt[k]; if (cnt[k] > worst) { worst = cnt[k]; worst_s = src[k0 + k]; } }
    }
    printf("L=%d n_vertices=%ld sources=%ld (step %d): pairs at distance > 8: %ld (worst source %ld: %ld)\n", L, nv, nsrc, step, miss, worst_s, worst);
    return 0;
}
