/* BFS in Omega B_1 (same graph and vertex ids as omega.c) without writing the edge list: neighbours are computed from the
   hexagon, so the 14M- and 36M-vertex graphs of the thesis fit in memory. Also checks the degrees of every vertex.
   Usage: omega_bfs HEX TYPES READING SOURCE [SIGMA]       prints eccentricity, counts per distance, and the first vertex
   found at the largest distance (decoded: copy, block, point/line label; or new vertex (t, bar, k)). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int q, n, nl, al, reading; static long N1, C, base, nv; static const char *types;
static int *PL, *LP, *sig, *isig;     /* PL[p*(q+1)+i]: lines on point p; LP[l*(q+1)+i]: points on line l */
static void cs(int a, int bar, int k, int *c) {
    if (a) { if (!bar) { c[0] = (k + 4) % 5; c[1] = (k + 1) % 5; } else { c[0] = (k + 2) % 5; c[1] = (k + 3) % 5; } }
    else   { if (!bar) { c[0] = (k + 3) % 5; c[1] = (k + 4) % 5; } else { c[0] = (k + 4) % 5; c[1] = (k + 1) % 5; } }
}
static long hubloc(int a, int bar, int t) {   /* local vertex of B_1 that hub (t,bar,.) uses in a block of type a */
    if (reading == 1) { int online = a ? !bar : bar; return online ? n + sig[t] : t; }
    return bar ? n + t : t;
}
static int nbrs(long x, long *out) {
    int m = 0;
    if (x < base) {
        long c = x / N1, v = x % N1; int B = c / 5, j = c % 5, a = types[B] == 'a';
        if (v < n) for (int i = 0; i <= q; i++) out[m++] = c * N1 + n + PL[v * (q + 1) + i];
        else for (int i = 0; i <= q; i++) out[m++] = c * N1 + LP[(v - n) * (q + 1) + i];
        /* which hubs use (c,v)? a hub (t,bar,k) uses local hubloc(a,bar,t) in copies cs(a,bar,k) */
        for (int bar = 0; bar < 2; bar++) {
            long t;
            if (reading == 1) { int online = a ? !bar : bar; if (online != (v >= n)) continue; t = online ? isig[v - n] : v; }
            else { if (bar != (v >= n)) continue; t = bar ? v - n : v; }
            for (int k = 0; k < 5; k++) { int cc[2]; cs(a, bar, k, cc); if (cc[0] == j || cc[1] == j) out[m++] = base + 10 * t + 5 * bar + k; }
        }
    } else {
        long h = x - base; int t = h / 10, bar = (h % 10) / 5, k = h % 5;
        for (int B = 0; B < al; B++) { int a = types[B] == 'a', cc[2]; cs(a, bar, k, cc);
            for (int i = 0; i < 2; i++) out[m++] = (5L * B + cc[i]) * N1 + hubloc(a, bar, t); }
    }
    return m;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d", &q, &n, &nl) != 3) return 2;
    LP = malloc(sizeof(int) * (long)nl * (q + 1)); PL = malloc(sizeof(int) * (long)n * (q + 1)); int *pc = calloc(n, sizeof(int));
    for (long l = 0; l < nl; l++) for (int i = 0; i <= q; i++) { int p; if (fscanf(f, "%d", &p) != 1) return 2; LP[l * (q + 1) + i] = p; PL[(long)p * (q + 1) + pc[p]++] = l; }
    fclose(f);
    types = argv[2]; reading = atoi(argv[3]); long src = atol(argv[4]); al = strlen(types);
    sig = malloc(sizeof(int) * n); isig = malloc(sizeof(int) * n); for (int t = 0; t < n; t++) sig[t] = t;
    if (argc > 5) { FILE *g = fopen(argv[5], "r"); for (int t = 0; t < n; t++) if (fscanf(g, "%d", &sig[t]) != 1) return 3; fclose(g); }
    for (int t = 0; t < n; t++) isig[sig[t]] = t;
    N1 = 2L * n; C = 5L * al; base = C * N1; nv = base + 10L * n;
    printf("Omega: q=%d types=%s reading=%d: %ld vertices (%ld copies of %ld + %ld new)\n", q, types, reading, nv, C, N1, 10L * n);
    long nb[64]; int mind = 99, maxd = 0; long nedge2 = 0;
    for (long x = 0; x < nv; x++) { int m = nbrs(x, nb); if (m < mind) mind = m; if (m > maxd) maxd = m; nedge2 += m; }
    printf("degrees: min %d max %d, edges %ld\n", mind, maxd, nedge2 / 2);
    int8_t *d = malloc(nv); memset(d, -1, nv); long *qq = malloc(nv * 8), h = 0, t = 0; d[src] = 0; qq[t++] = src;
    while (h < t) { long x = qq[h++]; int m = nbrs(x, nb); for (int i = 0; i < m; i++) if (d[nb[i]] < 0) { d[nb[i]] = d[x] + 1; qq[t++] = nb[i]; } }
    if (t != nv) { printf("unreached %ld\n", nv - t); return 1; }
    long cnt[64] = {0}; int ecc = 0; for (long x = 0; x < nv; x++) { cnt[d[x]]++; if (d[x] > ecc) ecc = d[x]; }
    printf("source %ld: eccentricity %d; counts", src, ecc); for (int k = 0; k <= ecc; k++) printf(" %ld", cnt[k]); printf("\n");
    long far = -1; for (long x = 0; x < nv; x++) if (d[x] == ecc) { far = x; break; }
    if (far < base) printf("far vertex %ld = copy %ld (block %ld, type %c), %s %ld\n", far, far / N1, far / N1 / 5, types[far / N1 / 5],
                           far % N1 < n ? "point" : "line", far % N1 < n ? far % N1 : far % N1 - n);
    else printf("far vertex %ld = new (t=%ld, bar=%ld, k=%ld)\n", far, (far - base) / 10, (far - base) % 10 / 5, (far - base) % 5);
    return 0;
}
