/* x5gen.c: the 5-level polygon cover of H(q) (table construction for Delta = q+3, D = 7) with both matchings equal
   to a duality phi of H(q) (q = 3^e), plus hubs on the absolute flags of phi.  d10D7 job (Opus), 2026-10-24.
   Vertices (v, i), v a point or line of H(q), i in Z5:
     (p,i) ~ (l,i) for p on l;  (p,i) ~ (phi(p), i+1) and (p,i) ~ (phi(p), i+2)   [sigma_1 = sigma_2 = phi]
   Freed absolute flag (p, l = phi(p), phi(l) = p, p on l): delete the 2 extra edges of p at all levels (10 edges),
   add line-side hubs za, zb ~ (p,i) for all i and point-side hubs z1, z2 ~ (l,i) for all i: +4 vertices.
   The duality maps S'(p) onto S(l), so the type-4 routes of the exp2 README cover every freed source at both shifted
   levels; same-side hubs are linked by the hub graph (line-side hubs j ~ point-side hubs k, from a file).
   Usage: x5gen HEXBIN PHI ABS HUBGRAPH OUT.edges   (HUBGRAPH: "H m" then m lines "j k", 0 <= j,k < H = 2*#abs) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0], N = hdr[1], Q1 = q + 1;
    int *LP = malloc(sizeof(int) * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    int *phi = malloc(sizeof(int) * 2 * N); f = fopen(argv[2], "rb"); if (fread(phi, sizeof(int), 2 * N, f) != (size_t)2 * N) return 1; fclose(f);
    int K = 0, *fp = malloc(sizeof(int) * 4096), *flp = malloc(sizeof(int) * 4096), a, b;
    f = fopen(argv[3], "r"); while (fscanf(f, "%d %d", &a, &b) == 2) { fp[K] = a; flp[K] = b; K++; } fclose(f);
    char *freed = calloc(N, 1); for (int k = 0; k < K; k++) { freed[fp[k]] = 1; if (phi[fp[k]] != N + flp[k] || phi[N + flp[k]] != fp[k]) { fprintf(stderr, "flag %d not absolute\n", k); return 1; } }
    int H, m; f = fopen(argv[4], "r"); if (fscanf(f, "%d %d", &H, &m) != 2 || H != 2 * K) { fprintf(stderr, "hub graph must have 2K = %d hubs per side\n", 2 * K); return 1; }
    long n = 10L * N + 4L * K;
    FILE *o = fopen(argv[5], "w"); fprintf(o, "%ld\n", n); long E = 0;
    #define ID(v, i) ((long)(i) * 2 * N + (v))
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + l, i)); E++; } }
    for (int p = 0; p < N; p++) { if (freed[p]) continue; for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(phi[p], (i + 1) % 5)); fprintf(o, "%ld %ld\n", ID(p, i), ID(phi[p], (i + 2) % 5)); E += 2; } }
    /* hubs: line-side hub h (0..2K-1) = 10N + h  (h = 2k, 2k+1 on freed point k); point-side hub h = 10N + 2K + h */
    for (int k = 0; k < K; k++) for (int s = 0; s < 2; s++) for (int i = 0; i < 5; i++) {
        fprintf(o, "%ld %ld\n", 10L * N + 2 * k + s, ID(fp[k], i));
        fprintf(o, "%ld %ld\n", 10L * N + 2L * K + 2 * k + s, ID(N + flp[k], i)); E += 2; }
    for (int e = 0; e < m; e++) { int j, k; if (fscanf(f, "%d %d", &j, &k) != 2) return 1; fprintf(o, "%ld %ld\n", 10L * N + j, 10L * N + 2L * K + k); E++; }
    fclose(f); fclose(o);
    fprintf(stderr, "q=%d N=%d K=%d n=%ld edges=%ld\n", q, N, K, n, E);
    return 0;
}
