/* x5gen.c: the 5-level polygon cover of H(q) (table construction for Delta = q+3, D = 7) with both matchings equal
   to a duality phi of H(q) (q = 3^e), plus hubs on the absolute flags of phi.  d10D7 job (Opus), 2026-10-24.
   Vertices (v, i), v a point or line of H(q), i in Z5:
     (p,i) ~ (l,i) for p on l;  (p,i) ~ (phi(p), i+1) and (p,i) ~ (phi(p), i+2)   [sigma_1 = sigma_2 = phi]
   Freed absolute flag (p, l = phi(p), phi(l) = p, p on l): delete the 2 extra edges of p at all levels (10 edges),
   add line-side hubs za, zb ~ (p,i) for all i and point-side hubs z1, z2 ~ (l,i) for all i: +4 vertices.
   The duality maps S'(p) onto S(l), so the type-4 routes of the exp2 README cover every freed source at both shifted
   levels; same-side hubs are linked by the hub graph (line-side hubs j ~ point-side hubs k, from a file).
   Usage: x5gen HEXBIN SOL HUBGRAPH OUT.edges
     SOL: d7hex solution file (M on points = sigma_1 = sigma_2, freed points; its hub edges are ignored);
     HUBGRAPH: "H m" then m lines "j k" (line-side hub j ~ point-side hub k, 0 <= j,k < H = 2K). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0], N = hdr[1], Q1 = q + 1;
    int *LP = malloc(sizeof(int) * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    /* the solution file (d7hex format): "d7hex q N K n", "freed p1..pK", "hubedges m ..." (ignored), then M[0..N-1] */
    int K = 0, nn, kk, qq, nv; char w[32];
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "d7hex %d %d %d %d %31s", &qq, &nn, &kk, &nv, w) != 5 || qq != q || nn != N) { fprintf(stderr, "bad sol\n"); return 1; }
    K = kk; int *fp = malloc(sizeof(int) * (K + 1)), *flp = malloc(sizeof(int) * (K + 1));
    for (int k = 0; k < K; k++) if (fscanf(f, "%d", &fp[k]) != 1) return 1;
    char tok[32]; int hm; if (fscanf(f, "%31s %d", tok, &hm) != 2) return 1; for (int e = 0; e < 2 * hm; e++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; }
    int *phi = malloc(sizeof(int) * 2 * N); for (int p = 0; p < N; p++) { int l; if (fscanf(f, "%d", &l) != 1) return 1; phi[p] = N + l; }
    fclose(f);
    char *freed = calloc(N, 1); for (int k = 0; k < K; k++) { freed[fp[k]] = 1; flp[k] = phi[fp[k]] - N; }
    for (int k = 0; k < K; k++) { int inc = 0; for (int t = 0; t < Q1; t++) if (LP[flp[k] * Q1 + t] == fp[k]) inc = 1; if (!inc) { fprintf(stderr, "freed point %d not on its line\n", fp[k]); return 1; } }
    int H, m; f = fopen(argv[3], "r"); if (fscanf(f, "%d %d", &H, &m) != 2 || H != 2 * K) { fprintf(stderr, "hub graph must have 2K = %d hubs per side\n", 2 * K); return 1; }
    long n = 10L * N + 4L * K;
    FILE *o = fopen(argv[4], "w"); fprintf(o, "%ld\n", n); long E = 0;
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
