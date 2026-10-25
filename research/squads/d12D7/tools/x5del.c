/* x5del.c: x5gen3 (5-level cover of H(q), matchings = M, freed points, hubs with per-level owners) with a set of
   deleted base vertices: every (v, i), v in DEL, is removed in all 5 levels (with its edges). Vertices are renumbered
   level by level, so (v, i) -> i*B' + rank(v) with B' = 2N - |DEL|, and the level shift stays an automorphism when the
   hubs do not break it (no hubs, or same owner at every level). Hubs keep their ids after the main vertices.
   DEL file: base ids, points 0..N-1, lines N..2N-1. HUBS3: as for x5gen3, or "-" for no hubs.
   Usage: x5del HEXBIN SOL DEL HUBS3|- OUT.edges */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: x5del HEXBIN SOL DEL HUBS3|- OUT.edges\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0], N = hdr[1], Q1 = q + 1;
    int *LP = malloc(sizeof(int) * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    int K, nn, qq, nv; char w[32];
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "d7hex %d %d %d %d %31s", &qq, &nn, &K, &nv, w) != 5 || qq != q || nn != N) { fprintf(stderr, "bad sol\n"); return 1; }
    int *fp = malloc(sizeof(int) * (K + 1)); for (int k = 0; k < K; k++) if (fscanf(f, "%d", &fp[k]) != 1) return 1;
    char tok[32]; int hm; if (fscanf(f, "%31s %d", tok, &hm) != 2) return 1; for (int e = 0; e < 2 * hm; e++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; }
    int *M = malloc(sizeof(int) * N); for (int p = 0; p < N; p++) if (fscanf(f, "%d", &M[p]) != 1) return 1; fclose(f);
    char *freed = calloc(N, 1); for (int k = 0; k < K; k++) freed[fp[k]] = 1;
    char *del = calloc(2 * N, 1); f = fopen(argv[3], "r"); int x, nd = 0; while (f && fscanf(f, "%d", &x) == 1) if (x >= 0 && x < 2 * N && !del[x]) { del[x] = 1; nd++; } if (f) fclose(f);
    long *rk = malloc(sizeof(long) * 2 * N); long Bp = 0; for (int v = 0; v < 2 * N; v++) rk[v] = del[v] ? -1 : Bp++;
    #define ID(v, i) ((long)(i) * Bp + rk[v])
    int HL = 0, HP = 0, m = 0; int *oL = NULL, *oP = NULL; FILE *hf = NULL;
    if (argv[4][0] != '-') { hf = fopen(argv[4], "r"); if (!hf || fscanf(hf, "%d %d %d", &HL, &HP, &m) != 3) return 1;
        oL = malloc(sizeof(int) * 5 * (HL + 1)); oP = malloc(sizeof(int) * 5 * (HP + 1));
        for (int j = 0; j < 5 * HL; j++) if (fscanf(hf, "%d", &oL[j]) != 1) return 1;
        for (int j = 0; j < 5 * HP; j++) if (fscanf(hf, "%d", &oP[j]) != 1) return 1; }
    long n = 5 * Bp + HL + HP;
    FILE *o = fopen(argv[5], "w"); fprintf(o, "%ld\n", n); long E = 0;
    for (int l = 0; l < N; l++) { if (del[N + l]) continue; for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; if (del[p]) continue; for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + l, i)); E++; } } }
    for (int p = 0; p < N; p++) { if (freed[p] || del[p] || del[N + M[p]]) continue; for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + M[p], (i + 1) % 5)); fprintf(o, "%ld %ld\n", ID(p, i), ID(N + M[p], (i + 2) % 5)); E += 2; } }
    for (int j = 0; j < HL; j++) for (int i = 0; i < 5; i++) { int v = fp[oL[j * 5 + i]]; if (del[v]) { fprintf(stderr, "hub owner deleted\n"); return 1; } fprintf(o, "%ld %ld\n", 5 * Bp + j, ID(v, i)); E++; }
    for (int k = 0; k < HP; k++) for (int i = 0; i < 5; i++) { int v = N + M[fp[oP[k * 5 + i]]]; if (del[v]) { fprintf(stderr, "hub owner deleted\n"); return 1; } fprintf(o, "%ld %ld\n", 5 * Bp + HL + k, ID(v, i)); E++; }
    for (int e = 0; e < m; e++) { int j, k; if (fscanf(hf, "%d %d", &j, &k) != 2) return 1; fprintf(o, "%ld %ld\n", 5 * Bp + j, 5 * Bp + HL + k); E++; }
    if (hf) fclose(hf); fclose(o);
    fprintf(stderr, "q=%d N=%d K=%d deleted %d base vertices (B'=%ld), hubs %d + %d, n=%ld edges=%ld\n", q, N, K, nd, Bp, HL, HP, n, E);
    return 0;
}
