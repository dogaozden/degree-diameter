/* x5gen3.c: 5-level cover of H(q) with both matchings = M (freed points from a d7hex .sol), hubs with one owner per
   level (research/squads/d12D7/clhaar/mkhubs3.py). Like research/d10D7/dual/x5gen2.c, but line-side hub j is adjacent
   to (F[oL[j][i]], i) and point-side hub k to (M(F[oP[k][i]]), i) for i = 0..4, so the owner may change with the level.
   Checks that no (p, i) or (M(p), i) gets more than 2 hubs (the 2 freed slots).
   HUBS3 file: "HL HP m", HL lines of 5 freed indices, HP lines of 5 freed indices, m lines "j k".
   Usage: x5gen3 HEXBIN SOL HUBS3 OUT.edges */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: x5gen3 HEXBIN SOL HUBS3 OUT.edges\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0], N = hdr[1], Q1 = q + 1;
    int *LP = malloc(sizeof(int) * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    int K, nn, qq, nv; char w[32];
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "d7hex %d %d %d %d %31s", &qq, &nn, &K, &nv, w) != 5 || qq != q || nn != N) { fprintf(stderr, "bad sol\n"); return 1; }
    int *fp = malloc(sizeof(int) * (K + 1)); for (int k = 0; k < K; k++) if (fscanf(f, "%d", &fp[k]) != 1) return 1;
    char tok[32]; int hm; if (fscanf(f, "%31s %d", tok, &hm) != 2) return 1; for (int e = 0; e < 2 * hm; e++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; }
    int *M = malloc(sizeof(int) * N); for (int p = 0; p < N; p++) if (fscanf(f, "%d", &M[p]) != 1) return 1; fclose(f);
    char *freed = calloc(N, 1); for (int k = 0; k < K; k++) freed[fp[k]] = 1;
    int HL, HP, m; f = fopen(argv[3], "r"); if (!f || fscanf(f, "%d %d %d", &HL, &HP, &m) != 3) return 1;
    int *oL = malloc(sizeof(int) * 5 * HL), *oP = malloc(sizeof(int) * 5 * HP);
    unsigned char *useL = calloc((size_t)K * 5, 1), *useP = calloc((size_t)K * 5, 1);
    for (int j = 0; j < HL; j++) for (int i = 0; i < 5; i++) { int o; if (fscanf(f, "%d", &o) != 1 || o < 0 || o >= K) { fprintf(stderr, "bad owner\n"); return 1; } oL[j * 5 + i] = o; if (++useL[o * 5 + i] > 2) { fprintf(stderr, "point slot overflow at freed %d level %d\n", o, i); return 1; } }
    for (int k = 0; k < HP; k++) for (int i = 0; i < 5; i++) { int o; if (fscanf(f, "%d", &o) != 1 || o < 0 || o >= K) { fprintf(stderr, "bad owner\n"); return 1; } oP[k * 5 + i] = o; if (++useP[o * 5 + i] > 2) { fprintf(stderr, "line slot overflow at freed %d level %d\n", o, i); return 1; } }
    long n = 10L * N + HL + HP;
    FILE *o = fopen(argv[4], "w"); fprintf(o, "%ld\n", n); long E = 0;
    #define ID(v, i) ((long)(i) * 2 * N + (v))
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + l, i)); E++; } }
    for (int p = 0; p < N; p++) { if (freed[p]) continue; for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + M[p], (i + 1) % 5)); fprintf(o, "%ld %ld\n", ID(p, i), ID(N + M[p], (i + 2) % 5)); E += 2; } }
    for (int j = 0; j < HL; j++) for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", 10L * N + j, ID(fp[oL[j * 5 + i]], i)); E++; }
    for (int k = 0; k < HP; k++) for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", 10L * N + HL + k, ID(N + M[fp[oP[k * 5 + i]]], i)); E++; }
    for (int e = 0; e < m; e++) { int j, k; if (fscanf(f, "%d %d", &j, &k) != 2) return 1; fprintf(o, "%ld %ld\n", 10L * N + j, 10L * N + HL + k); E++; }
    fclose(f); fclose(o);
    fprintf(stderr, "q=%d N=%d K=%d hubs %d + %d, n=%ld edges=%ld\n", q, N, K, HL, HP, n, E);
    return 0;
}
