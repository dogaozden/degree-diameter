/* x5gen2.c: like x5gen.c (5-level cover of H(q), both matchings = M, freed points from a d7hex .sol), but with a
   general hub layout read from HUBS: line-side hub j owned by freed point ownL[j] (adjacent to (p, i) for all i),
   point-side hub k owned by freed point ownP[k] (adjacent to (M(p), i) for all i), plus hub-graph edges j ~ k.
   Each freed point may own 1 or 2 hubs per side (10 freed slots at p and at M(p)).
   HUBS file: "HL HP m", then HL owner ids, then HP owner ids, then m lines "j k".
   Usage: x5gen2 HEXBIN SOL HUBS OUT.edges */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
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
    int *ownL = malloc(sizeof(int) * HL), *ownP = malloc(sizeof(int) * HP), *cntL = calloc(K, sizeof(int)), *cntP = calloc(K, sizeof(int));
    for (int j = 0; j < HL; j++) { if (fscanf(f, "%d", &ownL[j]) != 1 || ownL[j] < 0 || ownL[j] >= K) return 1; cntL[ownL[j]]++; }
    for (int k = 0; k < HP; k++) { if (fscanf(f, "%d", &ownP[k]) != 1 || ownP[k] < 0 || ownP[k] >= K) return 1; cntP[ownP[k]]++; }
    for (int k = 0; k < K; k++) if (cntL[k] > 2 || cntP[k] > 2) { fprintf(stderr, "freed point %d owns more than 2 hubs on a side\n", k); return 1; }
    long n = 10L * N + HL + HP;
    FILE *o = fopen(argv[4], "w"); fprintf(o, "%ld\n", n); long E = 0;
    #define ID(v, i) ((long)(i) * 2 * N + (v))
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + l, i)); E++; } }
    for (int p = 0; p < N; p++) { if (freed[p]) continue; for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + M[p], (i + 1) % 5)); fprintf(o, "%ld %ld\n", ID(p, i), ID(N + M[p], (i + 2) % 5)); E += 2; } }
    for (int j = 0; j < HL; j++) for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", 10L * N + j, ID(fp[ownL[j]], i)); E++; }
    for (int k = 0; k < HP; k++) for (int i = 0; i < 5; i++) { fprintf(o, "%ld %ld\n", 10L * N + HL + k, ID(N + M[fp[ownP[k]]], i)); E++; }
    for (int e = 0; e < m; e++) { int j, k; if (fscanf(f, "%d %d", &j, &k) != 2) return 1; fprintf(o, "%ld %ld\n", 10L * N + j, 10L * N + HL + k); E++; }
    fclose(f); fclose(o);
    fprintf(stderr, "q=%d N=%d K=%d hubs %d + %d, n=%ld edges=%ld\n", q, N, K, HL, HP, n, E);
    return 0;
}
