/* xgen.c: x5gen2.c for any odd number of levels LV = 2j+1: the polygon cover of H(q) with j matchings, all equal to
   M, with shifts 1..j: (p,i) ~ (M(p), i+s) for s = 1..j (Delta = q+1+j; LV = 3 is X(M), LV = 5 the (12,7)-type graph,
   LV = 7 the table's 3-matching cover). Freed points (from a d7hex .sol) lose their j extra edges in every level, so
   each freed point may own up to j hubs per side; a hub is adjacent to its owner in all LV levels.
   HUBS file: "HL HP m", then HL owner ids, then HP owner ids, then m lines "j k" (hub graph).
   Usage: xgen HEXBIN SOL HUBS LV OUT.edges */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0], N = hdr[1], Q1 = q + 1; int LV = atoi(argv[4]), J = (LV - 1) / 2; if (LV < 3 || LV % 2 == 0) return 1;
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
    for (int k = 0; k < K; k++) if (cntL[k] > J || cntP[k] > J) { fprintf(stderr, "freed point %d owns more than %d hubs on a side\n", k, J); return 1; }
    long BASE = 2L * LV * N, n = BASE + HL + HP;
    FILE *o = fopen(argv[5], "w"); fprintf(o, "%ld\n", n); long E = 0;
    #define ID(v, i) ((long)(i) * 2 * N + (v))
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; for (int i = 0; i < LV; i++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + l, i)); E++; } }
    for (int p = 0; p < N; p++) { if (freed[p]) continue; for (int i = 0; i < LV; i++) for (int sh = 1; sh <= J; sh++) { fprintf(o, "%ld %ld\n", ID(p, i), ID(N + M[p], (i + sh) % LV)); E++; } }
    for (int j = 0; j < HL; j++) for (int i = 0; i < LV; i++) { fprintf(o, "%ld %ld\n", BASE + j, ID(fp[ownL[j]], i)); E++; }
    for (int k = 0; k < HP; k++) for (int i = 0; i < LV; i++) { fprintf(o, "%ld %ld\n", BASE + HL + k, ID(N + M[fp[ownP[k]]], i)); E++; }
    for (int e = 0; e < m; e++) { int j, k; if (fscanf(f, "%d %d", &j, &k) != 2) return 1; fprintf(o, "%ld %ld\n", BASE + j, BASE + HL + k); E++; }
    fclose(f); fclose(o);
    fprintf(stderr, "q=%d N=%d LV=%d K=%d hubs %d + %d, n=%ld edges=%ld\n", q, N, LV, K, HL, HP, n, E);
    return 0;
}
