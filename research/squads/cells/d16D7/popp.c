/* popp.c: G-invariant partial ovoids (pairwise opposite points) and partial spreads (pairwise opposite lines) of H(q),
   G = <g> from collin.py. Orbits whose members are pairwise opposite, compatibility graph (all cross pairs opposite),
   exact maximum clique (simple branch and bound). Distance <= 4 is tested combinatorially (x, y within 4 iff equal,
   adjacent-at-2, or some element is at distance 2 from both). cell-16-7 session.
   Usage: popp HEXBIN PERMPTS.bin PERMLINES.bin KIND OUT.txt [maxsec]   (KIND 0 points, 1 lines; OUT: element list) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int q, N, Q1; static int32_t *LP, *PL;
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int M; static uint64_t *A; static int W; static int best = 0, *bestset, *cur; static double t0, tmax; static long nodes = 0;
static inline int adjm(int a, int b) { return (A[(size_t)a * W + (b >> 6)] >> (b & 63)) & 1; }
static void expand(int *cand, int nc, int depth) {
    nodes++;
    if (nc == 0) { if (depth > best) { best = depth; memcpy(bestset, cur, sizeof(int) * depth); fprintf(stderr, "  clique %d (%.1fs)\n", best, now() - t0); } return; }
    if (depth + nc <= best || now() - t0 > tmax) return;
    /* greedy colouring bound */
    int *col = malloc(sizeof(int) * nc), *ord = malloc(sizeof(int) * nc), ncol = 0, *cls = malloc(sizeof(int) * nc);
    char *done = calloc(nc, 1); int k = 0;
    while (k < nc) { ncol++; int start = k;
        for (int i = 0; i < nc; i++) if (!done[i]) { int ok = 1; for (int j = start; j < k; j++) if (adjm(cand[i], cand[ord[j]])) { ok = 0; break; } if (ok) { done[i] = 1; ord[k] = i; cls[k] = ncol; k++; } }
    }
    for (int t = nc - 1; t >= 0; t--) {
        if (depth + cls[t] <= best) break;
        int v = cand[ord[t]]; cur[depth] = v;
        int *nc2 = malloc(sizeof(int) * nc), n2 = 0;
        for (int s = 0; s < t; s++) { int u = cand[ord[s]]; if (adjm(v, u)) nc2[n2++] = u; }
        expand(nc2, n2, depth + 1); free(nc2);
        cand[ord[t]] = -1;   /* removed */
        /* compact remaining */
    }
    free(col); free(ord); free(cls); free(done);
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[(size_t)l * Q1 + k]; PL[(size_t)p * Q1 + c[p]++] = l; }
    int kind = atoi(argv[4]); tmax = argc > 6 ? atof(argv[6]) : 120;
    int32_t *perm = malloc(sizeof(int32_t) * N); f = fopen(argv[kind ? 3 : 2], "rb"); if (!f || fread(perm, 4, N, f) != (size_t)N) return 1; fclose(f);
    const int32_t *Aa = kind == 0 ? PL : LP, *Bb = kind == 0 ? LP : PL;
    int *orb = malloc(sizeof(int) * N), no = 0, *rep = malloc(sizeof(int) * N), m = 0;
    for (int i = 0; i < N; i++) orb[i] = -1;
    for (int s = 0; s < N; s++) if (orb[s] < 0) { int x = s, t = 0; while (orb[x] < 0) { orb[x] = no; x = perm[x]; t++; } m = t; rep[no++] = s; }
    /* mark2[x] = stamp if x within distance 2 of the current centre */
    int *mk = calloc(N, sizeof(int)), stamp = 0;
    #define NEAR4(x, y) ({ int _r = 0; stamp++; mk[x] = stamp; for (int a = 0; a < Q1; a++) { int yy = Aa[(size_t)(x) * Q1 + a]; for (int b = 0; b < Q1; b++) mk[Bb[(size_t)yy * Q1 + b]] = stamp; } \
        if (mk[y] == stamp) _r = 1; else for (int a = 0; a < Q1 && !_r; a++) { int yy = Aa[(size_t)(y) * Q1 + a]; for (int b = 0; b < Q1; b++) if (mk[Bb[(size_t)yy * Q1 + b]] == stamp) { _r = 1; break; } } _r; })
    int *orbel = malloc(sizeof(int) * (size_t)no * m);
    for (int o = 0; o < no; o++) { int x = rep[o]; for (int t = 0; t < m; t++) { orbel[(size_t)o * m + t] = x; x = perm[x]; } }
    int *good = malloc(sizeof(int) * no); M = 0;
    for (int o = 0; o < no; o++) { int x = rep[o], ok = 1; for (int t = 1; t < m && ok; t++) if (NEAR4(x, orbel[(size_t)o * m + t])) ok = 0; if (ok) good[M++] = o; }
    fprintf(stderr, "kind %d: %d orbits of %d, %d internally pairwise opposite\n", kind, no, m, M);
    W = (M + 63) / 64; A = calloc((size_t)M * W, 8); long ne = 0;
    for (int i = 0; i < M; i++) { int x = rep[good[i]];
        /* compatibility with orbit j: rep_i opposite to all members of orbit j */
        stamp++; int st0 = stamp; mk[x] = st0; for (int a = 0; a < Q1; a++) { int yy = Aa[(size_t)x * Q1 + a]; for (int b = 0; b < Q1; b++) mk[Bb[(size_t)yy * Q1 + b]] = st0; }
        for (int j = i + 1; j < M; j++) { int ok = 1;
            for (int t = 0; t < m && ok; t++) { int y = orbel[(size_t)good[j] * m + t];
                if (mk[y] == st0) { ok = 0; break; }
                for (int a = 0; a < Q1 && ok; a++) { int yy = Aa[(size_t)y * Q1 + a]; for (int b = 0; b < Q1; b++) if (mk[Bb[(size_t)yy * Q1 + b]] == st0) { ok = 0; break; } } }
            if (ok) { A[(size_t)i * W + (j >> 6)] |= 1ULL << (j & 63); A[(size_t)j * W + (i >> 6)] |= 1ULL << (i & 63); ne++; } }
    }
    fprintf(stderr, "compatibility graph: %d vertices, %ld edges (density %.4f)\n", M, ne, 2.0 * ne / ((double)M * (M - 1)));
    bestset = malloc(sizeof(int) * M); cur = malloc(sizeof(int) * M); int *cand = malloc(sizeof(int) * M);
    for (int i = 0; i < M; i++) cand[i] = i;
    t0 = now(); expand(cand, M, 0);
    fprintf(stderr, "RESULT kind %d: max clique %d orbits = %d elements (%s, %ld nodes)\n", kind, best, best * m, now() - t0 > tmax ? "time limit" : "exact", nodes);
    FILE *fo = fopen(argv[5], "w"); for (int i = 0; i < best; i++) for (int t = 0; t < m; t++) fprintf(fo, "%d\n", orbel[(size_t)good[bestset[i]] * m + t]); fclose(fo);
    return 0;
}
