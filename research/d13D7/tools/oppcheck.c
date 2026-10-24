/* oppcheck.c: independent check that a set of points (or lines) of H(q) is pairwise opposite (distance 6 in the
   incidence graph), by BFS balls of radius 4; also checks the criterion "distance <= 4 iff B(x,y) = 0" for 20 random
   points.  usage: oppcheck HEXFILE P|L FILE   (FILE: one index per line, '#' lines ignored) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int q, N, Q1; int32_t *lp, *pl; uint8_t *coord;
static void ball(int id, int maxd, uint8_t *dist, int32_t *queue) {
    memset(dist, 255, 2 * (size_t)N); int h = 0, t = 0; dist[id] = 0; queue[t++] = id;
    while (h < t) { int x = queue[h++]; if (dist[x] >= maxd) continue;
        const int32_t *nb = (x < N) ? &pl[(size_t)x * Q1] : &lp[(size_t)(x - N) * Q1]; int off = (x < N) ? N : 0;
        for (int k = 0; k < Q1; k++) { int y = nb[k] + off; if (dist[y] == 255) { dist[y] = dist[x] + 1; queue[t++] = y; } } }
}
static int B(int a, int b) { const uint8_t *x = coord + 7L * a, *y = coord + 7L * b;
    long s = x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2L*x[3]*y[3]; return (int)(((s % q) + q) % q); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1; q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    lp = malloc(4L * N * Q1); if (fread(lp, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1;
    coord = malloc(7L * N); if (fread(coord, 1, 7L * N, f) != 7L * N) return 1; fclose(f);
    pl = malloc(4L * N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = lp[(size_t)l * Q1 + k]; pl[(size_t)p * Q1 + c[p]++] = l; }
    uint8_t *dist = malloc(2L * N); int32_t *queue = malloc(8L * N);
    /* criterion check */
    srand(7); long badc = 0;
    for (int t = 0; t < 20; t++) { int x = rand() % N; ball(x, 6, dist, queue);
        for (int y = 0; y < N; y++) { int near = dist[y] <= 4, orth = B(x, y) == 0; if (near != orth) badc++; } }
    printf("criterion d<=4 iff B=0: %s (%ld mismatches over 20 points)\n", badc ? "FAILS" : "holds", badc);
    int type = argv[2][0] == 'L'; FILE *g = fopen(argv[3], "r"); char buf[256]; int *S = malloc(sizeof(int) * N); int m = 0;
    while (fgets(buf, sizeof buf, g)) { if (buf[0] == '#') continue; int v; if (sscanf(buf, "%d", &v) == 1) S[m++] = v; }
    uint8_t *in = calloc(2L * N, 1); for (int i = 0; i < m; i++) { if (S[i] < 0 || S[i] >= N || in[S[i] + type * N]) { printf("RESULT INVALID bad or repeated index\n"); return 1; } in[S[i] + type * N] = 1; }
    long bad = 0;
    for (int i = 0; i < m; i++) { ball(S[i] + type * N, 4, dist, queue);
        for (int j = 0; j < m; j++) if (j != i && dist[S[j] + type * N] <= 4) bad++; }
    printf("%d %s, %ld close pairs\n", m, type ? "lines" : "points", bad / 2);
    printf("RESULT %s pairwise_opposite %d\n", bad ? "INVALID" : "VALID", m);
    return bad ? 1 : 0;
}
