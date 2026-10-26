/* c11: Haar graphs H(G,S), S = {e, x, y}, for any finite group given by a table file (groups.py write_bin format:
   int32 N, then N*N uint16, row g = g*h, identity 0). Bipartite cubic on 2N vertices: black g ~ white g*s.
   Left multiplication is transitive on each side, so diameter = max(ecc(black e), ecc(white e)).
   Usage: haar_tab TABLE.bin D scan            exhaustive over x<y (first valid pair printed, then stop)
          haar_tab TABLE.bin D emit x y OUT    writes apsp edge list for S={0,x,y} and prints exact diameter */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int N, D;
static uint16_t *MT;
static int *INV;
static int *dist, *queue;

static inline int nb(int v, const int *S, int i) {
    if (v < N) return N + MT[(size_t)v * N + S[i]];
    return MT[(size_t)(v - N) * N + INV[S[i]]];
}

static int ecc(int src, const int *S, int limit) {
    for (int v = 0; v < 2 * N; v++) dist[v] = -1;
    int head = 0, tail = 0, cnt = 1, last = 0;
    dist[src] = 0; queue[tail++] = src;
    while (head < tail) {
        int v = queue[head++];
        if (dist[v] >= limit) continue;
        for (int i = 0; i < 3; i++) {
            int w = nb(v, S, i);
            if (dist[w] < 0) { dist[w] = dist[v] + 1; queue[tail++] = w; cnt++; last = dist[w]; }
        }
    }
    if (cnt < 2 * N) return -1;
    return last;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: haar_tab TABLE.bin D scan|emit ...\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("table"); return 1; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 1; N = n32;
    MT = malloc(sizeof(uint16_t) * (size_t)N * N);
    if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); return 1; }
    fclose(f);
    D = atoi(argv[2]);
    INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) {
        int found = 0;
        for (int y = 0; y < N; y++) if (MT[(size_t)x * N + y] == 0) { INV[x] = y; found = 1; break; }
        if (!found) { fprintf(stderr, "no inverse\n"); return 1; }
    }
    dist = malloc(sizeof(int) * 2 * N); queue = malloc(sizeof(int) * 2 * N);
    int S[3] = {0, 0, 0};
    if (!strcmp(argv[3], "emit")) {
        int x = atoi(argv[4]), y = atoi(argv[5]);
        S[1] = x; S[2] = y;
        int a = ecc(0, S, 2 * N), b = ecc(N, S, 2 * N);
        int dd = (a < 0 || b < 0) ? -1 : (a > b ? a : b);
        printf("N=%d S={0,%d,%d} exact_diameter=%d\n", N, x, y, dd);
        if (argc > 6) {
            FILE *o = fopen(argv[6], "w");
            fprintf(o, "%d\n", 2 * N);
            for (int v = 0; v < N; v++) for (int i = 0; i < 3; i++) fprintf(o, "%d %d\n", v, nb(v, S, i));
            fclose(o);
        }
        return 0;
    }
    long tried = 0; int fx = -1, fy = -1;
    for (int x = 1; x < N && fx < 0; x++)
        for (int y = x + 1; y < N; y++) {
            S[1] = x; S[2] = y; tried++;
            if (ecc(0, S, D) >= 0 && ecc(N, S, D) >= 0) { fx = x; fy = y; break; }
        }
    printf("RESULT N=%d D=%d tried=%ld first_x=%d first_y=%d\n", N, D, tried, fx, fy);
    return 0;
}
