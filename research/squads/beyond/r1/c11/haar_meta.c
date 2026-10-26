/* c11: Haar graphs H(G,S) of metacyclic groups G = Z_m x|_r Z_k (index a + m*j, (a,j)(b,l) = (a + r^j b, j+l)),
   S = {e, x, y}. Bipartite cubic graph on 2N vertices: black x ~ white x*s (s in S).
   Left multiplication acts transitively on each side, so diameter = max(ecc(black e), ecc(white e)).
   Usage: haar_meta m k r D scan [maxtrials|0 = exhaustive] [seed]   prints first valid S and stats
          haar_meta m k r D emit x y OUT                              writes OUT (apsp edge list) for S={e,x,y}
   Prints the exact diameter of the emitted graph too. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int m, k, r, N, D;
static uint16_t *MT;
static int *INV;
static int *pw;
static int *dist, *queue;

static int mulg(int x, int y) {
    int a = x % m, j = x / m, b = y % m, l = y / m;
    int c = (a + pw[j] * b) % m;
    return c + m * ((j + l) % k);
}

static void build(void) {
    N = m * k;
    pw = malloc(sizeof(int) * (k + 1));
    pw[0] = 1 % m;
    for (int j = 1; j <= k; j++) pw[j] = (pw[j - 1] * r) % m;
    if (pw[k] != 1 % m) { fprintf(stderr, "r^k != 1 mod m\n"); exit(2); }
    MT = malloc(sizeof(uint16_t) * (size_t)N * N);
    INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[(size_t)x * N + y] = (uint16_t)mulg(x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) if (MT[(size_t)x * N + y] == 0) { INV[x] = y; break; }
    dist = malloc(sizeof(int) * 2 * N);
    queue = malloc(sizeof(int) * 2 * N);
}

static inline int nb(int v, const int *S, int i) {
    if (v < N) return N + MT[(size_t)v * N + S[i]];
    return MT[(size_t)(v - N) * N + INV[S[i]]];
}

/* eccentricity of src (0 = black e, N = white e), or -1 if some vertex is farther than limit or unreached */
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

static int diam_ok(const int *S) {
    /* returns 1 iff diameter <= D */
    return ecc(0, S, D) >= 0 && ecc(N, S, D) >= 0;
}

static int diam_exact(const int *S) {
    int a = ecc(0, S, 2 * N), b = ecc(N, S, 2 * N);
    if (a < 0 || b < 0) return -1;
    return a > b ? a : b;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: haar_meta m k r D scan|emit ...\n"); return 1; }
    m = atoi(argv[1]); k = atoi(argv[2]); r = atoi(argv[3]); D = atoi(argv[4]);
    build();
    int S[3] = {0, 0, 0};
    if (!strcmp(argv[5], "emit")) {
        int x = atoi(argv[6]), y = atoi(argv[7]);
        S[0] = 0; S[1] = x; S[2] = y;
        int dd = diam_exact(S);
        printf("N=%d S={0,%d,%d} exact_diameter=%d\n", N, x, y, dd);
        if (argc > 8) {
            FILE *f = fopen(argv[8], "w");
            fprintf(f, "%d\n", 2 * N);
            for (int v = 0; v < N; v++)
                for (int i = 0; i < 3; i++) fprintf(f, "%d %d\n", v, nb(v, S, i));
            fclose(f);
        }
        return 0;
    }
    /* scan */
    long maxtrials = argc > 6 ? atol(argv[6]) : 0;
    unsigned seed = argc > 7 ? (unsigned)atoi(argv[7]) : 12345u;
    srand(seed);
    long tried = 0, good = 0; int first[2] = {-1, -1};
    if (maxtrials == 0) {
        for (int x = 1; x < N && good == 0; x++)
            for (int y = x + 1; y < N; y++) {
                S[0] = 0; S[1] = x; S[2] = y; tried++;
                if (diam_ok(S)) { good++; first[0] = x; first[1] = y; break; }
            }
    } else {
        for (long t = 0; t < maxtrials; t++) {
            int x = 1 + rand() % (N - 1), y = 1 + rand() % (N - 1);
            if (x == y) continue;
            S[0] = 0; S[1] = x; S[2] = y; tried++;
            if (diam_ok(S)) { good++; if (first[0] < 0) { first[0] = x; first[1] = y; } }
        }
    }
    printf("RESULT m=%d k=%d r=%d N=%d D=%d tried=%ld good=%ld first_x=%d first_y=%d\n", m, k, r, N, D, tried, good, first[0], first[1]);
    return 0;
}
