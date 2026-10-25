/* bfs1.c: BFS from one source over an EDGES file (n, then pairs). Prints, per distance, counts by vertex type:
   main point, main line, L-hub (id in [10N, 10N+HL)), P-hub. Usage: bfs1 EDGES SRC N HL */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); long src = atol(argv[2]), N = atol(argv[3]), HL = atol(argv[4]);
    long n; fscanf(f, "%ld", &n); long cap = 1 << 23, m = 0; long *U = malloc(cap * 8), *W = malloc(cap * 8), a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8); for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    int *dist = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) dist[i] = -1;
    long *q = malloc(n * 8), h = 0, t = 0; dist[src] = 0; q[t++] = src;
    while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
    long cnt[12][4] = {{0}}, tot[4] = {0}; long hubbase = 10 * N;
    for (long v = 0; v < n; v++) {
        int ty; if (v >= hubbase) ty = (v - hubbase < HL) ? 2 : 3; else ty = ((v / (2 * N)) >= 0 && (v % (2 * N)) < N) ? 0 : 1;
        tot[ty]++; int d = dist[v]; if (d < 0) d = 11; if (d > 10) d = 11;
        cnt[d][ty]++;
    }
    printf("src=%ld reached=%ld of %ld\n", src, t, n);
    printf("dist  mainpoint mainline Lhub Phub\n");
    for (int d = 0; d <= 11; d++) { long s = 0; for (int ty = 0; ty < 4; ty++) s += cnt[d][ty]; if (s) printf("%4d %9ld %9ld %6ld %6ld\n", d, cnt[d][0], cnt[d][1], cnt[d][2], cnt[d][3]); }
    return 0;
}
