/* viol: count ordered pairs at distance > D (or unreachable). usage: viol edges.txt D
   edges.txt: "n" then "u v" lines. Prints n, m, degree range, violating ordered pairs, violating sources. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]);
    long n, m = 0; if (fscanf(f, "%ld", &n) != 1) return 1;
    long cap = 1 << 20, *eu = malloc(cap * sizeof(long)), *ev = malloc(cap * sizeof(long));
    long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (m == cap) { cap *= 2; eu = realloc(eu, cap * sizeof(long)); ev = realloc(ev, cap * sizeof(long)); }
        eu[m] = a; ev[m] = b; m++;
    }
    fclose(f);
    long *deg = calloc(n, sizeof(long));
    for (long i = 0; i < m; i++) { if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) { printf("BAD edge %ld\n", i); return 1; } deg[eu[i]]++; deg[ev[i]]++; }
    long *st = calloc(n + 1, sizeof(long));
    for (long v = 0; v < n; v++) st[v + 1] = st[v] + deg[v];
    long *pos = malloc(n * sizeof(long)); long *adj = malloc(2 * m * sizeof(long));
    for (long v = 0; v < n; v++) pos[v] = st[v];
    for (long i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    long mind = 1 << 30, maxd = 0; for (long v = 0; v < n; v++) { if (deg[v] < mind) mind = deg[v]; if (deg[v] > maxd) maxd = deg[v]; }
    int *dist = malloc(n * sizeof(int)); long *que = malloc(n * sizeof(long));
    long viol = 0, vsrc = 0, worst = 0;
    for (long s = 0; s < n; s++) {
        for (long v = 0; v < n; v++) dist[v] = -1;
        long h = 0, t = 0; que[t++] = s; dist[s] = 0; long reached = 1;
        while (h < t) {
            long x = que[h++]; if (dist[x] >= D) continue;
            for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; que[t++] = y; reached++; } }
        }
        if (reached < n) { viol += n - reached; vsrc++; if (argc > 3) printf("SRC %ld %ld\n", s, n - reached); }
    }
    printf("n=%ld m=%ld deg=%ld..%ld D=%d violating_ordered_pairs=%ld violating_sources=%ld\n", n, m, mind, maxd, D, viol, vsrc);
    return 0;
}
