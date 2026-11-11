/* far: usage far edges.txt D  -> counts ordered pairs (s,t), s!=t, with dist > D or unreachable (BFS from all sources, 1 thread) */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]); long n, m; if (fscanf(f, "%ld", &n) != 1) return 1;
    int *eu = NULL, *ev = NULL; m = 0; long cap = 1 << 16; eu = malloc(cap * sizeof(int)); ev = malloc(cap * sizeof(int));
    long a, b; while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; eu = realloc(eu, cap * sizeof(int)); ev = realloc(ev, cap * sizeof(int)); }
        eu[m] = a; ev[m] = b; m++; }
    long *deg = calloc(n + 1, sizeof(long)); for (long i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    long *st = calloc(n + 1, sizeof(long)); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *pos = calloc(n, sizeof(long)); for (long i = 0; i < n; i++) pos[i] = st[i];
    int *adj = malloc(2 * m * sizeof(int));
    for (long i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    int maxd = 0; for (long i = 0; i < n; i++) if (deg[i] > maxd) maxd = deg[i];
    int *dist = malloc(n * sizeof(int)); int *q = malloc(n * sizeof(int));
    long far = 0;
    long stride = argc > 3 ? atol(argv[3]) : 1;  /* Z8-invariant lifts: sources s = 0 mod 8 suffice (x stride) */
    for (long s = 0; s < n; s += stride) {
        for (long i = 0; i < n; i++) dist[i] = -1;
        long h = 0, t = 0; q[t++] = s; dist[s] = 0;
        while (h < t) { int x = q[h++]; if (dist[x] >= D) continue; for (long k = st[x]; k < st[x + 1]; k++) { int y = adj[k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        far += n - t;   /* unreachable within D (BFS stopped at depth D) */
    }
    far *= stride; printf("n=%ld m=%ld maxdeg=%d far_ordered=%ld far_unordered=%ld\n", n, m, maxd, far, far / 2);
    return 0;
}
