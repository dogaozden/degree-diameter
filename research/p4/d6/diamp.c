/* diamp.c: multi-threaded bit-parallel check that a graph has diameter <= D (and its max degree / bipartiteness).
   Input: text "n m" then m lines "u v". Usage: diamp FILE D THREADS
   Each thread runs breadth-first searches from 64 sources at a time (one bit per source) for D rounds and counts
   ordered pairs left unreached. Prints OK iff that count is 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
static long n, m, *off, *adj; static int D; static long nextb = 0, bad = 0, done = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static void *work(void *arg) {
    (void)arg;
    typedef struct { uint64_t w[4]; } B4;
    B4 *vis = malloc(n * sizeof(B4)), *fr = malloc(n * sizeof(B4)), *nx = malloc(n * sizeof(B4));
    for (;;) {
        pthread_mutex_lock(&mu); long b = nextb; nextb += 256; pthread_mutex_unlock(&mu);
        if (b >= n) break;
        int k = (n - b < 256) ? (int)(n - b) : 256;
        B4 full; for (int i = 0; i < 4; i++) { int lo = i * 64; int c = k - lo; full.w[i] = c >= 64 ? ~0ULL : (c <= 0 ? 0 : ((1ULL << c) - 1)); }
        memset(vis, 0, n * sizeof(B4)); memset(fr, 0, n * sizeof(B4));
        for (int j = 0; j < k; j++) { vis[b + j].w[j / 64] = fr[b + j].w[j / 64] = 1ULL << (j % 64); }
        for (int r = 0; r < D; r++) {
            for (long v = 0; v < n; v++) {
                uint64_t x0 = 0, x1 = 0, x2 = 0, x3 = 0;
                for (long t = off[v]; t < off[v + 1]; t++) { const B4 *f = &fr[adj[t]]; x0 |= f->w[0]; x1 |= f->w[1]; x2 |= f->w[2]; x3 |= f->w[3]; }
                x0 &= ~vis[v].w[0]; x1 &= ~vis[v].w[1]; x2 &= ~vis[v].w[2]; x3 &= ~vis[v].w[3];
                nx[v].w[0] = x0; nx[v].w[1] = x1; nx[v].w[2] = x2; nx[v].w[3] = x3;
                vis[v].w[0] |= x0; vis[v].w[1] |= x1; vis[v].w[2] |= x2; vis[v].w[3] |= x3;
            }
            B4 *t = fr; fr = nx; nx = t;
        }
        long lb = 0; for (long v = 0; v < n; v++) for (int i = 0; i < 4; i++) lb += __builtin_popcountll(full.w[i] & ~vis[v].w[i]);
        pthread_mutex_lock(&mu); bad += lb; done += k;
        if ((done / 256) % 500 == 0) { fprintf(stderr, "progress %ld/%ld bad=%ld\n", done, n, bad); }
        pthread_mutex_unlock(&mu);
    }
    return NULL;
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: diamp FILE D THREADS\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); D = atoi(argv[2]); int T = atoi(argv[3]);
    if (fscanf(f, "%ld %ld", &n, &m) != 2) return 2;
    long *eu = malloc(m * sizeof(long)), *ev = malloc(m * sizeof(long)); long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { if (fscanf(f, "%ld %ld", &eu[i], &ev[i]) != 2) return 2;
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) { fprintf(stderr, "bad edge\n"); return 2; }
        deg[eu[i]]++; deg[ev[i]]++; }
    off = malloc((n + 1) * sizeof(long)); off[0] = 0; long maxd = 0;
    for (long v = 0; v < n; v++) { off[v + 1] = off[v] + deg[v]; if (deg[v] > maxd) maxd = deg[v]; }
    adj = malloc(2 * m * sizeof(long)); long *pos = malloc(n * sizeof(long)); memcpy(pos, off, n * sizeof(long));
    for (long i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    /* duplicate edges and 2-colouring */
    long dup = 0; char *col = malloc(n); memset(col, -1, n); long *q = malloc(n * sizeof(long)); int bip = 1; long comps = 0;
    for (long v = 0; v < n; v++) for (long t = off[v]; t < off[v + 1]; t++) for (long u = t + 1; u < off[v + 1]; u++) if (adj[t] == adj[u]) dup++;
    for (long s = 0; s < n; s++) if (col[s] < 0) { comps++; col[s] = 0; long h = 0, tl = 0; q[tl++] = s;
        while (h < tl) { long x = q[h++]; for (long t = off[x]; t < off[x + 1]; t++) { long y = adj[t]; if (col[y] < 0) { col[y] = 1 - col[x]; q[tl++] = y; } else if (col[y] == col[x]) bip = 0; } } }
    fprintf(stderr, "n=%ld m=%ld maxdeg=%ld duplicate=%ld bipartite=%d components=%ld\n", n, m, maxd, dup, bip, comps);
    pthread_t th[256]; for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    int ok = (bad == 0 && bip && dup == 0);
    printf("n=%ld m=%ld maxdeg=%ld bipartite=%d duplicate_edges=%ld D=%d far_ordered_pairs=%ld %s\n", n, m, maxd, bip, dup, D, bad, ok ? "OK" : "FAIL");
    return ok ? 0 : 1;
}
