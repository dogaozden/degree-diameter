/* chk7.c: independent diameter check of an edge list, cell-16-7 session, 2026-10-24.
   Reads "n" then edges "u v" (the format of research/lifts/coordinator_check/apsp.c), checks simple, bipartite,
   max degree <= d, connected, and that the BFS eccentricity of the chosen sources is <= D. Uses nothing from the
   construction code. Bit-parallel BFS, 256 sources per pass (push at sparse levels, pull at dense ones),
   pthreads over passes.
   Usage: chk7 EDGES d D THREADS all                    every vertex is a source (no symmetry assumed)
          chk7 EDGES d D THREADS shift L B              first checks that v -> (v + B) mod (L*B) for v < L*B,
                                                        v fixed for v >= L*B, is an automorphism of the edge set;
                                                        then sources = vertices 0..B-1 and L*B..n-1 (enough by symmetry)
          chk7 EDGES d D THREADS list s1 s2 ...         just these sources
          chk7 EDGES d D THREADS range a b              sources a..b-1 (to split "all" over machines) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>

#define W 4
static long n, m;
static int32_t *adj; static long *st;
static long *src; static long nsrc;
static int Dlim;
static long nextpass = 0, done = 0; static int worst = 0; static long badsrc = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;

static void *worker(void *arg) {
    (void)arg;
    uint64_t (*vis)[W] = malloc(sizeof(uint64_t) * W * n), (*fr)[W] = malloc(sizeof(uint64_t) * W * n), (*nx)[W] = malloc(sizeof(uint64_t) * W * n);
    long *front = malloc(sizeof(long) * n), *nfront = malloc(sizeof(long) * n);
    if (!vis || !fr || !nx || !front || !nfront) { fprintf(stderr, "out of memory\n"); exit(1); }
    for (;;) {
        pthread_mutex_lock(&mu); long pass = nextpass++; pthread_mutex_unlock(&mu);
        long s0 = pass * 64 * W; if (s0 >= nsrc) break;
        int ns = (nsrc - s0 < 64 * W) ? (int)(nsrc - s0) : 64 * W;
        uint64_t full[W]; for (int w = 0; w < W; w++) { int b = ns - 64 * w; full[w] = b >= 64 ? ~0ULL : (b <= 0 ? 0 : ((1ULL << b) - 1)); }
        memset(vis, 0, sizeof(uint64_t) * W * n); memset(fr, 0, sizeof(uint64_t) * W * n);
        long nf = 0;
        for (int k = 0; k < ns; k++) { long v = src[s0 + k]; if (!(fr[v][0] | fr[v][1] | fr[v][2] | fr[v][3])) front[nf++] = v; vis[v][k / 64] |= 1ULL << (k % 64); fr[v][k / 64] |= 1ULL << (k % 64); }
        int lev = 0;
        for (;;) {
            long nn = 0;
            if (nf < n / 32) {   /* push from the frontier */
                for (long i = 0; i < nf; i++) { long y = front[i];
                    for (long e = st[y]; e < st[y + 1]; e++) { long x = adj[e];
                        int was = (nx[x][0] | nx[x][1] | nx[x][2] | nx[x][3]) != 0;
                        for (int w = 0; w < W; w++) nx[x][w] |= fr[y][w] & ~vis[x][w];
                        if (!was && (nx[x][0] | nx[x][1] | nx[x][2] | nx[x][3])) nfront[nn++] = x; } }
                for (long i = 0; i < nf; i++) { long y = front[i]; for (int w = 0; w < W; w++) fr[y][w] = 0; }
                memcpy(front, nfront, sizeof(long) * nn);
            } else {             /* pull over all vertices that are not yet reached by every source */
                for (long x = 0; x < n; x++) {
                    if (vis[x][0] == full[0] && vis[x][1] == full[1] && vis[x][2] == full[2] && vis[x][3] == full[3]) { nx[x][0] = nx[x][1] = nx[x][2] = nx[x][3] = 0; continue; }
                    uint64_t a0 = 0, a1 = 0, a2 = 0, a3 = 0;
                    for (long e = st[x]; e < st[x + 1]; e++) { uint64_t *f = fr[adj[e]]; a0 |= f[0]; a1 |= f[1]; a2 |= f[2]; a3 |= f[3]; }
                    a0 &= ~vis[x][0]; a1 &= ~vis[x][1]; a2 &= ~vis[x][2]; a3 &= ~vis[x][3];
                    nx[x][0] = a0; nx[x][1] = a1; nx[x][2] = a2; nx[x][3] = a3;
                    if (a0 | a1 | a2 | a3) front[nn++] = x;
                }
                memset(fr, 0, sizeof(uint64_t) * W * n);
            }
            if (nn == 0) break;
            lev++;
            for (long i = 0; i < nn; i++) { long x = front[i]; for (int w = 0; w < W; w++) { vis[x][w] |= nx[x][w]; fr[x][w] = nx[x][w]; nx[x][w] = 0; } }
            nf = nn;
        }
        long unreached = 0;
        for (long x = 0; x < n; x++) for (int w = 0; w < W; w++) if (vis[x][w] != full[w]) { unreached++; break; }
        pthread_mutex_lock(&mu);
        if (lev > worst) worst = lev;
        if (unreached || lev > Dlim) badsrc++;
        done += ns;
        if (pass % 50 == 0) fprintf(stderr, "pass %ld: %ld of %ld sources done, worst %d, bad passes %ld\n", pass, done, nsrc, worst, badsrc);
        pthread_mutex_unlock(&mu);
        if (unreached) { printf("RESULT INVALID unreached vertices from sources %ld..\n", s0); fflush(stdout); }
    }
    free(vis); free(fr); free(nx); free(front); free(nfront);
    return NULL;
}

int main(int c, char **v) {
    if (c < 6) { fprintf(stderr, "usage: see header\n"); return 2; }
    FILE *f = fopen(v[1], "r"); if (!f) { perror(v[1]); return 2; }
    int d = atoi(v[2]); Dlim = atoi(v[3]); int T = atoi(v[4]);
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long cap = 1 << 20; int32_t *U = malloc(cap * 4), *V = malloc(cap * 4); long a, b; m = 0;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) { printf("RESULT INVALID bad edge %ld %ld\n", a, b); return 1; }
        if (m == cap) { cap *= 2; U = realloc(U, cap * 4); V = realloc(V, cap * 4); }
        U[m] = (int32_t)a; V[m] = (int32_t)b; m++;
    }
    fclose(f);
    long *deg = calloc(n + 1, sizeof(long)); for (long i = 0; i < m; i++) { deg[U[i]]++; deg[V[i]]++; }
    st = calloc(n + 1, sizeof(long)); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(sizeof(int32_t) * 2 * m); long *pos = calloc(n, sizeof(long));
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = V[i]; adj[st[V[i]] + pos[V[i]]++] = U[i]; }
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) {
        if (deg[x] > maxd) maxd = deg[x]; if (deg[x] < mind) mind = deg[x];
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++) if (adj[i] == adj[j]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; }
    }
    int *col = malloc(sizeof(int) * n); for (long i = 0; i < n; i++) col[i] = -1;
    long *qq = malloc(sizeof(long) * n), h = 0, t = 0; col[0] = 0; qq[t++] = 0; int bip = 1;
    while (h < t) { long x = qq[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; qq[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld)\n", t, n); return 1; }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s\n", n, m, mind, maxd, bip ? "yes" : "no");
    src = malloc(sizeof(long) * n); nsrc = 0;
    if (!strcmp(v[5], "all")) { for (long x = 0; x < n; x++) src[nsrc++] = x; }
    else if (!strcmp(v[5], "range")) { long lo = atol(v[6]), hi = atol(v[7]); for (long x = lo; x < hi && x < n; x++) src[nsrc++] = x; }
    else if (!strcmp(v[5], "list")) { for (int i = 6; i < c; i++) src[nsrc++] = atol(v[i]); }
    else if (!strcmp(v[5], "shift")) {
        long L = atol(v[6]), B = atol(v[7]), LB = L * B;
        if (LB > n) { printf("RESULT INVALID shift block larger than n\n"); return 1; }
        /* automorphism test: the image of every edge is an edge (sorted adjacency + binary search) */
        for (long x = 0; x < n; x++) { long lo = st[x], hi = st[x + 1];   /* insertion sort, degrees are small */
            for (long i = lo + 1; i < hi; i++) { int32_t k = adj[i]; long j = i - 1; while (j >= lo && adj[j] > k) { adj[j + 1] = adj[j]; j--; } adj[j + 1] = k; } }
        long badimg = 0;
        for (long i = 0; i < m; i++) {
            long x = U[i] < LB ? (U[i] + B) % LB : U[i], y = V[i] < LB ? (V[i] + B) % LB : V[i];
            long lo = st[x], hi = st[x + 1] - 1, found = 0;
            while (lo <= hi) { long md = (lo + hi) / 2; if (adj[md] == y) { found = 1; break; } if (adj[md] < y) lo = md + 1; else hi = md - 1; }
            if (!found) badimg++;
        }
        printf("shift v -> v+%ld mod %ld: %ld edges map to non-edges\n", B, LB, badimg);
        if (badimg) { printf("RESULT INVALID not an automorphism\n"); return 1; }
        for (long x = 0; x < B; x++) src[nsrc++] = x;
        for (long x = LB; x < n; x++) src[nsrc++] = x;
    } else { fprintf(stderr, "unknown mode\n"); return 2; }
    free(U); free(V);
    printf("sources: %ld (%s)\n", nsrc, v[5]); fflush(stdout);
    pthread_t th[64]; if (T < 1) T = 1; if (T > 64) T = 64;
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, worker, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    printf("max eccentricity over the %ld sources = %d, bad passes %ld\n", nsrc, worst, badsrc);
    if (bip && maxd <= d && worst <= Dlim && badsrc == 0) printf("RESULT VALID d=%d D=%d n=%ld (%s sources)\n", d, Dlim, n, v[5]);
    else printf("RESULT INVALID\n");
    return 0;
}
