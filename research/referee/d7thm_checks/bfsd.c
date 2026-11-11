/* Referee's checker: reads an edge list (first line "n m", then m lines "u v", 0-based), checks simple + bipartite,
   prints the degree range, and runs a bit-parallel BFS from every vertex (64 sources per word, OpenMP over batches).
   Prints the largest distance between vertices of the same colour (even) and of different colours (odd), and the
   number of ordered pairs at distance > D (argument 2).
   Usage: bfsd edges.txt D [lo hi [sample]] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int D = atoi(argv[2]);
    fseek(f, 0, SEEK_END); long fsz = ftell(f); fseek(f, 0, SEEK_SET);
    char *buf = malloc(fsz + 1); if (fread(buf, 1, fsz, f) != (size_t)fsz) return 1; buf[fsz] = 0; fclose(f);
    char *pp = buf;
    #define NEXTNUM(x) { while (*pp && (*pp < '0' || *pp > '9')) pp++; long _v = 0; while (*pp >= '0' && *pp <= '9') _v = 10 * _v + (*pp++ - '0'); x = _v; }
    long n, m; NEXTNUM(n);
    /* header "n m", or "n" alone (then m = number of remaining lines with two numbers) */
    { char *q = pp; while (*q == ' ' || *q == '\t') q++;
      if (*q >= '0' && *q <= '9') { NEXTNUM(m); }
      else { m = 0; for (char *r = pp; *r; r++) if (*r == '\n') m++; if (fsz && buf[fsz - 1] != '\n') m++; m -= 1; } }
    int *eu = malloc(m * sizeof(int)), *ev = malloc(m * sizeof(int)); long *deg = calloc(n, sizeof(long));
    for (long i = 0; i < m; i++) { NEXTNUM(eu[i]); NEXTNUM(ev[i]);
        if (eu[i] == ev[i] || eu[i] < 0 || ev[i] < 0 || eu[i] >= n || ev[i] >= n) { printf("BAD EDGE %ld\n", i); return 1; }
        deg[eu[i]]++; deg[ev[i]]++; }
    long *off = malloc((n + 1) * sizeof(long)); off[0] = 0; for (long v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    int *adj = malloc(2 * m * sizeof(int)); long *pos = malloc(n * sizeof(long)); memcpy(pos, off, n * sizeof(long));
    for (long i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    free(buf); free(eu); free(ev);
    /* sources: all, or the range [lo, hi) (arguments 3, 4), or a random sample of that range (argument 5, seed 1) */
    long lo = argc > 4 ? atol(argv[3]) : 0, hi = argc > 4 ? atol(argv[4]) : n, ns = hi - lo;
    long *src = malloc(ns * sizeof(long)); for (long i = 0; i < ns; i++) src[i] = lo + i;
    if (argc > 5) { long want = atol(argv[5]); srand(1);
        for (long i = 0; i < want && i < ns; i++) { long j = i + (((long)rand() << 31 | rand()) % (ns - i)); long t = src[i]; src[i] = src[j]; src[j] = t; }
        if (want < ns) ns = want; }
    long dmin = 1L << 60, dmax = 0; for (long v = 0; v < n; v++) { if (deg[v] < dmin) dmin = deg[v]; if (deg[v] > dmax) dmax = deg[v]; }
    /* simple: no repeated neighbour */
    long rep = 0; for (long v = 0; v < n; v++) for (long a = off[v]; a < off[v + 1]; a++) for (long b = a + 1; b < off[v + 1]; b++) if (adj[a] == adj[b]) rep++;
    /* bipartite: BFS 2-colouring */
    int *col = malloc(n * sizeof(int)); for (long v = 0; v < n; v++) col[v] = -1; int *qu = malloc(n * sizeof(int)); int bip = 1; long comps = 0;
    for (long s = 0; s < n; s++) if (col[s] < 0) { comps++; long h = 0, t = 0; col[s] = 0; qu[t++] = s;
        while (h < t) { int u = qu[h++]; for (long a = off[u]; a < off[u + 1]; a++) { int w = adj[a]; if (col[w] < 0) { col[w] = 1 - col[u]; qu[t++] = w; } else if (col[w] == col[u]) bip = 0; } } }
    printf("n=%ld m=%ld simple=%s bipartite=%s components=%ld degree %ld..%ld\n", n, m, rep ? "NO" : "yes", bip ? "yes" : "NO", comps, dmin, dmax);
    long nb = (ns + 63) / 64; int maxsame = 0, maxdiff = 0; long far = 0, farsame = 0, unreach = 0;
    #pragma omp parallel
    {
        uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
        int ms = 0, md = 0; long fa = 0, fs = 0, un = 0;
        #pragma omp for schedule(dynamic, 1)
        for (long b = 0; b < nb; b++) {
            memset(vis, 0, n * 8); memset(fr, 0, n * 8);
            long s0 = b * 64; int cnt = (ns - s0 < 64) ? (int)(ns - s0) : 64;
            for (int i = 0; i < cnt; i++) { vis[src[s0 + i]] |= 1ULL << i; fr[src[s0 + i]] |= 1ULL << i; }
            uint64_t full = (cnt == 64) ? ~0ULL : ((1ULL << cnt) - 1);
            for (int t = 1;; t++) {
                int any = 0;
                for (long v = 0; v < n; v++) { uint64_t x = 0; for (long a = off[v]; a < off[v + 1]; a++) x |= fr[adj[a]];
                    x &= ~vis[v]; nx[v] = x; if (x) any = 1; }
                if (!any) break;
                for (long v = 0; v < n; v++) { if (nx[v]) { vis[v] |= nx[v]; if (t > D) { fa += __builtin_popcountll(nx[v]); if (t % 2 == 0) fs += __builtin_popcountll(nx[v]); }
                        if (t % 2 == 0) { if (t > ms) ms = t; } else { if (t > md) md = t; } } }
                uint64_t *tmp = fr; fr = nx; nx = tmp;
            }
            for (long v = 0; v < n; v++) un += cnt - __builtin_popcountll(vis[v] & full);
        }
        #pragma omp critical
        { if (ms > maxsame) maxsame = ms; if (md > maxdiff) maxdiff = md; far += fa; farsame += fs; unreach += un; }
        free(vis); free(fr); free(nx);
    }
    printf("sources: %ld (%s)\n", ns, argc > 5 ? "random sample of the range" : argc > 4 ? "range" : "all");
    printf("max distance same colour %d, different colour %d; ordered pairs at distance > %d: %ld; unreachable ordered pairs: %ld\n",
           maxsame, maxdiff, D, far, unreach);
    printf("same-colour ordered pairs at distance > %d: %ld (hub-graph condition: VALID if 0 and connected)\n", D, farsame);
    printf("RESULT %s (diameter %s %d)\n", (far == 0 && unreach == 0 && bip && !rep) ? "VALID" : "INVALID", (far == 0 && unreach == 0) ? "<=" : ">", D);
    return 0;
}
