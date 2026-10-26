/* liftcheck: diameter check of a voltage lift over Z_M (bipartite base).
   Input (stdin or file): "nA nB M" then edges "a b v" meaning (a,g) ~ (b, g+v mod M), a in side A, b in side B.
   Since the lift is Z_M-symmetric, BFS from (x,0) for every base vertex x covers all sources.
   Output: max eccentricity, number of (source, target) pairs at distance > D, per-side summary.
   usage: liftcheck file D [verbose] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: liftcheck file D [verbose]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]); int verbose = argc > 3 ? atoi(argv[3]) : 0;
    int nA, nB, M; if (fscanf(f, "%d %d %d", &nA, &nB, &M) != 3) return 1;
    int nb = nA + nB; long cap = 1 << 16, ne = 0;
    int *ea = malloc(cap * sizeof(int)), *eb = malloc(cap * sizeof(int)), *ev = malloc(cap * sizeof(int));
    int a, b, v;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) {
        if (ne == cap) { cap *= 2; ea = realloc(ea, cap * sizeof(int)); eb = realloc(eb, cap * sizeof(int)); ev = realloc(ev, cap * sizeof(int)); }
        ea[ne] = a; eb[ne] = nA + b; ev[ne] = ((v % M) + M) % M; ne++;
    }
    fclose(f);
    int *deg = calloc(nb, sizeof(int));
    for (long i = 0; i < ne; i++) { deg[ea[i]]++; deg[eb[i]]++; }
    int *off = malloc((nb + 1) * sizeof(int)); off[0] = 0;
    for (int i = 0; i < nb; i++) off[i + 1] = off[i] + deg[i];
    int *adj = malloc(2 * ne * sizeof(int)), *adv = malloc(2 * ne * sizeof(int)), *fill = calloc(nb, sizeof(int));
    for (long i = 0; i < ne; i++) {
        int x = ea[i], y = eb[i];
        adj[off[x] + fill[x]] = y; adv[off[x] + fill[x]] = ev[i]; fill[x]++;
        adj[off[y] + fill[y]] = x; adv[off[y] + fill[y]] = (M - ev[i]) % M; fill[y]++;
    }
    int maxdeg = 0; for (int i = 0; i < nb; i++) if (deg[i] > maxdeg) maxdeg = deg[i];
    long N = (long)nb * M;
    int *dist = malloc(N * sizeof(int)), *queue = malloc(N * sizeof(int));
    long bad = 0; int maxecc = 0; long badA = 0, badB = 0;
    /* simple-graph check: parallel base edges must carry distinct voltages */
    long multi = 0;
    for (int x = 0; x < nb; x++)
        for (int i = off[x]; i < off[x + 1]; i++)
            for (int j = i + 1; j < off[x + 1]; j++)
                if (adj[i] == adj[j] && adv[i] == adv[j]) multi++;
    for (int s = 0; s < nb; s++) {
        for (long i = 0; i < N; i++) dist[i] = -1;
        long src = (long)s * M; dist[src] = 0; long qh = 0, qt = 0; queue[qt++] = src;
        while (qh < qt) {
            long u = queue[qh++]; int x = u / M, g = u % M;
            for (int i = off[x]; i < off[x + 1]; i++) {
                long w = (long)adj[i] * M + (g + adv[i]) % M;
                if (dist[w] < 0) { dist[w] = dist[u] + 1; queue[qt++] = w; }
            }
        }
        int ecc = 0; long b2 = 0;
        for (long i = 0; i < N; i++) {
            if (dist[i] < 0) { ecc = 1 << 20; b2++; continue; }
            if (dist[i] > ecc) ecc = dist[i];
            if (dist[i] > D) b2++;
        }
        if (ecc > maxecc) maxecc = ecc;
        bad += b2; if (s < nA) badA += b2; else badB += b2;
        if (verbose && b2) printf("source %d (%s) ecc %d far %ld\n", s, s < nA ? "A" : "B", ecc, b2);
    }
    printf("lift: nA=%d nB=%d M=%d vertices=%ld edges=%ld maxdeg=%d repeated-voltage parallel pairs=%ld\n", nA, nB, M, N, ne * M, maxdeg, multi);
    printf("RESULT maxecc=%d far_pairs=%ld (A sources %ld, B sources %ld) D=%d %s\n", maxecc, bad, badA, badB, D,
           (bad == 0 && multi == 0) ? "VALID" : "INVALID");
    return 0;
}
