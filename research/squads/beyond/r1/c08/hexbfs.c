/* hexbfs.c: checks the incidence graph of H(q) written by hexgen2 (hex/hex_q{q}.bin).
   Vertices: points 0..N-1, lines N..2N-1 (N = L). Builds the CSR graph, checks degrees (every vertex has q+1
   neighbours), that every edge joins a point and a line (bipartition), that no vertex repeats a neighbour,
   then runs BFS from: every point of line 0 and every line through point 0 (the 2(q+1) local sources), and
   NRAND random vertices (seeded). For each BFS it prints the level sizes of the first levels, the eccentricity,
   and the max eccentricity over all BFS runs. Moore expectation for the incidence graph of a generalized
   hexagon (girth 12, diameter 6): level sizes 1, q+1, (q+1)q, (q+1)q^2, (q+1)q^3, (q+1)q^4, q^5, ecc 6.
   Usage: hexbfs hex_q{q}.bin NRAND SEED   (single thread) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("open"); return 1; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0]; int64_t N = hdr[1], L = hdr[2]; int Q1 = q + 1;
    if (N != L) { fprintf(stderr, "N != L\n"); return 1; }
    int64_t n = 2 * N, M = N * Q1;               /* M incidences = edges */
    int32_t *lines = malloc(sizeof(int32_t) * M);
    if (fread(lines, 4, M, f) != (size_t)M) { fprintf(stderr, "short read\n"); return 1; }
    fclose(f);
    /* CSR: point p -> lines (adjacency offsets 2-sided) */
    int64_t *off = malloc(sizeof(int64_t) * (n + 1));
    int32_t *adj = malloc(sizeof(int32_t) * 2 * M);
    int64_t *fillp = malloc(sizeof(int64_t) * n);
    for (int64_t v = 0; v <= n; v++) off[v] = v * Q1;   /* every vertex has degree q+1 (checked below) */
    int64_t *cnt = calloc(N, sizeof(int64_t));
    for (int64_t l = 0; l < L; l++) for (int s = 0; s < Q1; s++) {
        int64_t p = lines[l * Q1 + s];
        if (p < 0 || p >= N) { fprintf(stderr, "bad point id\n"); return 1; }
        cnt[p]++;
    }
    for (int64_t p = 0; p < N; p++) if (cnt[p] != Q1) { fprintf(stderr, "point %lld has degree %lld\n", (long long)p, (long long)cnt[p]); return 1; }
    for (int64_t v = 0; v < n; v++) fillp[v] = off[v];
    for (int64_t l = 0; l < L; l++) for (int s = 0; s < Q1; s++) {
        int64_t p = lines[l * Q1 + s], lv = N + l;
        adj[fillp[p]++] = (int32_t)lv;          /* point -> line */
        adj[fillp[lv]++] = (int32_t)p;          /* line -> point */
    }
    /* checks: each line has Q1 distinct points, each vertex has Q1 distinct neighbours, bipartite by construction */
    int64_t bad = 0;
    for (int64_t v = 0; v < n; v++) {
        int32_t *a = adj + off[v];
        for (int i = 0; i < Q1; i++) {
            if ((v < N) == (a[i] < N)) bad++;          /* same side neighbour: not bipartite */
            for (int j = 0; j < i; j++) if (a[i] == a[j]) bad++;
        }
    }
    printf("q=%d vertices=%lld (points %lld + lines %lld) edges=%lld degree=%d everywhere, bipartite and simple violations=%lld\n",
           q, (long long)n, (long long)N, (long long)L, (long long)M, Q1, (long long)bad);
    if (bad) { printf("RESULT INVALID\n"); return 1; }

    int32_t *dist = malloc(sizeof(int32_t) * n), *queue = malloc(sizeof(int32_t) * n);
    int64_t maxecc = 0, nbfs = 0; int levok = 1;
    /* expected Moore level sizes from a vertex: L0=1, L_i=(q+1)q^{i-1} (i=1..5), L6=q^5 */
    int64_t exp_lv[7]; exp_lv[0] = 1; int64_t pw = 1;
    for (int i = 1; i <= 5; i++) { exp_lv[i] = Q1 * pw; pw *= q; }
    exp_lv[6] = pw;                                    /* pw = q^5 after the loop */
    srand(atoi(argv[3]));
    int64_t nrand = atoll(argv[2]);
    int64_t total_src = 2 * Q1 + nrand;
    for (int64_t it = 0; it < total_src; it++) {
        int64_t src;
        if (it < Q1) src = lines[it];                               /* the q+1 points of line 0 */
        else if (it < 2 * Q1) src = adj[off[0] + (it - Q1)];        /* the q+1 lines through point 0 */
        else src = (((int64_t)rand() << 31) | (int64_t)rand()) % n; /* random vertices */
        for (int64_t v = 0; v < n; v++) dist[v] = -1;
        int64_t qh = 0, qt = 0; queue[qt++] = (int32_t)src; dist[src] = 0;
        int64_t lvcount[64]; memset(lvcount, 0, sizeof lvcount);
        while (qh < qt) {
            int32_t v = queue[qh++]; int d = dist[v]; lvcount[d]++;
            int32_t *a = adj + off[v];
            for (int i = 0; i < Q1; i++) { int32_t w = a[i]; if (dist[w] < 0) { dist[w] = d + 1; queue[qt++] = w; } }
        }
        if (qt != n) { printf("source %lld: NOT connected (reached %lld of %lld)\n", (long long)src, (long long)qt, (long long)n); return 1; }
        int ecc = 0; for (int d = 0; d < 64; d++) if (lvcount[d]) ecc = d;
        int isp = src < N;
        if (ecc > maxecc) maxecc = ecc;
        nbfs++;
        int ok = (ecc == 6);
        for (int d = 0; d <= 6; d++) if (lvcount[d] != exp_lv[d]) ok = 0;
        if (!ok) levok = 0;
        if (it < 3 || !ok || it == total_src - 1) {
            printf("source %s %lld ecc %d levels", isp ? "point" : "line", (long long)src, ecc);
            for (int d = 0; d <= ecc && d < 8; d++) printf(" %lld", (long long)lvcount[d]);
            printf("  %s\n", ok ? "(matches Moore levels)" : "(MISMATCH with Moore levels)");
        }
    }
    printf("BFS sources run=%lld (local: %d points of line 0 and %d lines through point 0; random: %lld)\n",
           (long long)nbfs, Q1, Q1, (long long)nrand);
    printf("max eccentricity over BFS runs=%lld; all runs match expected Moore level sizes: %s\n",
           (long long)maxecc, levok ? "yes" : "no");
    printf("RESULT %s q=%d n=%lld maxdiam_seen=%lld\n", (maxecc <= 6 && levok) ? "VALID" : "INVALID", q, (long long)n, (long long)maxecc);
    return (maxecc <= 6 && levok) ? 0 : 1;
}
