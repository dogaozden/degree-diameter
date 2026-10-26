/* c06.c: Z8-voltage lift of W(q) (q prime) with three extra edges per vertex (Delta = q+4).
 * Lift vertices (x,h), x in base (points 0..N-1, lines N..2N-1), h in Z8; edge (x,h)-(y,h+g) for base edge (x,y,g).
 * cost = #{(v,u,s): no walk of length <= 5 from (v,0) to (u,s)} over all base v, u, s in Z8  (0 <=> diameter <= 5,
 *        since the lift is fibre-transitive).  Usage: c06 q SEED VOLTAGE_SPEC [OUT_EDGES]
 *   VOLTAGE_SPEC: comma list "k:g" = extra matching k (0..2) with voltage g in Z8, e.g. "0:1,0:4,1:2" (doubled 0).
 *                 "rnd" as the first token of spec = random Z8 voltages on the GQ flags (seed SEED); "zero" = all 0.
 *   With OUT_EDGES, writes the apsp input (n = 8*2*N first line) for a zero-cost lift.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define M 8
static int q, N;
static int *lines;          /* L*(q+1) point ids */
static uint8_t *inc;        /* N x N incidence matrix (point, line) */
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: c06 q SEED SPEC [OUT]\n"); return 1; }
    q = atoi(argv[1]); rs = 88172645463325252ULL ^ (uint64_t)atoll(argv[2]) * 2654435761ULL; if (!rs) rs = 1;
    char fn[256]; sprintf(fn, "gq/gq_q%d.bin", q);
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); return 1; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    N = hdr[1]; int Q1 = q + 1; lines = malloc(4L * hdr[2] * Q1);
    if (fread(lines, 4, (size_t)hdr[2] * Q1, f) != (size_t)hdr[2] * Q1) return 1; fclose(f);
    int V = 2 * N;
    inc = calloc((size_t)N * N, 1);
    /* base edges: flags (p, N+L) with voltage; extra matchings */
    int maxE = N * Q1 + 3 * N + 8;
    int *eu = malloc(sizeof(int) * maxE), *ev = malloc(sizeof(int) * maxE), *eg = malloc(sizeof(int) * maxE);
    int E = 0;
    for (int l = 0; l < N; l++) for (int s = 0; s < Q1; s++) { int p = lines[l * Q1 + s]; inc[(size_t)p * N + l] = 1;
        eu[E] = p; ev[E] = N + l; eg[E] = 0; E++; }
    int nflag = E;
    /* spec */
    char *spec = strdup(argv[3]);
    int zero = 0, rndv = 0;
    if (!strcmp(spec, "zero")) zero = 1;
    if (!strcmp(spec, "rnd")) rndv = 1;
    int nm = 0; int mk[3] = {-1, -1, -1}, mv[3] = {0, 0, 0}, cnt = 0;
    if (!zero && !rndv) {
        char *tok = strtok(spec, ",");
        while (tok) { int k, g; if (sscanf(tok, "%d:%d", &k, &g) != 2 || k < 0 || k > 2) { fprintf(stderr, "bad spec %s\n", tok); return 1; }
            mk[cnt] = k; mv[cnt] = g; cnt++; if (k + 1 > nm) nm = k + 1; tok = strtok(NULL, ","); }
    }
    if (rndv) { for (int i = 0; i < nflag; i++) eg[i] = rnd() % M; }
    if (!zero && !rndv) { if (cnt != 3) { fprintf(stderr, "need 3 extra edges\n"); return 1; } }
    /* build nm random perfect matchings (points -> lines) avoiding incidences and each other (Kuhn on complement) */
    int *mat = malloc(sizeof(int) * N * 3);
    for (int k = 0; k < nm; k++) {
        int *pl = malloc(sizeof(int) * N), *lp = malloc(sizeof(int) * N), *seen = malloc(sizeof(int) * N);
        for (int i = 0; i < N; i++) { pl[i] = -1; lp[i] = -1; }
        int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        /* forbidden: incidences and previously fixed matchings (stored in mat[0..k-1]) */
        for (int a = 0; a < N; a++) {
            int p = ord[a];
            for (int i = 0; i < N; i++) seen[i] = 0;
            /* iterative DFS augmenting path with recursion-free BFS */
            int *prev = malloc(sizeof(int) * N), *queueP = malloc(sizeof(int) * N), qh = 0, qt = 0;
            int *lpar = malloc(sizeof(int) * N);
            for (int i = 0; i < N; i++) lpar[i] = -1;
            queueP[qt++] = p; prev[p] = -1; int foundL = -1, fromP = -1;
            while (qh < qt && foundL < 0) {
                int x = queueP[qh++];
                int start = rnd() % N;
                for (int t = 0; t < N && foundL < 0; t++) { int l = (start + t) % N;
                    if (inc[(size_t)x * N + l] || seen[l]) continue;
                    int bad = 0; for (int kk = 0; kk < k; kk++) if (mat[kk * N + x] == l) { bad = 1; break; }
                    if (bad) continue;
                    seen[l] = 1; lpar[l] = x;
                    if (lp[l] < 0) { foundL = l; fromP = x; }
                    else { int y = lp[l]; if (qt < N) queueP[qt++] = y; prev[y] = l; }
                }
            }
            if (foundL < 0) { fprintf(stderr, "matching failed\n"); return 1; }
            /* augment along alternating path */
            int l = foundL;
            while (1) { int x = lpar[l]; int nxtl = pl[x]; pl[x] = l; lp[l] = x; if (x == p) break; l = nxtl; }
            free(prev); free(queueP); free(lpar);
        }
        for (int i = 0; i < N; i++) mat[k * N + i] = pl[i];
        free(pl); free(lp); free(seen); free(ord);
    }
    if (!zero && !rndv) {
        for (int i = 0; i < cnt; i++) { int k = mk[i];
            eu[E] = 0; ev[E] = 0; eg[E] = mv[i];
            /* store matching k edges */
            for (int p = 0; p < N; p++) { eu[E] = p; ev[E] = N + mat[k * N + p]; eg[E] = mv[i]; E++; }
        }
    } else if (zero) {
        /* no extra edges */
    }
    /* adjacency */
    int *deg = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) { deg[eu[e]]++; deg[ev[e]]++; }
    int **adjv = malloc(sizeof(int*) * V), **adjg = malloc(sizeof(int*) * V);
    for (int v = 0; v < V; v++) { adjv[v] = malloc(sizeof(int) * deg[v]); adjg[v] = malloc(sizeof(int) * deg[v]); deg[v] = 0; }
    for (int e = 0; e < E; e++) { int u = eu[e], w = ev[e], g = eg[e];
        adjv[u][deg[u]] = w; adjg[u][deg[u]] = g; deg[u]++;
        adjv[w][deg[w]] = u; adjg[w][deg[w]] = (M - g) % M; deg[w]++; }
    int maxdeg = 0; for (int v = 0; v < V; v++) if (deg[v] > maxdeg) maxdeg = deg[v];
    fprintf(stderr, "V=%d (lift %d) E=%d maxdeg=%d\n", V, V * M, E, maxdeg);
    /* cost: for each source v, propagate bit masks over 5 steps */
    uint8_t *cur = malloc(V), *nxt = malloc(V), *reach = malloc(V);
    long long total = 0;
    for (int src = 0; src < V; src++) {
        memset(cur, 0, V); memset(reach, 0, V);
        cur[src] = 1; reach[src] = 1;
        for (int t = 0; t < 5; t++) {
            memset(nxt, 0, V);
            for (int u = 0; u < V; u++) { uint8_t m = cur[u]; if (!m) continue;
                for (int j = 0; j < deg[u]; j++) { int w = adjv[u][j], g = adjg[u][j];
                    uint8_t r = (uint8_t)(((m << g) | (m >> (M - g))) & 0xFF); nxt[w] |= r; } }
            for (int w = 0; w < V; w++) reach[w] |= nxt[w];
            uint8_t *tmp = cur; cur = nxt; nxt = tmp;
        }
        for (int w = 0; w < V; w++) { int c = __builtin_popcount(reach[w]); total += M - c; }
    }
    /* note: the lift is fibre-transitive; each (v,0) source counts its own uncovered targets */
    printf("COST %lld\n", total);
    if (argc > 4 && total == 0) {
        FILE *o = fopen(argv[4], "w");
        fprintf(o, "%d\n", V * M);
        for (int u = 0; u < V; u++) for (int j = 0; j < deg[u]; j++) { int w = adjv[u][j], g = adjg[u][j];
            if (w < u) continue; /* each undirected base edge once */
            for (int h = 0; h < M; h++) fprintf(o, "%d %d\n", u * M + h, w * M + (h + g) % M); }
        fclose(o);
    }
    return 0;
}
