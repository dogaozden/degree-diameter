/* c3ins: 169-vertex candidates from known graphs (deep-37 round 1, card c3).
 * mode vdel IN OUT : IN = cubic bipartite graph on 170 vertices (85+85). For every vertex v, delete v and report far
 *                    of the remaining 169 graph (the three former neighbours of v become degree-2 vertices). Writes the
 *                    best 169-graph to OUT (edge list, relabelled 0..168).
 * mode ins3 IN OUT : IN = cubic bipartite graph on 168 vertices (84+84). Enumerate all triples of edges (a1,b1),(a2,b2),
 *                    (a3,b3) with distinct a's and distinct b's, delete them and add a new vertex z (side A) adjacent to
 *                    b1,b2,b3. Reports the best far; writes it to OUT.
 * far = unordered pairs at distance > 7 (bit-parallel BFS). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
#define MAXN 192
int n, adj[MAXN][3], deg[MAXN], side[MAXN];
static int far_eval(void) {
    static u64 M1[MAXN][3], M2[MAXN][3];
    u64 (*M)[3] = M1, (*NM)[3] = M2;
    for (int v = 0; v < n; v++) { M[v][0] = M[v][1] = M[v][2] = 0; M[v][v >> 6] |= 1ULL << (v & 63); }
    for (int k = 0; k < 7; k++) {
        for (int v = 0; v < n; v++) {
            u64 x0 = M[v][0], x1 = M[v][1], x2 = M[v][2];
            for (int i = 0; i < deg[v]; i++) { int u = adj[v][i]; x0 |= M[u][0]; x1 |= M[u][1]; x2 |= M[u][2]; }
            NM[v][0] = x0; NM[v][1] = x1; NM[v][2] = x2;
        }
        u64 (*t)[3] = M; M = NM; NM = t;
    }
    long far2 = 0;
    for (int v = 0; v < n; v++) far2 += n - (__builtin_popcountll(M[v][0]) + __builtin_popcountll(M[v][1]) + __builtin_popcountll(M[v][2]));
    return (int)(far2 / 2);
}
static void add_edge(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static void rem_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; break; }
    for (int i = 0; i < deg[b]; i++) if (adj[b][i] == a) { adj[b][i] = adj[b][--deg[b]]; break; }
}
static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++) for (int i = 0; i < deg[v]; i++) if (adj[v][i] > v) fprintf(f, "%d %d\n", v, adj[v][i]);
    fclose(f);
}
static int read_graph(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    if (fscanf(f, "%d", &n) != 1) exit(2);
    int a, b; int m = 0; int E[400][2];
    while (fscanf(f, "%d %d", &a, &b) == 2) { E[m][0] = a; E[m][1] = b; m++; }
    fclose(f);
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) add_edge(E[i][0], E[i][1]);
    /* sides by BFS */
    for (int v = 0; v < n; v++) side[v] = -1;
    int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
    return m;
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: c3ins vdel|ins3 IN OUT\n"); return 2; }
    int m = read_graph(argv[2]);
    int best = 1 << 30;
    if (!strcmp(argv[1], "vdel")) {
        int E[400][2], k = 0;
        for (int v = 0; v < n; v++) for (int i = 0; i < deg[v]; i++) if (adj[v][i] > v) { E[k][0] = v; E[k][1] = adj[v][i]; k++; }
        /* snapshot adjacency */
        static int S_adj[MAXN][3], S_deg[MAXN];
        memcpy(S_adj, adj, sizeof adj); memcpy(S_deg, deg, sizeof deg);
        int N0 = n;
        int bestv = -1;
        for (int v = 0; v < N0; v++) {
            if (side[v] != 1) continue; /* delete a B-vertex (side 1) */
            /* build graph without v: relabel u>v to u-1 */
            int map[MAXN]; int c = 0;
            for (int u = 0; u < N0; u++) map[u] = (u == v) ? -1 : c++;
            n = N0 - 1;
            for (int u = 0; u < n; u++) deg[u] = 0;
            for (int u = 0; u < N0; u++) if (u != v) {
                for (int i = 0; i < S_deg[u]; i++) { int w = S_adj[u][i]; if (w != v && u < w) add_edge(map[u], map[w]); }
            }
            /* the new 169 graph has vertex order: A = old side 0 (85), B = old side 1 minus v (84) */
            int f = far_eval();
            if (f < best) { best = f; bestv = v; fprintf(stderr, "vdel v=%d far=%d\n", v, f); write_graph(argv[3]); }
            n = N0; memcpy(adj, S_adj, sizeof adj); memcpy(deg, S_deg, sizeof deg);
        }
        printf("vdel DONE best=%d deleted=%d\n", best, bestv);
    } else {
        /* ins3 */
        int N0 = n;
        int E[400][2], k = 0;
        for (int v = 0; v < N0; v++) if (side[v] == 0) for (int i = 0; i < deg[v]; i++) { E[k][0] = v; E[k][1] = adj[v][i]; k++; }
        if (k != 252) fprintf(stderr, "warning: %d edges\n", k);
        int z = N0;
        int cnt = 0;
        for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) for (int l = j + 1; l < k; l++) {
            int a[3] = {E[i][0], E[j][0], E[l][0]}, b[3] = {E[i][1], E[j][1], E[l][1]};
            if (a[0] == a[1] || a[0] == a[2] || a[1] == a[2]) continue;
            if (b[0] == b[1] || b[0] == b[2] || b[1] == b[2]) continue;
            n = N0 + 1;
            deg[z] = 0;
            for (int t = 0; t < 3; t++) rem_edge(a[t], b[t]);
            for (int t = 0; t < 3; t++) add_edge(z, b[t]);
            int f = far_eval();
            cnt++;
            if (f < best) { best = f; fprintf(stderr, "ins3 i=%d j=%d l=%d far=%d\n", i, j, l, f); write_graph(argv[3]); }
            for (int t = 0; t < 3; t++) rem_edge(z, b[t]);
            for (int t = 0; t < 3; t++) add_edge(a[t], b[t]);
            n = N0;
        }
        printf("ins3 DONE best=%d triples=%d\n", best, cnt);
    }
    return 0;
}
