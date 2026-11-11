/* mixed: "one regular side, one side with point stabilisers of order 2" graphs (a hub type between Haar graphs and
 * bi-coset graphs), for a group G given by an hx table.
 *
 * A = G (regular).  B = G/H1 u G/H2, H_i = {e, h_i}, h_i involutions (|B| = N/2 + N/2 = N, so n = 2N).
 * Edges: (g)_A ~ (g d H1), (g d' H1), (g f H2), (g f' H2)   for d, d', f, f' in G (left multiplication by G is an
 * automorphism, so A is one orbit and B1, B2 are orbits with stabilisers conjugate to H1, H2).  Every B vertex has
 * degree 4.  WLOG d = e (replace all four by c^-1 times them).  Three BFS roots decide the diameter: e_A, H1, H2.
 * Cost = #A not within D-1 of e_A + #B not within D-1 of H1 + #B not within D-1 of H2 (0 iff diameter <= D).
 *
 * Search: random restarts + tabu-free hill climbing with random single changes (screen, not exact).
 * Usage: mixed TABLE SECONDS SEED [D] [OUTEDGES]   (SECONDS is CPU time; OUTEDGES gets the best graph)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int N, D = 9, n;
static uint16_t *MT; static int *INV;
static inline int mul(int a, int b) { return MT[(size_t)a * N + b]; }
static int *inv_list, ninv;
static int *lab1, *lab2;   /* coset label of y in G/H1, G/H2: 0..N/2-1 */
static int *rep1, *rep2;
static int adj[4 * 20000], deg[20000], dist[20000], q[20000];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void setlabels(int h, int *lab, int *rep) {
    int c = 0; for (int y = 0; y < N; y++) lab[y] = -1;
    for (int y = 0; y < N; y++) if (lab[y] < 0) { lab[y] = c; lab[mul(y, h)] = c; rep[c] = y; c++; }
}
static int bfs_far(int root, int lo, int hi) {
    for (int i = 0; i < n; i++) dist[i] = -1;
    int hd = 0, tl = 0; q[tl++] = root; dist[root] = 0;
    while (hd < tl) { int x = q[hd++]; if (dist[x] >= D - 1) continue; for (int i = 0; i < deg[x]; i++) { int y = adj[4 * x + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[tl++] = y; } } }
    int far = 0; for (int i = lo; i < hi; i++) if (dist[i] < 0) far++; return far;
}
/* vertices: A g = 0..N-1; B1 label c = N + c; B2 label c = N + N/2 + c */
static int cost(int h1, int h2, int dp, int f, int fp, int lim) {
    static int lh1 = -1, lh2 = -1;
    if (h1 != lh1) { setlabels(h1, lab1, rep1); lh1 = h1; }
    if (h2 != lh2) { setlabels(h2, lab2, rep2); lh2 = h2; }
    if (lab1[0] == lab1[dp] || lab2[f] == lab2[fp]) return 1 << 29;
    memset(deg, 0, sizeof(int) * n);
    for (int g = 0; g < N; g++) {
        int nb[4] = { N + lab1[g], N + lab1[mul(g, dp)], N + N / 2 + lab2[mul(g, f)], N + N / 2 + lab2[mul(g, fp)] };
        for (int i = 0; i < 4; i++) { int b = nb[i]; if (deg[b] >= 4) return 1 << 29; adj[4 * g + i] = b; adj[4 * b + deg[b]++] = g; }
        deg[g] = 4;
    }
    int c = bfs_far(0, 0, N); if (c > lim) return c;
    c += bfs_far(N + lab1[0], N, n); if (c > lim) return c;
    c += bfs_far(N + N / 2 + lab2[0], N, n); return c;
}
int main(int argc, char **argv) {
    FILE *fi = fopen(argv[1], "rb"); int32_t n32; if (!fi || fread(&n32, 4, 1, fi) != 1) return 2; N = n32; n = 2 * N;
    MT = malloc((size_t)N * N * 2); if (fread(MT, 2, (size_t)N * N, fi) != (size_t)N * N) return 2; fclose(fi);
    double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; if (argc > 4) D = atoi(argv[4]);
    INV = malloc(N * 4); for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul(a, b) == 0) { INV[a] = b; break; }
    inv_list = malloc(N * 4); ninv = 0; int ncen = 0;
    for (int g = 1; g < N; g++) if (mul(g, g) == 0) { int central = 1; for (int x = 0; x < N && central; x++) if (mul(g, x) != mul(x, g)) central = 0;
        if (central) ncen++; else inv_list[ninv++] = g; }
    printf("involutions: %d non-central, %d central (excluded)\n", ninv, ncen);
    if (!ninv || N % 2) { printf("no involutions\n"); return 0; }
    lab1 = malloc(N * 4); lab2 = malloc(N * 4); rep1 = malloc(N * 4); rep2 = malloc(N * 4);
    clock_t t0 = clock(); int best = 1 << 30; long evals = 0; int bb[5] = {0};
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        int v[5] = { inv_list[rnd() % ninv], inv_list[rnd() % ninv], (int)(rnd() % N), (int)(rnd() % N), (int)(rnd() % N) };
        int c = cost(v[0], v[1], v[2], v[3], v[4], 1 << 30); evals++;
        int stall = 0;
        while (stall < 400) {
            int w[5]; memcpy(w, v, sizeof w); int k = rnd() % 5;
            if (k < 2) w[k] = inv_list[rnd() % ninv]; else w[k] = rnd() % N;
            int c2 = cost(w[0], w[1], w[2], w[3], w[4], c); evals++;
            if (c2 <= c) { if (c2 < c) stall = 0; else stall++; c = c2; memcpy(v, w, sizeof w); } else stall++;
        }
        if (c < best) { best = c; memcpy(bb, v, sizeof bb); printf("best %d  h1 %d h2 %d d' %d f %d f' %d  (%.1fs, %ld evals)\n", best, bb[0], bb[1], bb[2], bb[3], bb[4], (double)(clock() - t0) / CLOCKS_PER_SEC, evals); fflush(stdout); }
        if (best == 0) break;
    }
    printf("FINAL best %d evals %ld  params h1 %d h2 %d d' %d f %d f' %d\n", best, evals, bb[0], bb[1], bb[2], bb[3], bb[4]);
    if (argc > 5 && best < (1 << 29)) { cost(bb[0], bb[1], bb[2], bb[3], bb[4], 1 << 30);
        FILE *fo = fopen(argv[5], "w"); fprintf(fo, "%d\n", n); for (int g = 0; g < N; g++) for (int i = 0; i < 4; i++) fprintf(fo, "%d %d\n", g, adj[4 * g + i]); fclose(fo); }
    return 0;
}
