/* hubs: "cubic Haar graph + hub orbits", a hub type for degree 4.
 * G group (hx table), |G| = N divisible by 4, K_A, K_B subgroups of order 4.
 * Vertices: A_base = G, A_hub = G/K_A (left cosets), B_base = G, B_hub = G/K_B;  n = 2N + N/2.
 * Edges:  (g)_A ~ (g s)_B for s in S = {e, x, y}   (cubic Haar part)
 *         (g)_A ~ (g K_B)_Bhub                       (each A_base vertex has one hub neighbour; a hub has 4)
 *         (g)_B ~ (g K_A)_Ahub
 * (A general attachment g -> g t K_B reduces to this by conjugating K_B.)  G acts by left multiplication with four
 * orbits, so four BFS roots decide the diameter: e_A, K_A, e_B, K_B.  Cost = sum over the 4 roots of the number of
 * vertices on the root's side not within D-1 (0 iff diameter <= D).
 * Search: random restarts + hill climbing on (x, y, K_A, K_B) (a screen, not exact).
 * Usage: hubs TABLE SECONDS(cpu) SEED [D] [OUTEDGES]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int N, D = 9, n, NA, NB;      /* NA = N + N/4 vertices per side */
static uint16_t *MT; static int *INV;
static inline int mul(int a, int b) { return MT[(size_t)a * N + b]; }
static int (*subs)[4]; static int nsub;
static int *labA, *labB;
static int *adj, *deg, *dist, *q;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int ord(int g) { int x = g, k = 1; while (x) { x = mul(x, g); k++; } return k; }
static void addsub(int a, int b, int c) { int s[4] = {0, a, b, c};
    for (int i = 1; i < 4; i++) for (int j = i + 1; j < 4; j++) if (s[i] > s[j]) { int t = s[i]; s[i] = s[j]; s[j] = t; }
    for (int i = 0; i < nsub; i++) if (!memcmp(subs[i], s, sizeof s)) return;
    memcpy(subs[nsub++], s, sizeof s); }
static void labels(int k, int *lab) { int c = 0; for (int y = 0; y < N; y++) lab[y] = -1;
    for (int y = 0; y < N; y++) if (lab[y] < 0) { for (int i = 0; i < 4; i++) lab[mul(y, subs[k][i])] = c; c++; } }
/* vertex ids: A_base g = g; A_hub c = N + c; B_base g = NA + g; B_hub c = NA + N + c */
static int bfs_far(int root, int lo, int hi) {
    for (int i = 0; i < n; i++) dist[i] = -1; int hd = 0, tl = 0; q[tl++] = root; dist[root] = 0;
    while (hd < tl) { int x = q[hd++]; if (dist[x] >= D - 1) continue; for (int i = 0; i < deg[x]; i++) { int y = adj[4 * x + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[tl++] = y; } } }
    int f = 0; for (int i = lo; i < hi; i++) if (dist[i] < 0) f++; return f;
}
static void edge(int a, int b) { adj[4 * a + deg[a]++] = b; adj[4 * b + deg[b]++] = a; }
static int cost(int x, int y, int ka, int kb, int lim) {
    static int lka = -1, lkb = -1;
    if (x == 0 || y == 0 || x == y) return 1 << 29;
    if (ka != lka) { labels(ka, labA); lka = ka; } if (kb != lkb) { labels(kb, labB); lkb = kb; }
    memset(deg, 0, sizeof(int) * n);
    for (int g = 0; g < N; g++) { edge(g, NA + g); edge(g, NA + mul(g, x)); edge(g, NA + mul(g, y));
        edge(g, NA + N + labB[g]); edge(NA + g, N + labA[g]); }
    int c = bfs_far(0, 0, NA); if (c > lim) return c;
    c += bfs_far(NA, NA, n); if (c > lim) return c;
    c += bfs_far(N + labA[0], 0, NA); if (c > lim) return c;
    c += bfs_far(NA + N + labB[0], NA, n); return c;
}
int main(int argc, char **argv) {
    FILE *fi = fopen(argv[1], "rb"); int32_t n32; if (!fi || fread(&n32, 4, 1, fi) != 1) return 2; N = n32;
    MT = malloc((size_t)N * N * 2); if (fread(MT, 2, (size_t)N * N, fi) != (size_t)N * N) return 2; fclose(fi);
    if (N % 4) { printf("N not divisible by 4\n"); return 0; }
    double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; if (argc > 4) D = atoi(argv[4]);
    NA = N + N / 4; n = 2 * NA;
    adj = malloc(sizeof(int) * 4 * n); deg = malloc(sizeof(int) * n); dist = malloc(sizeof(int) * n); q = malloc(sizeof(int) * n);
    labA = malloc(N * 4); labB = malloc(N * 4);
    INV = malloc(N * 4); for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul(a, b) == 0) { INV[a] = b; break; }
    subs = malloc(sizeof(int[4]) * 200000); nsub = 0;
    int *o = malloc(N * 4); for (int g = 0; g < N; g++) o[g] = g ? ord(g) : 1;
    for (int g = 1; g < N; g++) if (o[g] == 4) addsub(g, mul(g, g), mul(g, mul(g, g)));
    int *invs = malloc(N * 4), ni = 0; for (int g = 1; g < N; g++) if (o[g] == 2) invs[ni++] = g;
    for (int i = 0; i < ni && nsub < 190000; i++) for (int j = i + 1; j < ni; j++) { int a = invs[i], b = invs[j];
        if (mul(a, b) == mul(b, a)) addsub(a, b, mul(a, b)); }
    printf("N %d n %d: %d subgroups of order 4\n", N, n, nsub); fflush(stdout);
    if (!nsub) return 0;
    clock_t t0 = clock(); int best = 1 << 30, bb[4] = {0}; long ev = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        int v[4] = { 1 + (int)(rnd() % (N - 1)), 1 + (int)(rnd() % (N - 1)), (int)(rnd() % nsub), (int)(rnd() % nsub) };
        int c = cost(v[0], v[1], v[2], v[3], 1 << 30); ev++; int stall = 0;
        while (stall < 300) { int w[4]; memcpy(w, v, sizeof w); int k = rnd() % 4;
            if (k < 2) w[k] = 1 + rnd() % (N - 1); else w[k] = rnd() % nsub;
            int c2 = cost(w[0], w[1], w[2], w[3], c); ev++;
            if (c2 <= c) { stall = c2 < c ? 0 : stall + 1; c = c2; memcpy(v, w, sizeof w); } else stall++; }
        if (c < best) { best = c; memcpy(bb, v, sizeof bb); printf("best %d  x %d y %d KA {%d,%d,%d,%d} KB {%d,%d,%d,%d} (%.0fs, %ld evals)\n", best, bb[0], bb[1],
            subs[bb[2]][0], subs[bb[2]][1], subs[bb[2]][2], subs[bb[2]][3], subs[bb[3]][0], subs[bb[3]][1], subs[bb[3]][2], subs[bb[3]][3], (double)(clock() - t0) / CLOCKS_PER_SEC, ev); fflush(stdout); }
        if (!best) break;
    }
    printf("FINAL best %d evals %ld\n", best, ev);
    if (argc > 5 && best < (1 << 29)) { cost(bb[0], bb[1], bb[2], bb[3], 1 << 30); FILE *fo = fopen(argv[5], "w"); fprintf(fo, "%d\n", n);
        for (int a = 0; a < NA; a++) for (int i = 0; i < 4; i++) fprintf(fo, "%d %d\n", a, adj[4 * a + i]); fclose(fo); }
    return 0;
}
