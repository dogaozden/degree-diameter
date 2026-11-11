/* bicos: exhaustive search over the bi-coset graphs of the Frobenius group Z_p x| Z_k (affine maps x -> r^j x + a,
 * r of order k mod p) with vertex stabiliser H = <zeta>, zeta = r^k', |H| = h, k = h k'.
 *
 * Vertices on each side: (a, j), a in Z_p, j in Z_k'  (the cosets gH).  Edges: (a,j)_A ~ (a + r^j u, j + v)_B for
 * (u,v) in N0, where N0 is a zeta-invariant 4-subset of Z_p x Z_k' (r^j taken with 0 <= j < k'; the zeta-invariance
 * makes the graph independent of that choice, and Z_p x| Z_k acts transitively on each side).
 * If gcd(h, k') = 1 the graph is a Haar graph of Z_p x| Z_k'; if gcd(h, k') > 1 it is not a Haar graph of that group.
 *
 * zeta-orbits: (0,v) fixed, (u,v) with u != 0 an orbit of size h.  4 = h + h (h = 2), h + 1 + 1 (h = 2), 3 + 1 (h = 3).
 * Normalisation: scaling u -> c u (c in Z_p^*), translation of v (v -> v + t on both B... i.e. relabel B fibres), so
 * the first orbit is (1, 0)-orbit; the rest is enumerated in full.  Two roots (0,0)_A, (0,0)_B decide the diameter.
 *
 * Usage: bicos p k h r D  -> prints the best far count and every set reaching it (up to 20) as "far u1 v1 u2 v2 ..."
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int p, k, h, kp, r, D, n, nv;
static long R[4096];
static int *adj; /* 4 per vertex; A = 0..nv-1, B = nv..2nv-1 */
static int *dist, *q;
static int bfs_far(int root) {
    for (int i = 0; i < n; i++) dist[i] = -1;
    int hd = 0, tl = 0; q[tl++] = root; dist[root] = 0;
    while (hd < tl) { int x = q[hd++]; if (dist[x] >= D) continue; for (int i = 0; i < 4; i++) { int y = adj[4 * x + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[tl++] = y; } } }
    int far = 0; for (int i = 0; i < n; i++) if (dist[i] < 0) far++;
    return far;
}
static int build(int (*N0)[2]) {
    /* A vertex (a,j) = a + p*j; B = nv + a + p*j */
    int *deg = calloc(n, sizeof(int));
    for (int j = 0; j < kp; j++) for (int a = 0; a < p; a++) { int x = a + p * j;
        for (int i = 0; i < 4; i++) { long b = (a + R[j] * N0[i][0]) % p; int l = (j + N0[i][1]) % kp; int y = nv + (int)b + p * l;
            if (deg[y] >= 4) { free(deg); return 0; }
            adj[4 * x + i] = y; adj[4 * y + deg[y]++] = x; } }
    for (int y = nv; y < n; y++) if (deg[y] != 4) { free(deg); return 0; }
    /* repeated edges */
    for (int x = 0; x < nv; x++) for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) if (adj[4 * x + i] == adj[4 * x + j]) { free(deg); return 0; }
    free(deg); return 1;
}
int main(int argc, char **argv) {
    p = atoi(argv[1]); k = atoi(argv[2]); h = atoi(argv[3]); r = atoi(argv[4]); D = argc > 5 ? atoi(argv[5]) : 9;
    kp = k / h; nv = p * kp; n = 2 * nv;
    long z = 1; for (int i = 0; i < k; i++) { if (i < kp) R[i] = z; z = z * r % p; }
    if (z != 1) { fprintf(stderr, "r^k != 1\n"); return 2; }
    { long t = 1; for (int i = 1; i < k; i++) { t = t * r % p; if (t == 1) { fprintf(stderr, "r has order %d < k\n", i); return 2; } } }
    long zeta = 1; for (int i = 0; i < kp; i++) zeta = zeta * r % p;
    adj = malloc(sizeof(int) * 4 * n); dist = malloc(sizeof(int) * n); q = malloc(sizeof(int) * n);
    int best = 1 << 30, shown = 0; long cnt = 0;
    int N0[4][2];
    /* types: h=2: {(+-1,0), (+-u,v)}  and {(+-1,0), (0,v2), (0,v3)};  h=3: {(1,0),(z,0),(z^2,0), (0,v)} */
    for (int type = 0; type < 2; type++) {
        if (h == 3 && type == 1) break;
        int umax = (h == 2 && type == 0) ? p : 1;
        for (int u = 1; u < umax || (umax == 1 && u == 1); u++) for (int v2 = 0; v2 < kp; v2++) for (int v3 = 0; v3 < kp; v3++) {
            if (h == 2 && type == 0 && v3 > 0) break;
            if (h == 3 && v3 > 0) break;
            if (h == 2 && type == 1 && v3 <= v2) continue;
            if (h == 2) {
                N0[0][0] = 1; N0[0][1] = 0; N0[1][0] = p - 1; N0[1][1] = 0;
                if (type == 0) { if (u == 1 && v2 == 0) continue; if (u == p - 1 && v2 == 0) continue;
                    N0[2][0] = u; N0[2][1] = v2; N0[3][0] = p - u; N0[3][1] = v2; }
                else { N0[2][0] = 0; N0[2][1] = v2; N0[3][0] = 0; N0[3][1] = v3; }
            } else {
                N0[0][0] = 1; N0[0][1] = 0; N0[1][0] = (int)zeta; N0[1][1] = 0; N0[2][0] = (int)(zeta * zeta % p); N0[2][1] = 0;
                N0[3][0] = 0; N0[3][1] = v2;
            }
            if (!build(N0)) continue;
            cnt++;
            int f = bfs_far(0); if (f > best) continue; f += bfs_far(nv);
            if (f < best) { best = f; shown = 0; }
            if (f == best && shown < 20) { shown++; printf("far %d  N0 = (%d,%d) (%d,%d) (%d,%d) (%d,%d)\n", f, N0[0][0], N0[0][1], N0[1][0], N0[1][1], N0[2][0], N0[2][1], N0[3][0], N0[3][1]); }
        }
    }
    printf("p %d k %d h %d r %d n %d: %ld graphs, best far-vertex count (two roots) %d\n", p, k, h, r, n, cnt, best);
    return 0;
}
