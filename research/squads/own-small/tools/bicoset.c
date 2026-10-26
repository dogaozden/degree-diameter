/* bicoset: cubic bipartite bi-coset graphs with vertex stabiliser of order 2 (own-small job).
   G a group (binary table: int32 N, then N*N uint16, identity 0, T[x*N+y] = x*y), h an involution, d in G.
   H = <h>. Vertices: right cosets Hx on side A and Hx on side B (n = |G|). Hx(A) ~ Hy(B) iff y x^-1 in H u HdH,
   i.e. A-vertex Hx is adjacent to the B-vertices Hx, Hdx, Hdhx. G acts by right multiplication, transitively on each
   side with stabiliser conjugate to H, so the BFS from A-vertex H and from B-vertex H give the exact diameter.
   Every cubic bipartite graph with a colour-preserving group acting transitively on both sides with stabiliser of
   order 2 (acting faithfully on the neighbourhood) is of this form (B-side stabiliser normalised to H).
   Usage: bicoset GROUP.bin D INV.txt [MAXOUT]     INV.txt: "R h1 .. hR" involution reps (Aut-classes)
   For every h in INV and every d with |HdH| = 4 (d h d^-1 != h), prints the best cost per group:
   cost = #(vertices at distance > D from the A root) + #(... from the B root); disconnected graphs are skipped.
   Prints "HIT h d" lines for cost 0 (at most MAXOUT, default 5) and "BEST cost h d diam" at the end. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int N; static uint16_t *T; static int *INV;
static inline int mul(int x, int y) { return T[(size_t)x * N + y]; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: bicoset GROUP.bin D INV.txt [MAXOUT]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) return 2;
    N = n32; T = malloc((size_t)N * N * 2); if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    int D = atoi(argv[2]), maxout = argc > 4 ? atoi(argv[4]) : 5;
    INV = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int y = 0; y < N; y++) if (mul(g, y) == 0) { INV[g] = y; break; } }
    FILE *fi = fopen(argv[3], "r"); int R; if (!fi || fscanf(fi, "%d", &R) != 1) return 2;
    int *hs = malloc((R + 1) * sizeof(int)); for (int i = 0; i < R; i++) if (fscanf(fi, "%d", &hs[i]) != 1) return 2;
    fclose(fi);
    int M = N / 2;                       /* cosets per side */
    int *cid = malloc(N * sizeof(int)), *rep = malloc(M * sizeof(int));
    int *adj = malloc((size_t)2 * M * 3 * sizeof(int)), *deg = malloc(2 * M * sizeof(int));
    int *dist = malloc(2 * M * sizeof(int)), *q = malloc(2 * M * sizeof(int));
    long best = -1; int bh = -1, bd = -1, bdiam = -1, hits = 0; long tried = 0;
    for (int ih = 0; ih < R; ih++) {
        int h = hs[ih];
        if (h == 0 || mul(h, h) != 0) continue;
        /* right cosets Hx = {x, h x} */
        for (int x = 0; x < N; x++) cid[x] = -1;
        int c = 0;
        for (int x = 0; x < N; x++) if (cid[x] < 0) { cid[x] = c; cid[mul(h, x)] = c; rep[c++] = x; }
        if (c != M) { fprintf(stderr, "coset count %d != %d\n", c, M); return 2; }
        for (int d = 0; d < N; d++) {
            /* need d h d^-1 != h (so HdH has 4 elements and the two B-neighbours Hdx, Hdhx differ) */
            if (mul(mul(d, h), INV[d]) == h) continue;
            tried++;
            memset(deg, 0, 2 * M * sizeof(int));
            int ok = 1;
            for (int a = 0; a < M && ok; a++) {
                int x = rep[a];
                int nb[3] = { cid[x], cid[mul(d, x)], cid[mul(mul(d, h), x)] };
                for (int j = 0; j < 3; j++) {
                    int b = M + nb[j];
                    for (int t = 0; t < deg[a]; t++) if (adj[a * 3 + t] == b) ok = 0;   /* multi-edge */
                    if (!ok) break;
                    if (deg[b] >= 3) { ok = 0; break; }
                    adj[a * 3 + deg[a]++] = b; adj[b * 3 + deg[b]++] = a;
                }
            }
            if (!ok) continue;
            long cost = 0; int diam = 0;
            for (int root = 0; root < 2 && cost >= 0; root++) {
                int s = root ? M + cid[0] : cid[0];
                for (int v = 0; v < 2 * M; v++) dist[v] = -1;
                int qh = 0, qt = 0; dist[s] = 0; q[qt++] = s;
                while (qh < qt) { int v = q[qh++]; for (int t = 0; t < 3; t++) { int w = adj[v * 3 + t]; if (dist[w] < 0) { dist[w] = dist[v] + 1; q[qt++] = w; } } }
                if (qt < 2 * M) { cost = -1; break; }
                for (int v = 0; v < 2 * M; v++) { if (dist[v] > D) cost++; if (dist[v] > diam) diam = dist[v]; }
            }
            if (cost < 0) continue;
            if (best < 0 || cost < best) { best = cost; bh = h; bd = d; bdiam = diam; }
            if (cost == 0 && hits < maxout) { printf("HIT h %d d %d diam %d\n", h, d, diam); hits++; }
        }
    }
    printf("BEST %ld h %d d %d diam %d tried %ld\n", best, bh, bd, bdiam, tried);
    return 0;
}
