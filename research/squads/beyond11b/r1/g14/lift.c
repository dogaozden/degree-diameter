/* g14: voltage lifts of cubic bipartite BASE multigraphs on B+B vertices over a metacyclic group
 * G = Z_M x|_R Z_K (order n = M*K).  Lift: vertices (v,g), v in [0,2B), g in G; black u (v<B) and white w (v=B+w)
 * base edge e=(u,w) with voltage x_e gives lift edges (u,g)~(B+w, g*x_e).  G acts by left multiplication, so each
 * base vertex orbit is one fiber: diameter = max over the 2B sources (s,e) of eccentricity (exact).
 * Non-Haar when B >= 2 (several fiber orbits).  Spanning-tree voltages are gauged to the identity; the b+1 non-tree
 * voltages are searched by hill climbing; base graphs are random configuration-model 3-regular bipartite multigraphs.
 * Cost = number of (source, vertex) pairs at distance > D, plus a penalty for parallel lifted edges.
 * usage: lift M K R B D secs seed OUT   (writes OUT = "N" then "u v" lines on cost 0; prints FOUND line)        */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int M, K, R, n, B, D, NV, N;
static int *MUL, *INV;
static int eu[64], ew[64], ex[64], istree[64], ne;
static int *adj, *dist, *q;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rnd(int k) { return (int)(xr() % (unsigned long long)k); }

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int gen_base(void) { /* returns 1 if the base multigraph is connected; sets tree flags */
    int bl[64], wh[64], i, j, t;
    for (i = 0; i < 3 * B; i++) { bl[i] = i / 3; wh[i] = i / 3; }
    for (i = 3 * B - 1; i > 0; i--) { j = rnd(i + 1); t = wh[i]; wh[i] = wh[j]; wh[j] = t; }
    ne = 3 * B;
    for (i = 0; i < ne; i++) { eu[i] = bl[i]; ew[i] = wh[i]; istree[i] = 0; }
    /* BFS over 2B base vertices: black u -> id u, white w -> id B+w */
    int seen[128], qq[128], h = 0, tl = 0, cnt = 1;
    memset(seen, 0, sizeof(seen));
    seen[0] = 1; qq[tl++] = 0;
    while (h < tl) {
        int v = qq[h++];
        for (i = 0; i < ne; i++) {
            int a = eu[i], b = B + ew[i], o = -1;
            if (a == v) o = b; else if (b == v) o = a; else continue;
            if (!seen[o]) { seen[o] = 1; qq[tl++] = o; istree[i] = 1; cnt++; }
        }
    }
    return cnt == 2 * B;
}

static int cost(void) {
    int c = 0, s, i, h, tl, v, j;
    /* simplicity: parallel base edges need distinct voltages */
    for (i = 0; i < ne; i++) for (j = i + 1; j < ne; j++)
        if (eu[i] == eu[j] && ew[i] == ew[j] && ex[i] == ex[j]) c += N;
    /* adjacency */
    for (v = 0; v < B; v++) for (int g = 0; g < n; g++) {
        int id = v * n + g, k = 0;
        for (i = 0; i < ne; i++) if (eu[i] == v) adj[id * 3 + k++] = (B + ew[i]) * n + MUL[g * n + ex[i]];
    }
    for (v = 0; v < B; v++) { /* white side, index B+w */ }
    for (int w = 0; w < B; w++) for (int g = 0; g < n; g++) {
        int id = (B + w) * n + g, k = 0;
        for (i = 0; i < ne; i++) if (ew[i] == w) adj[id * 3 + k++] = eu[i] * n + MUL[g * n + INV[ex[i]]];
    }
    for (s = 0; s < NV; s++) {
        int src = s * n; /* identity fiber element index 0 is the identity */
        for (i = 0; i < N; i++) dist[i] = -1;
        h = 0; tl = 0; q[tl++] = src; dist[src] = 0;
        while (h < tl) {
            int x = q[h++];
            for (j = 0; j < 3; j++) { int y = adj[x * 3 + j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[tl++] = y; } }
        }
        for (i = 0; i < N; i++) if (dist[i] < 0 || dist[i] > D) c++;
        if (c > N * 4) return c; /* early out */
    }
    return c;
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: lift M K R B D secs seed OUT\n"); return 1; }
    M = atoi(argv[1]); K = atoi(argv[2]); R = atoi(argv[3]); B = atoi(argv[4]); D = atoi(argv[5]);
    double secs = atof(argv[6]); rs ^= (unsigned long long)atoll(argv[7]) * 2654435761ULL + 1;
    const char *out = argv[8];
    n = M * K; NV = 2 * B; N = NV * n;
    int *RP = malloc(sizeof(int) * (K + 1)); RP[0] = 1 % M;
    for (int b = 1; b <= K; b++) RP[b] = (int)((long long)RP[b - 1] * R % M);
    if ((long long)RP[K] != 1 % M) { fprintf(stderr, "R^K != 1 mod M\n"); return 1; }
    MUL = malloc(sizeof(int) * n * n); INV = malloc(sizeof(int) * n);
    for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) {
        int a = x / K, b = x % K, c = y / K, d = y % K;
        int aa = (int)((a + (long long)RP[b] * c) % M), dd = (b + d) % K;
        MUL[x * n + y] = aa * K + dd;
    }
    for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) if (MUL[x * n + y] == 0) INV[x] = y;
    adj = malloc(sizeof(int) * N * 3); dist = malloc(sizeof(int) * N); q = malloc(sizeof(int) * N);
    double t0 = now(), tend = t0 + secs;
    int best_all = 1 << 30; long evals = 0; int restarts = 0, found = 0;
    while (now() < tend && !found) {
        /* new base graph */
        if (!gen_base()) continue;
        restarts++;
        for (int i = 0; i < ne; i++) ex[i] = istree[i] ? 0 : rnd(n);
        int cur = cost(); evals++;
        int stall = 0, bestc = cur;
        if (cur == 0) { found = 1; break; }
        while (stall < 4000 && now() < tend) {
            int f, tries = 0;
            do { f = rnd(ne); tries++; } while (istree[f] && tries < 1000);
            if (istree[f]) break;
            int old = ex[f];
            ex[f] = rnd(n);
            int c = cost(); evals++;
            if (c <= cur) { if (c < bestc) { bestc = c; stall = 0; } else stall++; cur = c; }
            else { ex[f] = old; stall++; }
            if (cur == 0) { found = 1; break; }
        }
        if (bestc < best_all) best_all = bestc;
    }
    printf("M=%d K=%d R=%d n=%d B=%d N=%d D=%d restarts=%d evals=%ld best_cost=%d time=%.1f\n",
           M, K, R, n, B, N, D, restarts, evals, best_all, now() - t0);
    if (found) {
        FILE *fo = fopen(out, "w");
        fprintf(fo, "%d\n", N);
        for (int v = 0; v < NV; v++) for (int g = 0; g < n; g++) {
            int id = v * n + g;
            for (int j = 0; j < 3; j++) if (v < B) fprintf(fo, "%d %d\n", id, adj[id * 3 + j]);
        }
        fclose(fo);
        printf("FOUND N=%d base:", N);
        for (int i = 0; i < ne; i++) printf(" (%d,%d,%d)", eu[i], ew[i], ex[i]);
        printf("\n");
    }
    return 0;
}
