/* 3 copies of H(q) + 2m vertices: m points p_i "unhooked" in all three copies, each with a gadget x_i, w_i.
   Graph: copies c = 0,1,2 of the incidence graph (points 0..P-1, lines P..2P-1, vertex c*2P + v); cross edges
   (y, c) ~ (phi(y), c+1) for every point y not in {p_i}; gadget x_i ~ (p_i, c) for all c, w_i ~ (L_i, c) for all c,
   x_i ~ w_i, with L_i = phi(p_i). Max degree q+2, n = 6P + 2m.
   Gadget points: p_1 and points collinear with it (pairwise distance <= 4); gadget lines: L* and lines meeting it
   (pairwise distance <= 4), so the gadget vertices are within 6 of each other.
   Pairs avoiding every p_i, L_i, x_i, w_i keep the routes of the 3-copy proof; by Z3 symmetry it suffices to check
   the sources a_i = (p_i, 0), b_i = (L_i, 1), x_i, w_i. Score = vertices beyond distance 7 from those sources.
   phi starts random (with phi(p_i) = L_i) and is improved by swapping images (targeted, as in plus2ls.c).
   Usage: plusm HFILE m seconds seed OUT.edges [OUT.phi [R]]  (R: cluster radius, default 2)
   PHIIN=file: start from this phi (with seconds = 0 it just rebuilds and checks the graph of a saved phi).  -> writes the edge list when the score reaches 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static int P, q, K, *PL, *LP, *phi, *inv, NV, *dist, *queue, m, *GP, *GL, *gidP, *gidL;
static int *ADJ = NULL;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int nbrs(int v, int *out) {
    int n = 0;
    if (v >= 6 * P) { int i = (v - 6 * P) / 2, isw = (v - 6 * P) % 2;
        if (!isw) { for (int c = 0; c < 3; c++) out[n++] = c * 2 * P + GP[i]; out[n++] = v + 1; }
        else { for (int c = 0; c < 3; c++) out[n++] = c * 2 * P + P + GL[i]; out[n++] = v - 1; }
        return n; }
    int c = v / (2 * P), u = v % (2 * P), base = c * 2 * P;
    if (u < P) {
        for (int i = 0; i < K; i++) out[n++] = base + P + LP[u * K + i];
        if (gidP[u] >= 0) out[n++] = 6 * P + 2 * gidP[u];
        else out[n++] = ((c + 1) % 3) * 2 * P + P + phi[u];
    } else {
        int l = u - P;
        for (int i = 0; i < K; i++) out[n++] = base + PL[l * K + i];
        if (gidL[l] >= 0) out[n++] = 6 * P + 2 * gidL[l] + 1;
        else out[n++] = ((c + 2) % 3) * 2 * P + inv[l];
    }
    return n;
}
static int bfs(int s) {
    for (int i = 0; i < NV; i++) dist[i] = -1;
    int h = 0, t = 0, nb[64]; dist[s] = 0; queue[t++] = s;
    while (h < t) { int v = queue[h++]; if (dist[v] == 7) continue; int k = nbrs(v, nb);
        for (int i = 0; i < k; i++) if (dist[nb[i]] < 0) { dist[nb[i]] = dist[v] + 1; queue[t++] = nb[i]; } }
    return NV - t;
}
/* sources: 4 per gadget. Bit-parallel BFS (64 sources per pass) over the adjacency table ADJ (degree <= K+1). */
static int NS, *SRC, *SKIND, *SGI;   /* kind 0: a_i, 1: b_i, 2: x_i/w_i */
static int *DEG; static unsigned long long *VIS, *FR, *NX;
static void build_adj(void) {
    int nb[64];
    for (int v = 0; v < NV; v++) { int k = nbrs(v, nb); DEG[v] = k; for (int i = 0; i < k; i++) ADJ[v * (K + 1) + i] = nb[i]; }
}
static void fix_adj(int v) { int nb[64], k = nbrs(v, nb); DEG[v] = k; for (int i = 0; i < k; i++) ADJ[v * (K + 1) + i] = nb[i]; }
static int score(int cap, int *missv, int *misss, int *nmiss) {
    int s = 0; if (nmiss) *nmiss = 0;
    for (int s0 = 0; s0 < NS; s0 += 64) {
        int ns = NS - s0 < 64 ? NS - s0 : 64; unsigned long long full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(VIS, 0, 8 * (size_t)NV); memset(FR, 0, 8 * (size_t)NV);
        for (int k = 0; k < ns; k++) { VIS[SRC[s0 + k]] |= 1ULL << k; FR[SRC[s0 + k]] |= 1ULL << k; }
        for (int lev = 0; lev < 7; lev++) {
            for (int v = 0; v < NV; v++) { unsigned long long a = 0; const int *A = ADJ + v * (K + 1); for (int i = 0; i < DEG[v]; i++) a |= FR[A[i]]; NX[v] = a & ~VIS[v]; }
            for (int v = 0; v < NV; v++) VIS[v] |= NX[v];
            unsigned long long *t = FR; FR = NX; NX = t;
        }
        for (int v = 0; v < NV; v++) { unsigned long long ms = ~VIS[v] & full; if (!ms) continue; s += __builtin_popcountll(ms);
            if (nmiss) while (ms && *nmiss < 200000) { int k = __builtin_ctzll(ms); ms &= ms - 1; missv[*nmiss] = v; misss[*nmiss] = s0 + k; (*nmiss)++; } }
        if (s > cap) return s;
    }
    return s;
}
static void swap_img(int y1, int y2) { int m1 = phi[y1], m2 = phi[y2]; phi[y1] = m2; phi[y2] = m1; inv[m2] = y1; inv[m1] = y2;
    if (ADJ) for (int c = 0; c < 3; c++) { fix_adj(c * 2 * P + y1); fix_adj(c * 2 * P + y2); fix_adj(c * 2 * P + P + m1); fix_adj(c * 2 * P + P + m2); } }
static void bfs_inc(int s, int *d) {   /* distances inside one copy of the incidence graph */
    int h = 0, t = 0; for (int i = 0; i < 2 * P; i++) d[i] = -1; d[s] = 0; queue[t++] = s;
    while (h < t) { int v = queue[h++]; if (v < P) { for (int i = 0; i < K; i++) { int w = P + LP[v * K + i]; if (d[w] < 0) { d[w] = d[v] + 1; queue[t++] = w; } } }
        else { for (int i = 0; i < K; i++) { int w = PL[(v - P) * K + i]; if (d[w] < 0) { d[w] = d[v] + 1; queue[t++] = w; } } } }
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: plusm HFILE m seconds seed OUT.edges [OUT.phi [R]]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; K = q + 1;
    PL = malloc(sizeof(int) * P * K); LP = malloc(sizeof(int) * P * K); int *cnt = calloc(P, sizeof(int));
    for (int l = 0; l < P; l++) for (int i = 0; i < K; i++) { int y; if (fscanf(f, "%d", &y) != 1) return 2; PL[l * K + i] = y; LP[y * K + cnt[y]++] = l; }
    fclose(f);
    m = atoi(argv[2]); double secs = atof(argv[3]); rs ^= (unsigned long long)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    NV = 6 * P + 2 * m; dist = malloc(sizeof(int) * NV); queue = malloc(sizeof(int) * (NV > 2 * P ? NV : 2 * P));
    /* gadget points: p_1 = point 0 and points collinear with it; gadget lines: L* = a line far from p_1, and lines meeting it */
    int *dp = malloc(sizeof(int) * 2 * P), *dl = malloc(sizeof(int) * 2 * P);
    bfs_inc(0, dp);
    int Lstar = -1; for (int l = 0; l < P && Lstar < 0; l++) if (dp[P + l] == 5) Lstar = l;   /* a line at distance 5 from p_1 */
    bfs_inc(P + Lstar, dl);
    int *candP = malloc(sizeof(int) * P), nP = 0, *candL = malloc(sizeof(int) * P), nL = 0;
    int R = argc > 7 ? atoi(argv[7]) : 2;   /* cluster radius: gadget points within R of p_1, gadget lines within R of L* */
    int R0 = getenv("RMIN") ? atoi(getenv("RMIN")) : 0;   /* RMIN=2: leave p_1 and L* themselves alone */
    for (int r = R0; r <= R; r++) { for (int y = 0; y < P; y++) if (dp[y] == r) candP[nP++] = y; for (int l = 0; l < P; l++) if (dl[P + l] == r) candL[nL++] = l; }
    if (m > nP || m > nL) { fprintf(stderr, "m too large (max %d)\n", nP < nL ? nP : nL); return 2; }
    GP = malloc(sizeof(int) * m); GL = malloc(sizeof(int) * m); gidP = malloc(sizeof(int) * P); gidL = malloc(sizeof(int) * P);
    for (int i = 0; i < P; i++) gidP[i] = gidL[i] = -1;
    for (int i = 0; i < m; i++) { GP[i] = candP[i]; GL[i] = candL[i]; gidP[GP[i]] = i; gidL[GL[i]] = i; }
    /* phi: random bijection with phi(p_i) = L_i */
    phi = malloc(sizeof(int) * P); inv = malloc(sizeof(int) * P);
    { int *restL = malloc(sizeof(int) * P), nr = 0; for (int l = 0; l < P; l++) if (gidL[l] < 0) restL[nr++] = l;
      for (int i = nr - 1; i > 0; i--) { int j = rnd() % (i + 1), t = restL[i]; restL[i] = restL[j]; restL[j] = t; }
      int k = 0; for (int y = 0; y < P; y++) phi[y] = gidP[y] >= 0 ? GL[gidP[y]] : restL[k++]; }
    if (getenv("PHIIN")) {   /* warm start or rebuild: read phi (must map p_i to L_i) */
        FILE *g = fopen(getenv("PHIIN"), "r"); for (int y = 0; y < P; y++) if (fscanf(g, "%d", &phi[y]) != 1) return 2; fclose(g);
        for (int i = 0; i < m; i++) if (phi[GP[i]] != GL[i]) { fprintf(stderr, "PHIIN: phi(p_%d) != L_%d\n", i, i); return 2; } }
    for (int y = 0; y < P; y++) inv[phi[y]] = y;
    /* per-gadget distance lists for targeted moves */
    int **Y4 = malloc(sizeof(int *) * m), *nY4 = calloc(m, sizeof(int)), **Y2 = malloc(sizeof(int *) * m), *nY2 = calloc(m, sizeof(int));
    int **M4 = malloc(sizeof(int *) * m), *nM4 = calloc(m, sizeof(int)), **M2 = malloc(sizeof(int *) * m), *nM2 = calloc(m, sizeof(int));
    for (int i = 0; i < m; i++) {
        bfs_inc(GP[i], dp); bfs_inc(P + GL[i], dl);
        Y4[i] = malloc(sizeof(int) * P); Y2[i] = malloc(sizeof(int) * P); M4[i] = malloc(sizeof(int) * P); M2[i] = malloc(sizeof(int) * P);
        for (int y = 0; y < P; y++) { if (gidP[y] >= 0) continue; if (dp[y] == 4) Y4[i][nY4[i]++] = y; if (dp[y] == 2) Y2[i][nY2[i]++] = y; }
        for (int l = 0; l < P; l++) { if (gidL[l] >= 0) continue; if (dl[P + l] == 4) M4[i][nM4[i]++] = l; if (dl[P + l] == 2) M2[i][nM2[i]++] = l; }
    }
    NS = 4 * m; SRC = malloc(sizeof(int) * NS); SKIND = malloc(sizeof(int) * NS); SGI = malloc(sizeof(int) * NS);
    for (int i = 0; i < m; i++) {
        SRC[4 * i] = GP[i]; SKIND[4 * i] = 0; SGI[4 * i] = i;                      /* a_i = (p_i, 0) */
        SRC[4 * i + 1] = 2 * P + P + GL[i]; SKIND[4 * i + 1] = 1; SGI[4 * i + 1] = i; /* b_i = (L_i, 1) */
        SRC[4 * i + 2] = 6 * P + 2 * i; SKIND[4 * i + 2] = 2; SGI[4 * i + 2] = i;
        SRC[4 * i + 3] = 6 * P + 2 * i + 1; SKIND[4 * i + 3] = 2; SGI[4 * i + 3] = i;
    }
    ADJ = malloc(sizeof(int) * (size_t)NV * (K + 1)); DEG = malloc(sizeof(int) * NV);
    VIS = malloc(8 * (size_t)NV); FR = malloc(8 * (size_t)NV); NX = malloc(8 * (size_t)NV); build_adj();
    int *missv = malloc(sizeof(int) * 200000), *misss = malloc(sizeof(int) * 200000), nmiss;
    int cur = score(1 << 30, missv, misss, &nmiss), best = cur;
    double t0 = now(), lastp = t0; long long it = 0, acc = 0;
    fprintf(stderr, "q=%d m=%d n=%d start score %d\n", q, m, NV, cur);
    while (cur > 0 && now() - t0 < secs) {
        it++;
        int y1 = -1, y2 = -1;
        if (nmiss && rnd() % 10 < 9) {
            int j = rnd() % nmiss, t = missv[j], k = misss[j], i = SGI[k], u = t % (2 * P);
            if (t >= 6 * P) { y1 = rnd() % P; y2 = rnd() % P; }
            else if (SKIND[k] == 0 || SKIND[k] == 2) {   /* route from (p_i, .) */
                if (u < P) { int mm = LP[u * K + rnd() % K]; if (gidL[mm] >= 0) continue;
                    if (!nY4[i] && !nY2[i]) continue; y1 = ((rnd() % 4 && nY4[i]) || !nY2[i]) ? Y4[i][rnd() % nY4[i]] : Y2[i][rnd() % nY2[i]]; y2 = inv[mm]; }
                else { int z = PL[(u - P) * K + rnd() % K], mm = LP[z * K + rnd() % K]; if (gidL[mm] >= 0) continue;
                    if (!nY2[i]) continue; y1 = Y2[i][rnd() % nY2[i]]; y2 = inv[mm]; }
            } else {                                     /* route from (L_i, .) */
                if (u >= P) { int z = PL[(u - P) * K + rnd() % K]; if (gidP[z] >= 0) continue;
                    if (!nM4[i] && !nM2[i]) continue; int mm = ((rnd() % 4 && nM4[i]) || !nM2[i]) ? M4[i][rnd() % nM4[i]] : M2[i][rnd() % nM2[i]]; y1 = z; y2 = inv[mm]; }
                else { int m0 = LP[u * K + rnd() % K], z = PL[m0 * K + rnd() % K]; if (gidP[z] >= 0) continue;
                    if (!nM2[i]) continue; int mm = M2[i][rnd() % nM2[i]]; y1 = z; y2 = inv[mm]; }
            }
        } else { y1 = rnd() % P; y2 = rnd() % P; }
        if (y1 < 0 || y2 < 0 || y1 == y2 || gidP[y1] >= 0 || gidP[y2] >= 0) continue;
        swap_img(y1, y2);
        int s = score(cur, NULL, NULL, NULL);
        if (s <= cur) { cur = s; acc++; score(1 << 30, missv, misss, &nmiss); if (cur < best) best = cur; }
        else swap_img(y1, y2);
        if (now() - lastp > 15) { fprintf(stderr, "t=%.0f it=%lld acc=%lld score=%d best=%d\n", now() - t0, it, acc, cur, best); lastp = now(); }
    }
    fprintf(stderr, "final score %d after %lld moves, %.1f s\n", cur, it, now() - t0);
    printf("RESULT q=%d m=%d n=%d score=%d\n", q, m, NV, cur);
    if (argc > 6) { f = fopen(argv[6], "w"); for (int y = 0; y < P; y++) fprintf(f, "%d%c", phi[y], y + 1 < P ? ' ' : '\n'); fclose(f); }
    if (cur == 0) {   /* write the edge list (apsp.c format) */
        f = fopen(argv[5], "w"); long long ne = 0; fprintf(f, "%d\n", NV); int nb[64];
        for (int v = 0; v < NV; v++) { int k = nbrs(v, nb); for (int i = 0; i < k; i++) if (nb[i] > v) { fprintf(f, "%d %d\n", v, nb[i]); ne++; } }
        fclose(f); fprintf(stderr, "wrote %s: n=%d edges=%lld\n", argv[5], NV, ne);
    }
    return cur == 0 ? 0 : 1;
}
