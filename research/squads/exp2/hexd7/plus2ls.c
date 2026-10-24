/* Local search for the bijection phi in plus2.py's graph (3 copies of H(q) + 2 vertices).
   Graph: copies c = 0,1,2 of the incidence graph (points 0..P-1, lines P..2P-1, vertex c*2P + v); cross edges
   (y, c) ~ (phi(y), c+1) for every point y != p; gadget x ~ (p, c) for all c, w ~ (L0, c) for all c, x ~ w.
   Only pairs involving a = (p, 0) or b = (L0, 1) can be at distance > 7 (Z3 symmetry; every other pair keeps the
   routes of the 3-copy proof), so the score is the number of vertices beyond distance 7 from a plus from b.
   Moves: swap the images of two points; targeted (route a -> y -> phi(y) -> t for an unreached point t, or
   b -> M -> phi^-1(M) -> t for an unreached line t), random otherwise. Accept if the score does not increase.
   Input: HFILE (line 1: P q; then P lines of q+1 point indices), PHI (P line indices), p, L0.
   Usage: plus2ls HFILE PHI p L0 seconds seed OUTPHI */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static int P, q, K, *PL, *LP, *phi, *inv, p0, L0, NV, *dist, *queue;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
/* neighbours of vertex v; returns count */
static int nbrs(int v, int *out) {
    int n = 0, X = 6 * P, Wv = 6 * P + 1;
    if (v == X) { for (int c = 0; c < 3; c++) out[n++] = c * 2 * P + p0; out[n++] = Wv; return n; }
    if (v == Wv) { for (int c = 0; c < 3; c++) out[n++] = c * 2 * P + P + L0; out[n++] = X; return n; }
    int c = v / (2 * P), u = v % (2 * P), base = c * 2 * P;
    if (u < P) {   /* point */
        for (int i = 0; i < K; i++) out[n++] = base + P + LP[u * K + i];
        if (u == p0) out[n++] = X;
        else out[n++] = ((c + 1) % 3) * 2 * P + P + phi[u];
    } else {
        int l = u - P;
        for (int i = 0; i < K; i++) out[n++] = base + PL[l * K + i];
        if (l == L0) out[n++] = Wv;
        else out[n++] = ((c + 2) % 3) * 2 * P + inv[l];
    }
    return n;
}
/* BFS to depth 7 from s; returns number of unreached vertices; dist[] filled (-1 = unreached) */
static int bfs(int s) {
    for (int i = 0; i < NV; i++) dist[i] = -1;
    int h = 0, t = 0, nb[64]; dist[s] = 0; queue[t++] = s;
    while (h < t) { int v = queue[h++]; if (dist[v] == 7) continue; int k = nbrs(v, nb);
        for (int i = 0; i < k; i++) if (dist[nb[i]] < 0) { dist[nb[i]] = dist[v] + 1; queue[t++] = nb[i]; } }
    return NV - t;
}
static int score(int *ua, int *nua, int *ub, int *nub) {
    int A = 6 * P * 0 + p0, B = 1 * 2 * P + P + L0, s = 0;
    s += bfs(A); if (ua) { *nua = 0; for (int i = 0; i < NV; i++) if (dist[i] < 0) ua[(*nua)++] = i; }
    s += bfs(B); if (ub) { *nub = 0; for (int i = 0; i < NV; i++) if (dist[i] < 0) ub[(*nub)++] = i; }
    return s;
}
static void swap_img(int y1, int y2) { int m1 = phi[y1], m2 = phi[y2]; phi[y1] = m2; phi[y2] = m1; inv[m2] = y1; inv[m1] = y2; }
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: plus2ls HFILE PHI p L0 seconds seed OUTPHI\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d", &P, &q) != 2) return 2; K = q + 1;
    PL = malloc(sizeof(int) * P * K); LP = malloc(sizeof(int) * P * K); int *cnt = calloc(P, sizeof(int));
    for (int l = 0; l < P; l++) for (int i = 0; i < K; i++) { int y; if (fscanf(f, "%d", &y) != 1) return 2; PL[l * K + i] = y; LP[y * K + cnt[y]++] = l; }
    fclose(f);
    phi = malloc(sizeof(int) * P); inv = malloc(sizeof(int) * P);
    f = fopen(argv[2], "r"); for (int y = 0; y < P; y++) if (fscanf(f, "%d", &phi[y]) != 1) return 2; fclose(f);
    for (int y = 0; y < P; y++) inv[phi[y]] = y;
    p0 = atoi(argv[3]); L0 = atoi(argv[4]); double secs = atof(argv[5]); rs ^= (unsigned long long)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL;
    if (phi[p0] != L0) { fprintf(stderr, "phi(p) != L0\n"); return 2; }
    NV = 6 * P + 2; dist = malloc(sizeof(int) * NV); queue = malloc(sizeof(int) * NV);
    /* distances from p and L0 inside one copy (for targeted moves) */
    int *dP = malloc(sizeof(int) * 2 * P), *dL = malloc(sizeof(int) * 2 * P);
    { int saveL0 = L0; (void)saveL0; }
    for (int pass = 0; pass < 2; pass++) {
        int *d = pass ? dL : dP, s = pass ? P + L0 : p0, h = 0, t = 0;
        for (int i = 0; i < 2 * P; i++) d[i] = -1; d[s] = 0; queue[t++] = s;
        while (h < t) { int v = queue[h++]; if (v < P) { for (int i = 0; i < K; i++) { int w = P + LP[v * K + i]; if (d[w] < 0) { d[w] = d[v] + 1; queue[t++] = w; } } }
            else { for (int i = 0; i < K; i++) { int w = PL[(v - P) * K + i]; if (d[w] < 0) { d[w] = d[v] + 1; queue[t++] = w; } } } }
    }
    int *Y4 = malloc(sizeof(int) * P), nY4 = 0, *M4 = malloc(sizeof(int) * P), nM4 = 0, *Y2 = malloc(sizeof(int) * P), nY2 = 0, *M2 = malloc(sizeof(int) * P), nM2 = 0;
    for (int y = 0; y < P; y++) { if (dP[y] == 4) Y4[nY4++] = y; if (dP[y] == 2) Y2[nY2++] = y; }
    for (int m = 0; m < P; m++) { if (dL[P + m] == 4) M4[nM4++] = m; if (dL[P + m] == 2) M2[nM2++] = m; }
    int *ua = malloc(sizeof(int) * NV), *ub = malloc(sizeof(int) * NV), nua, nub;
    int cur = score(ua, &nua, ub, &nub), best = cur; double t0 = now(), lastp = t0; long long it = 0, acc = 0;
    fprintf(stderr, "start score %d (from a: %d, from b: %d)\n", cur, nua, nub);
    while (cur > 0 && now() - t0 < secs) {
        it++;
        int y1, y2;
        int r = rnd() % 100;
        if (r < 45 && nua > 0) {   /* fix an unreached target of a */
            int t = ua[rnd() % nua], c = t / (2 * P), u = t % (2 * P);
            if (u < P) {   /* a point: give some y at distance 4 (or 2) from p the image of a line through u */
                int m = LP[u * K + rnd() % K]; if (m == L0) continue;
                y1 = (rnd() % 4) ? Y4[rnd() % nY4] : Y2[rnd() % nY2]; y2 = inv[m];
            } else {      /* a line: give some y at distance 2 from p a line near it -> use a random line meeting u */
                int l = u - P, z = PL[l * K + rnd() % K], m = LP[z * K + rnd() % K]; if (m == L0) continue;
                y1 = Y2[rnd() % nY2]; y2 = inv[m];
            }
            (void)c;
        } else if (r < 90 && nub > 0) {   /* fix an unreached target of b */
            int t = ub[rnd() % nub], u = t % (2 * P);
            if (u >= P) { int l = u - P, z = PL[l * K + rnd() % K]; if (z == p0) continue;
                int m = (rnd() % 4) ? M4[rnd() % nM4] : M2[rnd() % nM2]; y1 = z; y2 = inv[m]; }
            else { int m0 = LP[u * K + rnd() % K], z = PL[m0 * K + rnd() % K]; if (z == p0) continue;
                int m = M2[rnd() % nM2]; y1 = z; y2 = inv[m]; }
        } else { y1 = rnd() % P; y2 = rnd() % P; }
        if (y1 == y2 || y1 == p0 || y2 == p0) continue;
        swap_img(y1, y2);
        int s = score(NULL, NULL, NULL, NULL);
        if (s <= cur || (rnd() % 1000) < 2) {
            cur = s; acc++; score(ua, &nua, ub, &nub);
            if (cur < best) best = cur;
        } else swap_img(y1, y2);
        if (now() - lastp > 10) { fprintf(stderr, "t=%.0f it=%lld acc=%lld score=%d (a %d, b %d) best=%d\n", now() - t0, it, acc, cur, nua, nub, best); lastp = now(); }
    }
    fprintf(stderr, "final score %d after %lld moves, %.1f s\n", cur, it, now() - t0);
    printf("RESULT score=%d\n", cur);
    f = fopen(argv[7], "w"); for (int y = 0; y < P; y++) fprintf(f, "%d%c", phi[y], y + 1 < P ? ' ' : '\n'); fclose(f);
    return cur == 0 ? 0 : 1;
}
