/* Tabu search over single voltage moves for the FAKE-chart cost (same walks and cost as mlift_chart.c with all walks admissible).
   usage: tabu BASE TABLE SECS SEED   (tree edges fixed to identity; prints best fake cost and voltages) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef struct { int len, E[4], end; } W;
int k, ne, EA[64], EB[64], n, *T, *Inv, e_id, istree[64], volt[64];
W *wA[32], *wB[32]; int nwA[32], nwB[32]; unsigned char *hit;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int mul(int a, int b) { return T[a * n + b]; }
int cost(void) {
    int c = 0;
    for (int i = 0; i < k; i++) { memset(hit, 0, k * n);
        for (int w = 0; w < nwA[i]; w++) { W *x = &wA[i][w]; int g;
            if (x->len == 2) { g = mul(Inv[volt[x->E[1]]], volt[x->E[0]]); if (x->end == i && g == e_id) continue; }
            else g = mul(Inv[volt[x->E[3]]], mul(volt[x->E[2]], mul(Inv[volt[x->E[1]]], volt[x->E[0]])));
            hit[x->end * n + g] = 1; }
        for (int t = 0; t < k * n; t++) c += !hit[t]; }
    for (int j = 0; j < k; j++) { memset(hit, 0, k * n);
        for (int w = 0; w < nwB[j]; w++) { W *x = &wB[j][w]; int g;
            if (x->len == 2) { g = mul(volt[x->E[1]], Inv[volt[x->E[0]]]); if (x->end == j && g == e_id) continue; }
            else g = mul(volt[x->E[3]], mul(Inv[volt[x->E[2]]], mul(volt[x->E[1]], Inv[volt[x->E[0]]])));
            hit[x->end * n + g] = 1; }
        for (int t = 0; t < k * n; t++) c += !hit[t]; }
    return c;
}
int parallel_ok(void) { for (int a = 0; a < ne; a++) for (int b = a + 1; b < ne; b++) if (EA[a] == EA[b] && EB[a] == EB[b] && volt[a] == volt[b]) return 0; return 1; }
int main(int argc, char **argv) {
    if (argc < 5) return 1;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &k) != 1) return 2;
    ne = 4 * k; int dA[32] = {0}, dB[32] = {0};
    for (int i = 0; i < ne; i++) { if (fscanf(f, "%d %d", &EA[i], &EB[i]) != 2) return 3; }
    fclose(f);
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &n) != 1) return 4;
    T = malloc(sizeof(int) * n * n); Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) return 5; fclose(f);
    for (int i = 0; i < n; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e_id = i; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == e_id) Inv[i] = j;
    double secs = atof(argv[3]); rs ^= (unsigned long long)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    hit = malloc(k * n + 1);
    /* spanning tree (BFS from A0) */
    int seen[64] = {0}, q[64], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int x = q[h++];
        for (int i = 0; i < ne; i++) { int a = EA[i], b = k + EB[i], y = -1;
            if (x == a && !seen[b]) y = b; else if (x == b && !seen[a]) y = a;
            if (y >= 0) { seen[y] = 1; q[t++] = y; istree[i] = 1; } } }
    if (t != 2 * k) { printf("base disconnected\n"); return 7; }
    /* walks: A-side from orbit i, B-side from orbit j (same definitions as mlift_ejoint.c) */
    for (int i = 0; i < k; i++) { wA[i] = malloc(sizeof(W) * 200); nwA[i] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EA[e1] == i)
        for (int e2 = 0; e2 < ne; e2++) if (EB[e2] == EB[e1] && e2 != e1) {
            W *w = &wA[i][nwA[i]++]; w->len = 2; w->E[0] = e1; w->E[1] = e2; w->end = EA[e2];
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EA[e3] == EA[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EB[e4] == EB[e3]) {
                W *v = &wA[i][nwA[i]++]; v->len = 4; v->E[0] = e1; v->E[1] = e2; v->E[2] = e3; v->E[3] = e4; v->end = EA[e4]; } } }
    for (int j = 0; j < k; j++) { wB[j] = malloc(sizeof(W) * 200); nwB[j] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EB[e1] == j)
        for (int e2 = 0; e2 < ne; e2++) if (EA[e2] == EA[e1] && e2 != e1) {
            W *w = &wB[j][nwB[j]++]; w->len = 2; w->E[0] = e1; w->E[1] = e2; w->end = EB[e2];
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EB[e3] == EB[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EA[e4] == EA[e3]) {
                W *v = &wB[j][nwB[j]++]; v->len = 4; v->E[0] = e1; v->E[1] = e2; v->E[2] = e3; v->E[3] = e4; v->end = EB[e4]; } } }
    int freeE[64], nf = 0; for (int e = 0; e < ne; e++) if (!istree[e]) freeE[nf++] = e;
    do { for (int e = 0; e < ne; e++) volt[e] = istree[e] ? e_id : (int)(xr() % n); } while (!parallel_ok());
    int cur = cost(), gbest = cur, gv[64]; memcpy(gv, volt, sizeof volt);
    static long tabu[64][128]; long it = 0, since = 0; clock_t t0 = clock();
    while (gbest > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++; int bc = 1 << 30, bf = -1, bg = -1, ties = 0;
        for (int fi = 0; fi < nf; fi++) { int e = freeE[fi], old = volt[e];
            for (int g = 0; g < n; g++) { if (g == old) continue; volt[e] = g; if (!parallel_ok()) continue;
                int c2 = cost(); int isT = tabu[e][g] > it;
                if (isT && c2 >= gbest) continue;
                if (c2 < bc) { bc = c2; bf = e; bg = g; ties = 1; }
                else if (c2 == bc) { ties++; if (xr() % ties == 0) { bf = e; bg = g; } } }
            volt[e] = old; }
        if (bf < 0) continue;
        int oldv = volt[bf]; tabu[bf][oldv] = it + 4 + (long)(xr() % 6);
        volt[bf] = bg; cur = bc; since++;
        if (cur < gbest) { gbest = cur; memcpy(gv, volt, sizeof volt); since = 0; }
        if (since > 400) { /* perturb from best */
            memcpy(volt, gv, sizeof volt); for (int r = 0; r < 3; r++) { int e = freeE[xr() % nf]; volt[e] = (int)(xr() % n); }
            if (!parallel_ok()) memcpy(volt, gv, sizeof volt);
            cur = cost(); since = 0; }
    }
    printf("k=%d n=%d m=%d best_fake_cost=%d iters=%ld volt=", k, n, k * n, gbest, it);
    for (int e = 0; e < ne; e++) printf("%d%c", gv[e], e + 1 < ne ? ',' : '\n');
    return 0;
}
