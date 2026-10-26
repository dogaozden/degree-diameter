/* tabu: tabu search over cubic bipartite m+m graphs (A = 0..m-1, B = m..2m-1) for the (9,5) route-chart controller.
   Cost as in tools/ctrl: far same-side unordered pairs (walk length > 4) / 2 + W4 * (vertices on no 4-cycle).
   Move: double-edge switch (a1b1,a2b2 -> a1b2,a2b1), best non-tabu move of SAMPLE random candidates per step;
   removed edges are tabu for TEN steps; aspiration if the move beats the best cost. After STALL steps without a new
   best, restart from the best state with PERT random switches.
   Usage: tabu m seconds seed OUT [INIT]   (INIT: edge file "2m" then "u v" lines, same as OUT)
   Writes OUT.best always (lowest cost), OUT itself only at cost 0.  Env W4 NO4 TEN SAMPLE STALL PERT. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>
static int m, n, adj[128][3], W4 = 2, NO4 = 1, TEN = 12, SAMPLE = 300, STALL = 3000, PERT = 6;
static long tabu_until[128][128];
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
typedef struct { uint64_t w[2]; } bs;
static bs nb[128];
static inline void bor(bs *a, const bs *b) { a->w[0] |= b->w[0]; a->w[1] |= b->w[1]; }
static int cost(void) {
    for (int x = 0; x < n; x++) { nb[x].w[0] = nb[x].w[1] = 0; for (int k = 0; k < 3; k++) { int y = adj[x][k]; nb[x].w[y >> 6] |= 1ULL << (y & 63); } }
    int far = 0;
    for (int s = 0; s < n; s++) {
        bs b2 = {{0, 0}}, b3 = {{0, 0}}, b4 = {{0, 0}};
        for (int k = 0; k < 3; k++) bor(&b2, &nb[adj[s][k]]);
        for (int y = 0; y < n; y++) if ((b2.w[y >> 6] >> (y & 63)) & 1) bor(&b3, &nb[y]);
        for (int y = 0; y < n; y++) if ((b3.w[y >> 6] >> (y & 63)) & 1) bor(&b4, &nb[y]);
        int lo = s < m ? 0 : m;
        for (int t = lo; t < lo + m; t++) if (!((b4.w[t >> 6] >> (t & 63)) & 1) && t != s) far++;
    }
    int no4 = 0;
    if (NO4) for (int x = 0; x < n; x++) {
        int ok = 0;
        for (int i = 0; i < 3 && !ok; i++) for (int j = i + 1; j < 3 && !ok; j++) {
            bs c = nb[adj[x][i]]; c.w[0] &= nb[adj[x][j]].w[0]; c.w[1] &= nb[adj[x][j]].w[1];
            if (__builtin_popcountll(c.w[0]) + __builtin_popcountll(c.w[1]) >= 2) ok = 1;
        }
        if (!ok) no4++;
    }
    return far / 2 + W4 * no4;
}
static int has(int x, int y) { for (int k = 0; k < 3; k++) if (adj[x][k] == y) return 1; return 0; }
static void setnb(int x, int old, int nw) { for (int k = 0; k < 3; k++) if (adj[x][k] == old) { adj[x][k] = nw; return; } }
static void swp(int a1, int k1, int a2, int k2) {
    int b1 = adj[a1][k1], b2 = adj[a2][k2];
    adj[a1][k1] = b2; adj[a2][k2] = b1; setnb(b1, a1, a2); setnb(b2, a2, a1);
}
static void save(const char *fn, int *ok) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", n); for (int u = 0; u < m; u++) for (int k = 0; k < 3; k++) fprintf(f, "%d %d\n", u, adj[u][k]);
    fclose(f); if (ok) *ok = 1;
}
static void random_start(void) {
    for (;;) {
        int perm[3][128]; int ok = 1;
        for (int c = 0; c < 3; c++) { for (int i = 0; i < m; i++) perm[c][i] = i; for (int i = m - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[c][i]; perm[c][i] = perm[c][j]; perm[c][j] = t; } }
        for (int u = 0; u < m; u++) if (perm[0][u] == perm[1][u] || perm[0][u] == perm[2][u] || perm[1][u] == perm[2][u]) ok = 0;
        if (!ok) continue;
        for (int u = 0; u < m; u++) for (int c = 0; c < 3; c++) adj[u][c] = m + perm[c][u];
        for (int v = 0; v < m; v++) for (int c = 0; c < 3; c++) adj[m + v][c] = 0;
        for (int u = 0; u < m; u++) for (int c = 0; c < 3; c++) { int v = adj[u][c]; int k = 0; while (adj[v][k] != 0 && k < 3) k++; (void)k; }
        /* rebuild B side properly */
        for (int v = 0; v < m; v++) { int cnt = 0; for (int u = 0; u < m; u++) for (int c = 0; c < 3; c++) if (adj[u][c] == m + v) adj[m + v][cnt++] = u; }
        break;
    }
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: tabu m seconds seed OUT [INIT]\n"); return 2; }
    m = atoi(argv[1]); n = 2 * m; double secs = atof(argv[2]);
    rs ^= strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 30; i++) rnd();
    const char *out = argv[4];
    if (getenv("W4")) W4 = atoi(getenv("W4")); if (getenv("NO4")) NO4 = atoi(getenv("NO4"));
    if (getenv("TEN")) TEN = atoi(getenv("TEN")); if (getenv("SAMPLE")) SAMPLE = atoi(getenv("SAMPLE"));
    if (getenv("STALL")) STALL = atoi(getenv("STALL")); if (getenv("PERT")) PERT = atoi(getenv("PERT"));
    if (argc > 5) {
        FILE *f = fopen(argv[5], "r"); int nn; if (!f || fscanf(f, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "bad INIT\n"); return 2; }
        int deg[128] = {0};
        for (int i = 0; i < 3 * m; i++) { int u, v; if (fscanf(f, "%d %d", &u, &v) != 2) return 2; if (u >= m) { int t = u; u = v; v = t; } adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
        fclose(f);
        for (int x = 0; x < n; x++) if (deg[x] != 3) { fprintf(stderr, "INIT not cubic\n"); return 2; }
    } else random_start();
    int cur = cost(), best = cur; static int badj[128][3]; memcpy(badj, adj, sizeof adj);
    double t0 = now(); long step = 0, last_imp = 0;
    while (best > 0 && now() - t0 < secs) {
        step++;
        int bc = INT_MAX, bu1 = -1, bk1 = 0, bu2 = 0, bk2 = 0, ties = 0;
        for (int t = 0; t < SAMPLE; t++) {
            int a1 = rnd() % m, a2 = rnd() % m; if (a1 == a2) continue;
            int k1 = rnd() % 3, k2 = rnd() % 3;
            int b1 = adj[a1][k1], b2 = adj[a2][k2];
            if (b1 == b2 || has(a1, b2) || has(a2, b1)) continue;
            int tabu = tabu_until[a1][b2] > step || tabu_until[a2][b1] > step;
            swp(a1, k1, a2, k2);
            int c = cost();
            swp(a1, k1, a2, k2); /* undo: adj[a1][k1] is b2 now, swapping back restores b1,b2 */
            if (tabu && c >= best) continue;
            if (c < bc) { bc = c; bu1 = a1; bk1 = k1; bu2 = a2; bk2 = k2; ties = 1; }
            else if (c == bc && rnd() % (++ties) == 0) { bu1 = a1; bk1 = k1; bu2 = a2; bk2 = k2; }
        }
        if (bu1 < 0) continue;
        int b1 = adj[bu1][bk1], b2 = adj[bu2][bk2];
        swp(bu1, bk1, bu2, bk2);
        tabu_until[bu1][b1] = step + TEN; tabu_until[bu2][b2] = step + TEN;
        cur = bc;
        if (cur < best) { best = cur; memcpy(badj, adj, sizeof adj); last_imp = step; fprintf(stderr, "t=%.1f step=%ld best=%d\n", now() - t0, step, best); }
        if (step - last_imp > STALL) {
            memcpy(adj, badj, sizeof adj); memset(tabu_until, 0, sizeof tabu_until);
            for (int p = 0; p < PERT; p++) { int a1 = rnd() % m, a2 = rnd() % m; if (a1 == a2) { p--; continue; } int k1 = rnd() % 3, k2 = rnd() % 3; int x1 = adj[a1][k1], x2 = adj[a2][k2]; if (x1 == x2 || has(a1, x2) || has(a2, x1)) { p--; continue; } swp(a1, k1, a2, k2); }
            cur = cost(); last_imp = step;
        }
    }
    memcpy(adj, badj, sizeof adj);
    printf("RESULT tabu m=%d best=%d steps=%ld time=%.1f NO4=%d W4=%d TEN=%d SAMPLE=%d\n", m, best, step, now() - t0, NO4, W4, TEN, SAMPLE);
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", out); save(fn, 0);
    if (best == 0) save(out, 0);
    return best == 0 ? 0 : 1;
}
