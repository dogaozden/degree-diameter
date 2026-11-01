/* kopt.c: exact k-opt neighbourhood of a voltage-lift solution (vl format): every way of changing K of the
 * non-tree voltages to any group elements, checked for diameter <= D with an early-abort test (stop at the first
 * uncovered sheet). Prints every candidate with cost 0 as a vl solution.
 * usage: kopt SOL GROUP K [D=5]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXB 64
#define MAXE 512
static int b, E, m, D = 5, W, K;
static int side[MAXB], eu[MAXE], ew[MAXE], volt[MAXE], fixed_[MAXE];
static int deg[MAXB], dn[MAXB][32], de[MAXB][32], dd[MAXB][32];
static uint16_t *mul; static int *inv_;
static uint64_t *cov;
static int order[MAXB * MAXB][2], norder;

static inline int dvolt(int v, int i) { int g = volt[de[v][i]]; return dd[v][i] ? inv_[g] : g; }
static int maxlen;
static void dfs(int v, int laste, int h, int len) {
    cov[(size_t)v * W + (h >> 6)] |= 1ULL << (h & 63);
    if (len == maxlen) return;
    for (int i = 0; i < deg[v]; i++) { int e = de[v][i]; if (e == laste) continue;
        dfs(dn[v][i], e, mul[(size_t)h * m + dvolt(v, i)], len + 1); }
}
static int last_fail_s = 0;
/* 1 if diameter <= D */
static int ok_all(void) {
    for (int k = 0; k < b; k++) {
        int s = (k + last_fail_s) % b;
        memset(cov, 0, sizeof(uint64_t) * b * W);
        maxlen = side[s] == 0 ? D : D - 1;
        dfs(s, -1, 0, 0);
        for (int v = 0; v < b; v++) {
            if (side[s] == 1 && side[v] == 0) continue;
            int cnt = 0; for (int w = 0; w < W; w++) cnt += __builtin_popcountll(cov[(size_t)v * W + w]);
            if (cnt < m) { last_fail_s = s; return 0; }
        }
    }
    return 1;
}
static int freee[MAXE], nfree, pick[8];
static long long tested = 0, found = 0;
static void emit(void) {
    found++;
    printf("SOL %d %d\n", b, E);
    for (int v = 0; v < b; v++) printf("%d%c", side[v], v == b - 1 ? '\n' : ' ');
    for (int e = 0; e < E; e++) printf("%d %d %d\n", eu[e], ew[e], volt[e]);
    fflush(stdout);
}
static int par_ok(int e) { for (int f = 0; f < E; f++) if (f != e && eu[f] == eu[e] && ew[f] == ew[e] && volt[f] == volt[e]) return 0; return 1; }
static void rec_vals(int t) {
    if (t == K) { tested++; if (ok_all()) emit(); return; }
    int e = pick[t], old = volt[e];
    for (int g = 0; g < m; g++) { if (g == old) continue; volt[e] = g; if (!par_ok(e)) continue; rec_vals(t + 1); }
    volt[e] = old;
}
static void rec_sets(int start, int t) {
    if (t == K) { rec_vals(0); return; }
    for (int i = start; i < nfree; i++) { pick[t] = freee[i]; rec_sets(i + 1, t + 1); }
}

int main(int argc, char **argv) {
    if (argc < 4) return 2;
    K = atoi(argv[3]); if (argc > 4) D = atoi(argv[4]);
    FILE *f = fopen(argv[1], "r"); char line[512];
    if (!f || !fgets(line, sizeof line, f) || sscanf(line, "%d %d", &b, &E) != 2) return 2;
    for (int v = 0; v < b; v++) if (fscanf(f, "%d", &side[v]) != 1) return 2;
    for (int e = 0; e < E; e++) { if (fscanf(f, "%d %d %d", &eu[e], &ew[e], &volt[e]) != 3) return 2;
        if (side[eu[e]] == 1) { int t = eu[e]; eu[e] = ew[e]; ew[e] = t; } }
    fclose(f);
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &m) != 1) return 2;
    mul = malloc(sizeof(uint16_t) * m * m); inv_ = malloc(sizeof(int) * m);
    for (long i = 0; i < (long)m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    fclose(f);
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (mul[(size_t)x * m + y] == 0) inv_[x] = y;
    W = (m + 63) / 64; cov = malloc(sizeof(uint64_t) * b * W);
    for (int e = 0; e < E; e++) { int u = eu[e], w = ew[e];
        dn[u][deg[u]] = w; de[u][deg[u]] = e; dd[u][deg[u]] = 0; deg[u]++;
        dn[w][deg[w]] = u; de[w][deg[w]] = e; dd[w][deg[w]] = 1; deg[w]++; }
    /* spanning tree edges stay fixed (a lift is unchanged up to isomorphism by re-normalising them) */
    { int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
      while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) if (!seen[dn[x][i]]) { seen[dn[x][i]] = 1; q[t++] = dn[x][i]; fixed_[de[x][i]] = 1; } } }
    for (int e = 0; e < E; e++) if (!fixed_[e]) freee[nfree++] = e;
    fprintf(stderr, "b %d E %d m %d free %d K %d; start ok=%d\n", b, E, m, nfree, K, ok_all());
    (void)order; (void)norder;
    rec_sets(0, 0);
    fprintf(stderr, "tested %lld found %lld\n", tested, found);
    return 0;
}
