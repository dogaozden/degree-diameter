/* kdesc.c: exact steepest descent over the 1- and 2-change neighbourhoods of a voltage lift (vl format), D = 5.
 *
 * Cost = number of uncovered (base vertex, group element) pairs over all base sources (as in vl.c): a side-0
 * source must reach every fibre within D, a side-1 source the side-1 fibres within D - 1; cost 0 <=> diameter <= D.
 * Each step scans every change of one non-tree voltage and every change of two (C(F,2) m^2 candidates), with
 * branch-and-bound on the partial cost (sources are summed one at a time and a candidate is dropped as soon as it
 * cannot beat the best found in this scan), and applies the best move if it lowers the cost; ties are broken at
 * random. Stops at a 2-opt local minimum, at cost 0 (prints SOL and writes OUT), or after MAXSTEPS steps.
 * usage: kdesc SOL GROUP [OUT]     env: D (5), SEED (1), MAXSTEPS (50), K2 (1: also scan 2-changes)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 64
#define MAXE 512
static int b, E, m, D = 5, W;
static int side[MAXB], eu[MAXE], ew[MAXE], volt[MAXE], fixed_[MAXE];
static int deg[MAXB], dn[MAXB][32], de[MAXB][32], dd[MAXB][32];
static uint16_t *mul; static int *inv_;
static uint64_t *cov;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static inline int dvolt(int v, int i) { int g = volt[de[v][i]]; return dd[v][i] ? inv_[g] : g; }
static int maxlen;
static void dfs(int v, int laste, int h, int len) {
    cov[(size_t)v * W + (h >> 6)] |= 1ULL << (h & 63);
    if (len == maxlen) return;
    for (int i = 0; i < deg[v]; i++) { int e = de[v][i]; if (e == laste) continue;
        dfs(dn[v][i], e, mul[(size_t)h * m + dvolt(v, i)], len + 1); }
}
static int src_order[MAXB];
/* full cost, abandoning (returning a value >= bound) once the partial sum reaches bound */
static int cost_bound(int bound) {
    int c = 0;
    for (int k = 0; k < b; k++) {
        int s = src_order[k];
        memset(cov, 0, sizeof(uint64_t) * b * W);
        maxlen = side[s] == 0 ? D : D - 1;
        dfs(s, -1, 0, 0);
        for (int v = 0; v < b; v++) {
            if (side[s] == 1 && side[v] == 0) continue;
            int cnt = 0; for (int w = 0; w < W; w++) cnt += __builtin_popcountll(cov[(size_t)v * W + w]);
            c += m - cnt;
        }
        if (c >= bound) {   /* move the failing source to the front: later candidates fail faster */
            if (k > 0) { int t = src_order[k]; memmove(src_order + 1, src_order, sizeof(int) * k); src_order[0] = t; }
            return c;
        }
    }
    return c;
}
static int par_ok(int e) { for (int f = 0; f < E; f++) if (f != e && eu[f] == eu[e] && ew[f] == ew[e] && volt[f] == volt[e]) return 0; return 1; }
static void write_sol(FILE *f) {
    fprintf(f, "%d %d\n", b, E);
    for (int v = 0; v < b; v++) fprintf(f, "%d%c", side[v], v == b - 1 ? '\n' : ' ');
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", eu[e], ew[e], volt[e]);
}

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    if (getenv("D")) D = atoi(getenv("D"));
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    int MAXSTEPS = getenv("MAXSTEPS") ? atoi(getenv("MAXSTEPS")) : 50, K2 = getenv("K2") ? atoi(getenv("K2")) : 1;
    FILE *f = fopen(argv[1], "r"); char line[512];
    if (!f || !fgets(line, sizeof line, f)) return 2;
    if (!strncmp(line, "SOL", 3)) { if (sscanf(line + 3, "%d %d", &b, &E) != 2) return 2; }
    else if (sscanf(line, "%d %d", &b, &E) != 2) return 2;
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
    { int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
      while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) if (!seen[dn[x][i]]) { seen[dn[x][i]] = 1; q[t++] = dn[x][i]; fixed_[de[x][i]] = 1; } } }
    int fr[MAXE], nf = 0; for (int e = 0; e < E; e++) if (!fixed_[e]) fr[nf++] = e;
    for (int k = 0; k < b; k++) src_order[k] = k;
    int cur = cost_bound(1 << 30);
    fprintf(stderr, "b %d E %d m %d free %d start cost %d\n", b, E, m, nf, cur);
    double t0 = now();
    for (int step = 0; step < MAXSTEPS && cur > 0; step++) {
        int best = cur, nbest = 0, be1 = -1, bv1 = 0, be2 = -1, bv2 = 0; long tested = 0;
        /* 1-changes */
        for (int i = 0; i < nf; i++) { int e = fr[i], old = volt[e];
            for (int g = 0; g < m; g++) { if (g == old) continue; volt[e] = g; if (!par_ok(e)) continue;
                int c = cost_bound(best + 1); tested++;
                if (c < best) { best = c; nbest = 1; be1 = e; bv1 = g; be2 = -1; }
                else if (c == best && best < cur && rnd() % (++nbest) == 0) { be1 = e; bv1 = g; be2 = -1; } }
            volt[e] = old; }
        /* 2-changes */
        if (K2) for (int i = 0; i < nf; i++) for (int j = i + 1; j < nf; j++) {
            int e1 = fr[i], e2 = fr[j], o1 = volt[e1], o2 = volt[e2];
            for (int g1 = 0; g1 < m; g1++) { if (g1 == o1) continue; volt[e1] = g1; if (!par_ok(e1)) continue;
                for (int g2 = 0; g2 < m; g2++) { if (g2 == o2) continue; volt[e2] = g2; if (!par_ok(e2)) continue;
                    int c = cost_bound(best + 1); tested++;
                    if (c < best) { best = c; nbest = 1; be1 = e1; bv1 = g1; be2 = e2; bv2 = g2; }
                    else if (c == best && best < cur && rnd() % (++nbest) == 0) { be1 = e1; bv1 = g1; be2 = e2; bv2 = g2; } }
                volt[e2] = o2; }
            volt[e1] = o1; volt[e2] = o2;
            if (best == 0) break;
        }
        fprintf(stderr, "step %d cost %d -> %d (tested %ld, ties %d, %.1f s)\n", step, cur, best, tested, nbest, now() - t0);
        if (best >= cur) break;
        volt[be1] = bv1; if (be2 >= 0) volt[be2] = bv2; cur = best;
        if (argc > 3) { FILE *o = fopen(argv[3], "w"); if (o) { write_sol(o); fclose(o); } }
    }
    printf("RESULT cost %d secs %.1f\n", cur, now() - t0);
    if (cur == 0) { printf("SOL "); write_sol(stdout); }
    return 0;
}
