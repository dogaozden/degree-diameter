/* exact.c: exact minimum of the lift cost (tabu.c cost: uncovered (base vertex, group element) pairs over all
 * sources) over ALL assignments of K chosen free voltages (from a given list of edge indices), all other
 * voltages fixed. Branch-and-bound: cost_bound stops at the first partial sum >= bound.
 * usage: exact SOL GROUP K EDGES [OUT]   EDGES = comma list of edge indices (file order, 0-based), free edges only.
 *   env: D (5), BOUND (5: report all assignments with cost < BOUND), SECS (600), PLATEAU (50: max plateau SOLs kept)
 * stdout: RESULT best <c> combos <n> secs <t> complete <0|1>; plus SOL block of the best (if best < BOUND)
 * OUT (optional): best solution as vl SOL block (overwritten on improvement).
 * PLAT file (env PLAT, optional): every assignment with cost == best, as SOL blocks (up to PLATEAU).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 64
#define MAXE 512
#define INF (1 << 30)
static int b, E, m, D = 5, W;
static int side[MAXB], eu[MAXE], ew[MAXE], volt[MAXE], fixed_[MAXE];
static int deg[MAXB], dn[MAXB][32], de[MAXB][32], dd[MAXB][32];
static uint16_t *mul; static int *inv_;
static uint64_t *cov;
static inline int dvolt(int v, int i) { int g = volt[de[v][i]]; return dd[v][i] ? inv_[g] : g; }
static int maxlen;
static void dfs(int v, int laste, int h, int len) {
    cov[(size_t)v * W + (h >> 6)] |= 1ULL << (h & 63);
    if (len == maxlen) return;
    for (int i = 0; i < deg[v]; i++) { int e = de[v][i]; if (e == laste) continue;
        dfs(dn[v][i], e, mul[(size_t)h * m + dvolt(v, i)], len + 1); }
}
static int src_order[MAXB];
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
        if (c >= bound) {
            if (k > 0) { int t = src_order[k]; memmove(src_order + 1, src_order, sizeof(int) * k); src_order[0] = t; }
            return c;
        }
    }
    return c;
}
static int par_ok(int e) { for (int f = 0; f < E; f++) if (f != e && eu[f] == eu[e] && ew[f] == ew[e] && volt[f] == volt[e]) return 0; return 1; }
static void write_sol(FILE *f) {
    fprintf(f, "SOL %d %d\n", b, E);
    for (int v = 0; v < b; v++) fprintf(f, "%d%c", side[v], v == b - 1 ? '\n' : ' ');
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", eu[e], ew[e], volt[e]);
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int K, nl, list[64], pick[8], pickv[8];
static int best = INF, bound, PLATEAU = 50, nplat = 0, complete = 1;
static long long combos = 0, nbelow = 0;
static double t0, SECS;
static FILE *OUTF, *PLATF;
static int dummy;
static void leaf(void) {
    combos++;
    if ((combos & 0xFFFF) == 0) {
        if (now() - t0 > SECS) { complete = 0; }
        if ((combos & 0x3FFFFF) == 0) fprintf(stderr, "  combos %lld best %d t %.1f\n", combos, best, now() - t0);
    }
    int c = cost_bound(bound);
    if (c >= bound) return;
    nbelow++;
    if (c < best) {
        best = c; bound = c + 1;
        fprintf(stderr, "best %d after %lld combos t %.1f\n", best, combos, now() - t0);
        if (OUTF) { rewind(OUTF); write_sol(OUTF); fflush(OUTF); }
    }
    if (c == best && PLATF && nplat < PLATEAU) { nplat++; write_sol(PLATF); fflush(PLATF); }
}
static void rec_vals(int t) {
    if (!complete) return;
    if (t == K) { leaf(); return; }
    int e = pick[t], old = volt[e];
    for (int g = 0; g < m; g++) {
        if (g == old) continue;
        volt[e] = g;
        if (!par_ok(e)) continue;
        rec_vals(t + 1);
        if (!complete) break;
    }
    volt[e] = old;
}
static void rec_sets(int start, int t) {
    if (!complete) return;
    if (t == K) { rec_vals(0); return; }
    for (int i = start; i < nl; i++) { pick[t] = list[i]; rec_sets(i + 1, t + 1); if (!complete) return; }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: exact SOL GROUP K EDGES [OUT]\n"); return 2; }
    K = atoi(argv[3]);
    if (getenv("D")) D = atoi(getenv("D"));
    SECS = getenv("SECS") ? atof(getenv("SECS")) : 600;
    bound = getenv("BOUND") ? atoi(getenv("BOUND")) : 5;
    if (getenv("PLATEAU")) PLATEAU = atoi(getenv("PLATEAU"));
    FILE *f = fopen(argv[1], "r"); char line[1024];
    if (!f) return 2;
    int got = 0;
    while (!got && fgets(line, sizeof line, f)) {
        if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
        char *p = line; if (!strncmp(p, "SOL", 3)) p += 3;
        if (sscanf(p, "%d %d", &b, &E) == 2) got = 1;
    }
    if (!got) return 2;
    { int k = 0;
      while (k < b && fgets(line, sizeof line, f)) {
        if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
        char *p = line; int x, nc;
        while (k < b && sscanf(p, "%d%n", &x, &nc) == 1) { side[k++] = x; p += nc; }
      } }
    int ne = 0;
    while (ne < E && fgets(line, sizeof line, f)) {
        if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
        int u, w, v = 0; int c = sscanf(line, "%d %d %d", &u, &w, &v);
        if (c < 2) return 2; if (c == 2) v = 0;
        if (side[u] == 1) { int t = u; u = w; w = t; }
        eu[ne] = u; ew[ne] = w; volt[ne] = v; ne++;
    }
    fclose(f);
    f = fopen(argv[2], "r"); int m_; if (!f || fscanf(f, "%d", &m_) != 1) return 2; m = m_;
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
    for (int e = 0; e < E; e++) if (fixed_[e] && volt[e] != 0) { fprintf(stderr, "tree edge %d not normalised\n", e); return 2; }
    /* edge list */
    { char *s = argv[4], *tok; char buf[4096]; strncpy(buf, s, sizeof buf - 1); buf[sizeof buf - 1] = 0;
      for (tok = strtok(buf, ","); tok; tok = strtok(NULL, ",")) { int e = atoi(tok);
        if (e < 0 || e >= E || fixed_[e]) { fprintf(stderr, "edge %d is a tree edge or out of range\n", e); return 2; }
        list[nl++] = e; } }
    for (int k = 0; k < b; k++) src_order[k] = k;
    OUTF = argc > 5 ? fopen(argv[5], "w") : NULL;
    PLATF = getenv("PLAT") ? fopen(getenv("PLAT"), "w") : NULL;
    int start = cost_bound(INF);
    fprintf(stderr, "b %d E %d m %d K %d edges %d start cost %d bound %d\n", b, E, m, K, nl, start, bound);
    t0 = now();
    rec_sets(0, 0);
    printf("RESULT best %d combos %lld below %lld secs %.1f complete %d start %d\n", best == INF ? -1 : best, combos, nbelow, now() - t0, complete, start);
    if (best < INF) { /* print the best solution: re-run is not needed, OUTF holds it */ }
    if (OUTF) fclose(OUTF);
    if (PLATF) fclose(PLATF);
    (void)dummy; (void)pickv;
    return 0;
}
