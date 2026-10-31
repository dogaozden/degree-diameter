/* tsym.c: tabu search over SYMMETRIC voltage lifts (c11). Same cost as shared/tabu.c (uncovered (source, vertex, element)
 * triples for diameter D), but the voltages obey a symmetry given by a SYM file:
 *   ptype 0: free representative e whose partner p (ptype 1) gets volt f(volt e);
 *   ptype 2: self-fixed free representative, volt restricted to F = {g : f(g) = g};
 *   ptype 3: tree edge, volt fixed to 0 (not moved).
 * f defaults to the inverse map (theta = id, side-swapping sigma); FMAP=file overrides (m integers, f(g) for g=0..m-1).
 * usage: tsym BASE SYM GROUP [OUT]     env: D (5), SECS (60), SEED (1), INIT (random|sol), TMIN (7), TMAX (15),
 *   STALL (3000), KICK (2), FMAP (file), VERBOSE (0)
 * stdout: RESULT best <cost> steps <n> restarts <r> secs <t>, and SOL block if cost 0.
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
static int side[MAXB], eu[MAXE], ew[MAXE], volt[MAXE], ptype[MAXE], partner[MAXE];
static int deg[MAXB], dn[MAXB][32], de[MAXB][32], dd[MAXB][32];
static uint16_t *mul; static int *inv_, *fmap, *allowed_fixed; static int nfixed;
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
static int ok_all(void) { for (int e = 0; e < E; e++) if (!par_ok(e)) return 0; return 1; }
/* set representative e to g (and its partner); returns 0 if a parallel-edge clash results */
static void setv(int e, int g) { volt[e] = g; if (ptype[e] == 0) volt[partner[e]] = fmap[g]; }
static int clash(int e) { if (!par_ok(e)) return 1; if (ptype[e] == 0 && !par_ok(partner[e])) return 1; return 0; }
static void write_sol(FILE *f) {
    fprintf(f, "%d %d\n", b, E);
    for (int v = 0; v < b; v++) fprintf(f, "%d%c", side[v], v == b - 1 ? '\n' : ' ');
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", eu[e], ew[e], volt[e]);
}
static void write_file(const char *path) { FILE *o = fopen(path, "w"); if (o) { write_sol(o); fclose(o); } }
static int getenv_int(const char *k, int def) { const char *s = getenv(k); return s ? atoi(s) : def; }

int main(int argc, char **argv) {
    if (argc < 4) return 2;
    D = getenv_int("D", 5);
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    int TMIN = getenv_int("TMIN", 7), TMAX = getenv_int("TMAX", 15), STALL = getenv_int("STALL", 3000);
    int KICK = getenv_int("KICK", 2);
    const char *INIT = getenv("INIT") ? getenv("INIT") : "random";
    const char *OUT = argc > 4 ? argv[4] : NULL;
    char line[1024];
    /* ---- base ---- */
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    int got = 0;
    while (!got && fgets(line, sizeof line, f)) {
        if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
        char *p = line; if (!strncmp(p, "SOL", 3)) p += 3;
        if (sscanf(p, "%d %d", &b, &E) == 2) got = 1;
    }
    if (!got || b > MAXB || E > MAXE) { fprintf(stderr, "bad base header\n"); return 2; }
    { int k = 0;
      while (k < b && fgets(line, sizeof line, f)) {
        if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
        char *p = line; int x, nc;
        while (k < b && sscanf(p, "%d%n", &x, &nc) == 1) { side[k++] = x; p += nc; } } }
    int ne = 0;
    while (ne < E && fgets(line, sizeof line, f)) {
        if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
        int u, w, v = 0; int c = sscanf(line, "%d %d %d", &u, &w, &v);
        if (c < 2) return 2;
        if (side[u] == 1) { int t = u; u = w; w = t; }
        eu[ne] = u; ew[ne] = w; volt[ne] = 0; ne++;
    }
    fclose(f);
    if (ne != E) { fprintf(stderr, "expected %d edges\n", E); return 2; }
    /* ---- group ---- */
    f = fopen(argv[3], "r"); if (!f || fscanf(f, "%d", &m) != 1) return 2;
    mul = malloc(sizeof(uint16_t) * m * m); inv_ = malloc(sizeof(int) * m);
    for (long i = 0; i < (long)m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    fclose(f);
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (mul[(size_t)x * m + y] == 0) inv_[x] = y;
    fmap = malloc(sizeof(int) * m); allowed_fixed = malloc(sizeof(int) * m); nfixed = 0;
    if (getenv("FMAP")) { FILE *g = fopen(getenv("FMAP"), "r"); if (!g) return 2;
        for (int x = 0; x < m; x++) if (fscanf(g, "%d", &fmap[x]) != 1) return 2; fclose(g); }
    else for (int x = 0; x < m; x++) fmap[x] = inv_[x];
    for (int x = 0; x < m; x++) if (fmap[x] == x) allowed_fixed[nfixed++] = x;
    /* ---- symmetry file: ptype partner per edge ---- */
    f = fopen(argv[2], "r"); if (!f) return 2;
    for (int e = 0; e < E; e++) { if (fscanf(f, "%d %d", &ptype[e], &partner[e]) != 2) { fprintf(stderr, "bad sym\n"); return 2; } }
    fclose(f);
    /* ---- adjacency ---- */
    for (int e = 0; e < E; e++) { int u = eu[e], w = ew[e];
        dn[u][deg[u]] = w; de[u][deg[u]] = e; dd[u][deg[u]] = 0; deg[u]++;
        dn[w][deg[w]] = u; de[w][deg[w]] = e; dd[w][deg[w]] = 1; deg[w]++; }
    W = (m + 63) / 64; cov = malloc(sizeof(uint64_t) * b * W);
    int fr[MAXE], nf = 0; for (int e = 0; e < E; e++) if (ptype[e] == 0 || ptype[e] == 2) fr[nf++] = e;
    /* ---- initial state ---- */
    if (!strcmp(INIT, "random")) {
        for (int e = 0; e < E; e++) if (ptype[e] == 3) volt[e] = 0;
        int tries = 0;
        do {
            for (int i = 0; i < nf; i++) { int e = fr[i];
                int g = ptype[e] == 2 ? allowed_fixed[rnd() % nfixed] : (int)(rnd() % m);
                setv(e, g); }
            tries++;
        } while (!ok_all() && tries < 100000);
        if (!ok_all()) { fprintf(stderr, "no clash-free start\n"); return 2; }
    } else {
        for (int e = 0; e < E; e++) if (ptype[e] == 3 && volt[e] != 0) return 2;
        if (!ok_all()) { fprintf(stderr, "input clash\n"); return 2; }
    }
    for (int k = 0; k < b; k++) src_order[k] = k;
    long *tabu_until = calloc((size_t)E * m, sizeof(long));
    int *bestv = malloc(sizeof(int) * E);
    int cur = cost_bound(INF);
    int gbest = cur; memcpy(bestv, volt, sizeof(int) * E);
    if (getenv("VERBOSE")) fprintf(stderr, "b %d E %d m %d reps %d start cost %d\n", b, E, m, nf, cur);
    if (OUT && gbest == 0) write_file(OUT);
    double t0 = now();
    long it = 0, last_imp = 0; int restarts = 0;
    while (gbest > 0 && now() - t0 < SECS) {
        it++;
        int bestc = INF, nb = 0, be = -1, bg = -1;
        for (int i = 0; i < nf; i++) {
            int e = fr[i], old = volt[e];
            int nv = ptype[e] == 2 ? nfixed : m;
            for (int t = 0; t < nv; t++) {
                int g = ptype[e] == 2 ? allowed_fixed[t] : t;
                if (g == old) continue;
                int po = ptype[e] == 0 ? volt[partner[e]] : 0;
                setv(e, g);
                if (clash(e)) { if (ptype[e] == 0) volt[partner[e]] = po; volt[e] = old; continue; }
                int tabu = tabu_until[(size_t)e * m + g] > it;
                int c = cost_bound(bestc + 1);
                if (c <= bestc) {
                    if (!(tabu && c >= gbest)) {
                        if (c < bestc) { bestc = c; nb = 1; be = e; bg = g; }
                        else if (rnd() % (++nb) == 0) { be = e; bg = g; }
                    }
                }
                if (ptype[e] == 0) volt[partner[e]] = po; volt[e] = old;
            }
        }
        if (be < 0) {
            be = fr[rnd() % nf];
            do { bg = ptype[be] == 2 ? allowed_fixed[rnd() % nfixed] : (int)(rnd() % m); } while (bg == volt[be]);
            setv(be, bg); bestc = cost_bound(INF);
        } else {
            int old = volt[be];
            setv(be, bg);
            int tt = TMIN + (int)(rnd() % (TMAX - TMIN + 1));
            tabu_until[(size_t)be * m + old] = it + tt;
        }
        cur = bestc;
        if (cur < gbest) {
            gbest = cur; memcpy(bestv, volt, sizeof(int) * E); last_imp = it;
            fprintf(stderr, "best %d step %ld t %.1f\n", gbest, it, now() - t0);
            if (OUT) write_file(OUT);
        } else if (it - last_imp > STALL) {
            memcpy(volt, bestv, sizeof(int) * E);
            for (int k = 0; k < KICK; k++) {
                int e = fr[rnd() % nf]; int g, guard = 0;
                do { g = ptype[e] == 2 ? allowed_fixed[rnd() % nfixed] : (int)(rnd() % m); } while (g == volt[e] && ++guard < 100);
                setv(e, g);
            }
            cur = cost_bound(INF); restarts++; last_imp = it;
        }
    }
    memcpy(volt, bestv, sizeof(int) * E);
    if (OUT) write_file(OUT);
    printf("RESULT best %d steps %ld restarts %d secs %.1f\n", gbest, it, restarts, now() - t0);
    if (gbest == 0) { printf("SOL "); write_sol(stdout); }
    return 0;
}
