/* tabu.c: tabu search over single-voltage changes of a voltage lift (vl format), D = 5.
 * Started from kdesc.c (same cost: uncovered (base vertex, group element) pairs over all base sources, D for side-0
 * sources and D-1 for side-1 sources; cost 0 <=> diameter <= D; branch and bound in cost_bound).
 *
 * Each step scans ALL 1-changes (free edge e, new value g != volt[e], parallel edges kept distinct), and takes the
 * best admissible move even if it does not improve (sideways or uphill). A move is admissible if it is not tabu,
 * or it is tabu but beats the best cost seen so far (aspiration). Applying move (e: old -> g) makes "e back to old"
 * tabu for TMIN..TMAX steps (TABUEDGE=1: the edge e is frozen for that time instead). Ties are broken at random.
 * After STALL steps without a new global best, the search restarts from the best solution with KICK random
 * 1-changes and an empty tabu list (the tabu list is kept by absolute step count, so old entries expire anyway).
 * Stops at cost 0 (writes OUT), or after SECS seconds.
 *
 * usage: tabu SOL GROUP [OUT]
 *   SOL: vl-format base with voltages (lines "u w [volt]"; a leading "SOL" token and '#' lines are allowed).
 *        The spanning tree (BFS from vertex 0, as in kdesc) must have identity voltages unless INIT=random.
 *   GROUP: m, then the m x m multiplication table (element 0 = identity).
 *   env: D (5), SECS (60), SEED (1), INIT (sol | random; random = random free voltages, tree = identity),
 *        TMIN (7), TMAX (15), STALL (3000), KICK (2), TABUEDGE (0), CHECK (0: recompute cost each step)
 * stdout: RESULT best <cost> steps <n> restarts <r> secs <t>, plus SOL block if cost 0.
 * stderr: "best <cost> step <n> t <secs>" for each new global best.
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
/* full cost; returns a value >= bound (not exact) as soon as the partial sum reaches bound */
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
    fprintf(f, "%d %d\n", b, E);
    for (int v = 0; v < b; v++) fprintf(f, "%d%c", side[v], v == b - 1 ? '\n' : ' ');
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", eu[e], ew[e], volt[e]);
}
static void write_file(const char *path) { FILE *o = fopen(path, "w"); if (o) { write_sol(o); fclose(o); } }

static int getenv_int(const char *k, int def) { const char *s = getenv(k); return s ? atoi(s) : def; }

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    D = getenv_int("D", 5);
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    int TMIN = getenv_int("TMIN", 7), TMAX = getenv_int("TMAX", 15), STALL = getenv_int("STALL", 3000);
    int KICK = getenv_int("KICK", 2), TABUEDGE = getenv_int("TABUEDGE", 0), CHECK = getenv_int("CHECK", 0);
    const char *INIT = getenv("INIT") ? getenv("INIT") : "sol";
    const char *OUT = argc > 3 ? argv[3] : NULL;

    /* ---- base with voltages (line based, so "u w" lines without a voltage are accepted) ---- */
    FILE *f = fopen(argv[1], "r"); char line[1024];
    if (!f) return 2;
    int got = 0;
    while (!got && fgets(line, sizeof line, f)) {
        if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
        char *p = line; if (!strncmp(p, "SOL", 3)) p += 3;
        if (sscanf(p, "%d %d", &b, &E) == 2) got = 1;
    }
    if (!got || b > MAXB || E > MAXE) { fprintf(stderr, "bad base header\n"); return 2; }
    {   /* side line: b integers (may span lines, read by token) */
        int k = 0;
        while (k < b && fgets(line, sizeof line, f)) {
            if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
            char *p = line; int x, nc;
            while (k < b && sscanf(p, "%d%n", &x, &nc) == 1) { side[k++] = x; p += nc; }
        }
    }
    int ne = 0;
    while (ne < E && fgets(line, sizeof line, f)) {
        if (line[0] == '#' || strspn(line, " \t\r\n") == strlen(line)) continue;
        int u, w, v = 0;
        int c = sscanf(line, "%d %d %d", &u, &w, &v);
        if (c < 2) { fprintf(stderr, "bad edge line: %s", line); return 2; }
        if (c == 2) v = 0;
        if (side[u] == 1) { int t = u; u = w; w = t; }
        eu[ne] = u; ew[ne] = w; volt[ne] = v; ne++;
    }
    fclose(f);
    if (ne != E) { fprintf(stderr, "expected %d edges, read %d\n", E, ne); return 2; }

    /* ---- group ---- */
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &m) != 1) return 2;
    mul = malloc(sizeof(uint16_t) * m * m); inv_ = malloc(sizeof(int) * m);
    for (long i = 0; i < (long)m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    fclose(f);
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (mul[(size_t)x * m + y] == 0) inv_[x] = y;
    W = (m + 63) / 64; cov = malloc(sizeof(uint64_t) * b * W);

    /* ---- adjacency, spanning tree (BFS from 0, same as kdesc) ---- */
    for (int e = 0; e < E; e++) { int u = eu[e], w = ew[e];
        dn[u][deg[u]] = w; de[u][deg[u]] = e; dd[u][deg[u]] = 0; deg[u]++;
        dn[w][deg[w]] = u; de[w][deg[w]] = e; dd[w][deg[w]] = 1; deg[w]++; }
    { int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
      while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) if (!seen[dn[x][i]]) { seen[dn[x][i]] = 1; q[t++] = dn[x][i]; fixed_[de[x][i]] = 1; } } }
    int fr[MAXE], nf = 0; for (int e = 0; e < E; e++) if (!fixed_[e]) fr[nf++] = e;

    /* ---- initial state ---- */
    if (!strcmp(INIT, "random")) {
        for (int e = 0; e < E; e++) volt[e] = fixed_[e] ? 0 : (int)(rnd() % m);
        for (int i = 0; i < nf; i++) while (!par_ok(fr[i])) volt[fr[i]] = (int)(rnd() % m);
    } else {
        for (int e = 0; e < E; e++) if (fixed_[e] && volt[e] != 0) {
            fprintf(stderr, "spanning-tree edge %d has voltage %d != 0: normalise the input (gauge) first\n", e, volt[e]);
            return 2; }
    }
    for (int i = 0; i < nf; i++) if (!par_ok(fr[i])) { fprintf(stderr, "input has parallel edges with equal voltage\n"); return 2; }
    for (int k = 0; k < b; k++) src_order[k] = k;

    long *tabu_until = calloc((size_t)E * m, sizeof(long));
    long *edge_until = calloc(E, sizeof(long));
    int *bestv = malloc(sizeof(int) * E);

    int cur = cost_bound(INF);
    int gbest = cur; memcpy(bestv, volt, sizeof(int) * E);
    fprintf(stderr, "b %d E %d m %d free %d INIT %s start cost %d\n", b, E, m, nf, INIT, cur);
    if (OUT && gbest == 0) write_file(OUT);
    double t0 = now();
    long it = 0, last_imp = 0; int restarts = 0;
    while (gbest > 0 && now() - t0 < SECS) {
        it++;
        int bestc = INF, nb = 0, be = -1, bg = -1;
        for (int i = 0; i < nf; i++) {
            int e = fr[i], old = volt[e];
            for (int g = 0; g < m; g++) {
                if (g == old) continue;
                volt[e] = g;
                if (!par_ok(e)) continue;
                int tabu = TABUEDGE ? (edge_until[e] > it) : (tabu_until[(size_t)e * m + g] > it);
                int c = cost_bound(bestc + 1);       /* exact whenever c <= bestc */
                if (c > bestc) continue;
                if (tabu && c >= gbest) continue;    /* tabu, and no aspiration */
                if (c < bestc) { bestc = c; nb = 1; be = e; bg = g; }
                else if (rnd() % (++nb) == 0) { be = e; bg = g; }
            }
            volt[e] = old;
        }
        if (be < 0) {   /* every move tabu (very rare): random move */
            be = fr[rnd() % nf]; bg = (volt[be] + 1 + rnd() % (m - 1)) % m;
            volt[be] = bg; bestc = cost_bound(INF);
        } else {
            int old = volt[be];
            volt[be] = bg;
            int tt = TMIN + (int)(rnd() % (TMAX - TMIN + 1));
            if (TABUEDGE) edge_until[be] = it + tt; else tabu_until[(size_t)be * m + old] = it + tt;
        }
        cur = bestc;
        if (CHECK) { int chk = cost_bound(INF); if (chk != cur) { fprintf(stderr, "CHECK mismatch %d vs %d\n", chk, cur); return 3; } }
        if (cur < gbest) {
            gbest = cur; memcpy(bestv, volt, sizeof(int) * E); last_imp = it;
            fprintf(stderr, "best %d step %ld t %.1f\n", gbest, it, now() - t0);
            if (OUT) write_file(OUT);
        } else if (it - last_imp > STALL) {   /* long stall: restart from the best solution with a few kicks */
            memcpy(volt, bestv, sizeof(int) * E);
            for (int k = 0; k < KICK; k++) {
                int e = fr[rnd() % nf]; int g;
                do { g = (int)(rnd() % m); volt[e] = g; } while (g == bestv[e] || !par_ok(e));
            }
            cur = cost_bound(INF); restarts++; last_imp = it;
        }
        if (it % 2000 == 0) fprintf(stderr, "  step %ld cur %d best %d t %.1f\n", it, cur, gbest, now() - t0);
    }
    memcpy(volt, bestv, sizeof(int) * E);
    if (OUT) write_file(OUT);
    printf("RESULT best %d steps %ld restarts %d secs %.1f\n", gbest, it, restarts, now() - t0);
    if (gbest == 0) { printf("SOL "); write_sol(stdout); }
    return 0;
}
