/* c8: grow a 6-regular bipartite base graph by NEW vertices (removing 3*NEW base edges and
   re-hanging their endpoints on the new vertices), then anneal with degree-preserving 2-switch
   moves (bipartition kept). Objective = number of unordered pairs at distance > DIAM, computed
   with bitset ball expansion. Usage: grow BASE_EDGES TARGET_N SECONDS SEED OUT T0 T1 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define DEG 6
#define DIAM 5

static int n, W;
static int col[MAXN];
static int adj[MAXN][DEG];
static int dg[MAXN];
static int bestadj[MAXN][DEG];
static uint64_t BS[2][MAXN][MAXW];
static uint64_t rs[2];

static inline uint64_t rnd(void) {
    uint64_t s1 = rs[0]; const uint64_t s0 = rs[1];
    rs[0] = s0; s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
    return rs[1] + s0;
}
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int m) { return (int)(rnd() % (uint64_t)m); }

static int has_edge(int a, int b) { for (int i = 0; i < DEG; i++) if (adj[a][i] == b) return 1; return 0; }
static void repl(int a, int old, int nw) {
    for (int i = 0; i < DEG; i++) if (adj[a][i] == old) { adj[a][i] = nw; return; }
    fprintf(stderr, "repl fail %d %d %d\n", a, old, nw); exit(2);
}

/* number of unordered pairs at distance > DIAM */
static long uncovered(void) {
    int cur = 0;
    for (int v = 0; v < n; v++) { memset(BS[0][v], 0, sizeof(uint64_t) * W); BS[0][v][v >> 6] |= 1ULL << (v & 63); }
    for (int k = 0; k < DIAM; k++) {
        int nx = 1 - cur;
        for (int v = 0; v < n; v++) {
            uint64_t *o = BS[nx][v];
            memcpy(o, BS[cur][v], sizeof(uint64_t) * W);
            for (int i = 0; i < DEG; i++) {
                uint64_t *s = BS[cur][adj[v][i]];
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        cur = nx;
    }
    long cov = 0;
    for (int v = 0; v < n; v++) for (int w = 0; w < W; w++) cov += __builtin_popcountll(BS[cur][v][w]);
    return ((long)n * n - cov) / 2;
}

static void write_graph(const char *fn, int (*A)[DEG]) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", n);
    for (int u = 0; u < n; u++) for (int i = 0; i < DEG; i++) if (A[u][i] > u) fprintf(f, "%d %d\n", u, A[u][i]);
    fclose(f);
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: grow BASE TARGET_N SECONDS SEED OUT T0 T1\n"); return 1; }
    int target = atoi(argv[2]);
    double secs = atof(argv[3]);
    uint64_t seed = strtoull(argv[4], 0, 10);
    const char *outf = argv[5];
    double T0 = atof(argv[6]), T1 = atof(argv[7]);
    rs[0] = 0x9E3779B97F4A7C15ULL ^ (seed * 0x2545F4914F6CDD1DULL + 1);
    rs[1] = 0xD1B54A32D192ED03ULL + seed * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();

    FILE *f = fopen(argv[1], "r");
    int nb, u, v;
    if (fscanf(f, "%d", &nb) != 1) return 1;
    static int eu[4000], ev[4000]; int ne = 0;
    while (fscanf(f, "%d %d", &u, &v) == 2) { eu[ne] = u; ev[ne] = v; ne++; }
    fclose(f);
    n = target; W = (n + 63) / 64;
    int NEW = n - nb;
    if (NEW % 2 || n > MAXN) { fprintf(stderr, "bad NEW\n"); return 1; }

    /* base adjacency (must be DEG-regular) */
    memset(dg, 0, sizeof dg);
    for (int i = 0; i < ne; i++) { adj[eu[i]][dg[eu[i]]++] = ev[i]; adj[ev[i]][dg[ev[i]]++] = eu[i]; }
    for (int i = 0; i < nb; i++) if (dg[i] != DEG) { fprintf(stderr, "base not %d-regular at %d\n", DEG, i); return 1; }
    /* 2-colour base by BFS */
    for (int i = 0; i < n; i++) col[i] = -1;
    static int q[MAXN]; int qh = 0, qt = 0; col[0] = 0; q[qt++] = 0;
    while (qh < qt) { int x = q[qh++]; for (int i = 0; i < DEG; i++) { int y = adj[x][i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[qt++] = y; } } }
    /* new vertices: alternate colours */
    for (int i = nb; i < n; i++) { col[i] = (i - nb) & 1; dg[i] = 0; }

    /* remove 3*NEW random base edges */
    int R = 3 * NEW;
    static int used[4000];
    int SB[400], SW[400], ns = 0;
    int removed = 0;
    while (removed < R) {
        int e = irand(ne);
        if (used[e]) continue;
        used[e] = 1; removed++;
        int a = eu[e], b = ev[e];
        int bl = col[a] == 0 ? a : b;  /* black endpoint */
        int wh = col[a] == 0 ? b : a;  /* white endpoint */
        for (int i = 0; i < DEG; i++) if (adj[bl][i] == wh) { adj[bl][i] = adj[bl][--dg[bl]]; break; }
        for (int i = 0; i < DEG; i++) if (adj[wh][i] == bl) { adj[wh][i] = adj[wh][--dg[wh]]; break; }
        SB[ns] = bl; SW[ns] = wh; ns++;
    }
    /* assign black slots to new white vertices, white slots to new black vertices */
    int NWv[400], NBv[400], nw = 0, nbk = 0;
    for (int i = nb; i < n; i++) { if (col[i] == 1) NWv[nw++] = i; else NBv[nbk++] = i; }
    for (int attempt = 0; attempt < 100000; attempt++) {
        int ok = 1;
        for (int i = ns - 1; i > 0; i--) { int j = irand(i + 1); int t = SB[i]; SB[i] = SB[j]; SB[j] = t; }
        for (int i = ns - 1; i > 0; i--) { int j = irand(i + 1); int t = SW[i]; SW[i] = SW[j]; SW[j] = t; }
        for (int k = 0; k < nw && ok; k++) for (int j = 0; j < DEG && ok; j++) for (int l = 0; l < j; l++)
            if (SB[k * DEG + j] == SB[k * DEG + l]) { ok = 0; break; }
        for (int k = 0; k < nbk && ok; k++) for (int j = 0; j < DEG && ok; j++) for (int l = 0; l < j; l++)
            if (SW[k * DEG + j] == SW[k * DEG + l]) { ok = 0; break; }
        if (ok) break;
        if (attempt == 99999) { fprintf(stderr, "no simple assignment\n"); return 1; }
    }
    for (int k = 0; k < nw; k++) for (int j = 0; j < DEG; j++) {
        int w = NWv[k], a = SB[k * DEG + j];
        adj[w][dg[w]++] = a; adj[a][dg[a]++] = w;
    }
    for (int k = 0; k < nbk; k++) for (int j = 0; j < DEG; j++) {
        int bk = NBv[k], x = SW[k * DEG + j];
        adj[bk][dg[bk]++] = x; adj[x][dg[x]++] = bk;
    }
    for (int i = 0; i < n; i++) if (dg[i] != DEG) { fprintf(stderr, "degree fix failed at %d (%d)\n", i, dg[i]); return 1; }
    /* sanity: bipartite */
    for (int x = 0; x < n; x++) for (int i = 0; i < DEG; i++) if (col[adj[x][i]] == col[x]) { fprintf(stderr, "colour clash\n"); return 1; }

    long cur = uncovered(), best = cur;
    memcpy(bestadj, adj, sizeof adj);
    fprintf(stderr, "start n=%d uncovered_pairs=%ld\n", n, cur);
    double t0 = now();
    long it = 0, acc = 0;
    /* list of black vertices for sampling */
    int blk[MAXN], nblk = 0;
    for (int i = 0; i < n; i++) if (col[i] == 0) blk[nblk++] = i;
    double T = T0;
    while (cur > 0) {
        it++;
        if ((it & 255) == 0) {
            double el = now() - t0;
            if (el > secs) break;
            T = T0 * pow(T1 / T0, el / secs);
        }
        int a = blk[irand(nblk)];
        int i = irand(DEG); int b = adj[a][i];
        int c = blk[irand(nblk)];
        if (c == a) continue;
        int j = irand(DEG); int d = adj[c][j];
        if (d == b) continue;
        if (has_edge(a, d) || has_edge(c, b)) continue;
        adj[a][i] = d; adj[c][j] = b; repl(b, a, c); repl(d, c, a);
        long nv = uncovered();
        long dl = nv - cur;
        if (dl <= 0 || urand() < exp(-(double)dl / T)) {
            cur = nv; acc++;
            if (cur < best) { best = cur; memcpy(bestadj, adj, sizeof adj);
                fprintf(stderr, "it=%ld t=%.1f best=%ld T=%.3f\n", it, now() - t0, best, T); }
        } else {
            adj[a][i] = b; adj[c][j] = d; repl(b, c, a); repl(d, a, c);
        }
        if (it % 20000 == 0) fprintf(stderr, "  it=%ld cur=%ld best=%ld T=%.3f acc=%ld\n", it, cur, best, T, acc);
    }
    memcpy(adj, bestadj, sizeof adj);
    write_graph(outf, bestadj);
    fprintf(stderr, "done it=%ld best_uncovered=%ld final_T=%.3f\n", it, best, T);
    printf("%d %ld\n", n, best);
    return 0;
}
