/* hg.c (w4, handsoff-49): annealing over voltage assignments of a regular lift of ANY small 4-regular base graph
   (<= 64 vertices, bipartite or not). Same walk-bitset evaluator as hx.c, roots = all base vertices (one 64-bit word).
   Lift over G (|G| = k): vertex (v,x) = v*k+x; base edge (a,b) voltage g: lift edges (a,x) ~ (b, x*g).
   cost = sum over roots u and targets (v,x) of [no walk of length <= D from u to v with voltage x]
        = 2 * far_pairs / k (exact; checked against score48 on random lifts).
   Usage: hg BASE GROUP seconds seed T0 T1 OUTPREFIX [INITSOL]
     BASE: text file "b m", then m lines "u v" (simple graph, 4-regular)
     GROUP: cyc:k or file.bin (groups.py format: int32 N, N*N uint16, T[x*k+g] = x*g)
   Writes OUTPREFIX.best (lines "e g") and, when cost 0 or WRITE_EDGES set, OUTPREFIX.edges.
   Final line: RESULT best=<cost> k=<k> n=<b*k> ... */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 64
#define MAXE 256
#define MAXK 1024
#define D 9

static int nb, ne, k;
static uint16_t *T;
static int inv_[MAXK];
static int ea[MAXE], eb[MAXE], ev[MAXE], tree_[MAXE];
static int cot[MAXE], ncot;
static int ninc[MAXB], incw[MAXB][8], incg[MAXB][8];
static uint64_t SA_[MAXB][MAXK], SB_[MAXB][MAXK];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void load_group(const char *spec) {
    if (strncmp(spec, "cyc:", 4) == 0) {
        k = atoi(spec + 4);
        T = malloc(sizeof(uint16_t) * k * k);
        for (int x = 0; x < k; x++) for (int g = 0; g < k; g++) T[x * k + g] = (uint16_t)((x + g) % k);
    } else {
        FILE *f = fopen(spec, "rb");
        if (!f) { perror("group"); exit(1); }
        int32_t N; if (fread(&N, 4, 1, f) != 1) exit(1);
        k = N; T = malloc(sizeof(uint16_t) * k * k);
        if (fread(T, 2, (size_t)k * k, f) != (size_t)k * k) { fprintf(stderr, "short group\n"); exit(1); }
        fclose(f);
    }
    if (k > MAXK) { fprintf(stderr, "k too big\n"); exit(1); }
    for (int g = 0; g < k; g++) for (int h = 0; h < k; h++) if (T[g * k + h] == 0) { inv_[g] = h; break; }
}

static void load_base(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f || fscanf(f, "%d %d", &nb, &ne) != 2) { fprintf(stderr, "bad base\n"); exit(1); }
    if (nb > MAXB || ne > MAXE) { fprintf(stderr, "base too big\n"); exit(1); }
    for (int e = 0; e < ne; e++) if (fscanf(f, "%d %d", &ea[e], &eb[e]) != 2) exit(1);
    fclose(f);
    /* BFS spanning tree from 0: tree edges get voltage 0 */
    int adjE[MAXB][8], deg[MAXB], vis[MAXB] = {0}, q[MAXB], qh = 0, qt = 0;
    memset(deg, 0, sizeof deg);
    for (int e = 0; e < ne; e++) { adjE[ea[e]][deg[ea[e]]++] = e; adjE[eb[e]][deg[eb[e]]++] = e; }
    memset(tree_, 0, sizeof tree_);
    q[qt++] = 0; vis[0] = 1;
    while (qh < qt) {
        int x = q[qh++];
        for (int i = 0; i < deg[x]; i++) {
            int e = adjE[x][i];
            int y = (ea[e] == x) ? eb[e] : ea[e];
            if (!vis[y]) { vis[y] = 1; tree_[e] = 1; q[qt++] = y; }
        }
    }
    for (int i = 0; i < nb; i++) if (!vis[i]) { fprintf(stderr, "base disconnected\n"); exit(1); }
    ncot = 0;
    for (int e = 0; e < ne; e++) if (!tree_[e]) cot[ncot++] = e;
}

static void build_inc(void) {
    memset(ninc, 0, sizeof ninc);
    for (int e = 0; e < ne; e++) {
        int a = ea[e], b = eb[e], g = ev[e];
        incw[b][ninc[b]] = a; incg[b][ninc[b]] = g; ninc[b]++;
        incw[a][ninc[a]] = b; incg[a][ninc[a]] = inv_[g]; ninc[a]++;
    }
}

static int eval_cost(void) {
    build_inc();
    memset(SA_, 0, sizeof SA_);
    for (int v = 0; v < nb; v++) SA_[v][0] |= 1ULL << v;
    uint64_t (*cur)[MAXK] = SA_, (*nxt)[MAXK] = SB_;
    for (int step = 1; step <= D; step++) {
        for (int v = 0; v < nb; v++) memcpy(nxt[v], cur[v], sizeof(uint64_t) * k);
        for (int v = 0; v < nb; v++)
            for (int i = 0; i < ninc[v]; i++) {
                int w = incw[v][i], g = incg[v][i];
                for (int x = 0; x < k; x++) nxt[v][T[x * k + g]] |= cur[w][x];
            }
        uint64_t (*t)[MAXK] = cur; cur = nxt; nxt = t;
    }
    int cost = 0;
    for (int v = 0; v < nb; v++)
        for (int x = 0; x < k; x++) cost += nb - __builtin_popcountll(cur[v][x]);
    return cost;
}

static void write_sol(const char *path) {
    FILE *f = fopen(path, "w");
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d\n", e, ev[e]);
    fclose(f);
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    fprintf(f, "%d\n", nb * k);
    for (int e = 0; e < ne; e++)
        for (int x = 0; x < k; x++)
            fprintf(f, "%d %d\n", ea[e] * k + x, eb[e] * k + T[x * k + ev[e]]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: hg BASE GROUP seconds seed T0 T1 OUTPREFIX [INITSOL]\n"); return 1; }
    load_base(argv[1]);
    load_group(argv[2]);
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double T0 = atof(argv[5]), T1 = atof(argv[6]);
    const char *outp = argv[7];
    for (int e = 0; e < ne; e++) ev[e] = tree_[e] ? 0 : (int)(rnd() % k);
    if (argc > 8) {
        FILE *f = fopen(argv[8], "r"); int e, g;
        while (f && fscanf(f, "%d %d", &e, &g) == 2) ev[e] = g;
        if (f) fclose(f);
    }
    int cur = eval_cost(), best = cur;
    int bestv[MAXE]; memcpy(bestv, ev, sizeof(int) * ne);
    fprintf(stderr, "base b=%d m=%d k=%d n=%d start cost %d\n", nb, ne, k, nb * k, cur);
    clock_t t0 = clock();
    double T = T0;
    long it = 0, acc = 0;
    while (ncot > 0) {
        if ((it & 15) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            T = T0 * pow(T1 / T0, el / secs);
            if ((it & 65535) == 0) fprintf(stderr, "P it=%ld t=%.0f T=%.3f cur=%d best=%d\n", it, el, T, cur, best);
        }
        it++;
        int e = cot[rnd() % ncot];
        int old = ev[e];
        int ng = (int)(rnd() % (k - 1)); if (ng >= old) ng++;
        ev[e] = ng;
        int nc = eval_cost();
        int dlt = nc - cur;
        if (dlt <= 0 || urand() < exp(-dlt / T)) {
            cur = nc; acc++;
            if (cur < best) {
                best = cur; memcpy(bestv, ev, sizeof(int) * ne);
                if (best == 0) break;
            }
        } else ev[e] = old;
    }
    memcpy(ev, bestv, sizeof(int) * ne);
    int chk = eval_cost();
    char path[512];
    snprintf(path, sizeof path, "%s.best", outp); write_sol(path);
    if (chk == 0 || getenv("WRITE_EDGES")) { snprintf(path, sizeof path, "%s.edges", outp); write_edges(path); }
    printf("RESULT best=%d k=%d n=%d it=%ld acc=%ld check=%d\n", best, k, nb * k, it, acc, chk);
    return 0;
}
