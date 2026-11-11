/* hx.c (w4, handsoff-49): simulated annealing over voltage assignments of a regular lift of the incidence graph of the
   split Cayley hexagon H(3) (728 vertices, 4-regular, bipartite, girth 12, diameter 6).
   Lift over G (|G| = k): vertex (v,x) = v*k+x; base edge (a,b) with voltage g (a point, b line):
   lift edges (a,x) ~ (b, x*g) for all x. Directed b->a has voltage g^-1.
   Walks from root (u,e): S[v][x] = set (bitset over roots u) of roots u having a walk of length <= D to (v,x).
   S_t[v][y] |= S_{t-1}[w][x] for each directed edge w->v of voltage g with y = x*g.
   cost = sum over (v,x) of (728 - #roots reaching (v,x) within D). Cost 0 <=> diameter <= D of the lift.
   Usage: hx GROUP seconds seed T0 T1 OUTPREFIX [INITSOL]
     GROUP = cyc:k  or  file.bin (groups.py format: int32 N, N*N uint16, T[g][h] = g*h, identity 0).
     INITSOL: lines "e g" (edge index in base.txt order, voltage) to start from.
   Writes OUTPREFIX.best (lines "e g" for all 1456 edges, best state) and, when cost 0, OUTPREFIX.edges.
   Prints progress lines "P ..." and "RESULT best=<cost> ..." at the end. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define NB 728
#define NE 1456
#define W 12
#define MAXK 64
#define D 9
#define NP 364

static int k;
static uint16_t *T;      /* T[x*k+g] = x*g */
static int inv_[MAXK];
static int ea[NE], eb[NE], ev[NE], tree_[NE];
static int cot[NE], ncot = 0;
static int ninc[NB], incw[NB][4], incg[NB][4];
static uint64_t SA_[NB][MAXK][W], SB_[NB][MAXK][W];

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
        k = N;
        T = malloc(sizeof(uint16_t) * k * k);
        if (fread(T, 2, (size_t)k * k, f) != (size_t)k * k) { fprintf(stderr, "short group file\n"); exit(1); }
        fclose(f);
    }
    if (k > MAXK) { fprintf(stderr, "k too big\n"); exit(1); }
    for (int g = 0; g < k; g++) {
        int found = -1;
        for (int h = 0; h < k; h++) if (T[g * k + h] == 0) { found = h; break; }
        inv_[g] = found;
    }
}

static void load_base(const char *path) {
    FILE *f = fopen(path, "r");
    int nb, m;
    if (!f || fscanf(f, "%d %d", &nb, &m) != 2 || nb != NB || m != NE) { fprintf(stderr, "bad base\n"); exit(1); }
    for (int e = 0; e < NE; e++) {
        int u, v;
        if (fscanf(f, "%d %d", &u, &v) != 2) exit(1);
        if (u > v) { int t = u; u = v; v = t; }
        ea[e] = u; eb[e] = v; /* u point (< NP), v line */
    }
    fclose(f);
    /* spanning tree by BFS from vertex 0 */
    static int adj[NB][4], deg[NB], vis[NB], q[NB];
    memset(deg, 0, sizeof deg);
    for (int e = 0; e < NE; e++) {
        adj[ea[e]][deg[ea[e]]++] = e;
        adj[eb[e]][deg[eb[e]]++] = e;
    }
    memset(tree_, 0, sizeof tree_);
    memset(vis, 0, sizeof vis);
    int qh = 0, qt = 0; q[qt++] = 0; vis[0] = 1;
    while (qh < qt) {
        int x = q[qh++];
        for (int i = 0; i < deg[x]; i++) {
            int e = adj[x][i];
            int y = (ea[e] == x) ? eb[e] : ea[e];
            if (!vis[y]) { vis[y] = 1; tree_[e] = 1; q[qt++] = y; }
        }
    }
    ncot = 0;
    for (int e = 0; e < NE; e++) if (!tree_[e]) cot[ncot++] = e;
    /* incoming lists: directed a->b has voltage g; directed b->a has g^-1 */
    memset(ninc, 0, sizeof ninc);
}

static void build_inc(void) {
    /* in-edges of each vertex, voltages ev[] must be set; called after each change of voltages (cheap) */
    memset(ninc, 0, sizeof ninc);
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = eb[e], g = ev[e];
        /* walk a -> b uses voltage g: contributes to S[b] from S[a] */
        incw[b][ninc[b]] = a; incg[b][ninc[b]] = g; ninc[b]++;
        /* walk b -> a uses voltage inv(g) */
        incw[a][ninc[a]] = b; incg[a][ninc[a]] = inv_[g]; ninc[a]++;
    }
}

static uint64_t (*Scur)[MAXK][W] = SA_, (*Snxt)[MAXK][W] = SB_;

/* cost of current voltages ev[] */
static int eval_cost(void) {
    build_inc();
    memset(SA_, 0, sizeof SA_);
    for (int v = 0; v < NB; v++) SA_[v][0][v >> 6] |= 1ULL << (v & 63);
    Scur = SA_; Snxt = SB_;
    for (int step = 1; step <= D; step++) {
        memcpy(Snxt, Scur, sizeof SA_);
        for (int v = 0; v < NB; v++) {
            for (int i = 0; i < ninc[v]; i++) {
                int w = incw[v][i], g = incg[v][i];
                for (int x = 0; x < k; x++) {
                    int y = T[x * k + g];
                    uint64_t *dst = Snxt[v][y];
                    const uint64_t *src = Scur[w][x];
                    for (int j = 0; j < W; j++) dst[j] |= src[j];
                }
            }
        }
        uint64_t (*t)[MAXK][W] = Scur; Scur = Snxt; Snxt = t;
    }
    int cost = 0;
    for (int v = 0; v < NB; v++)
        for (int x = 0; x < k; x++) {
            int c = 0;
            for (int j = 0; j < W; j++) c += __builtin_popcountll(Scur[v][x][j]);
            cost += NB - c;
        }
    return cost;
}

static void write_sol(const char *path) {
    FILE *f = fopen(path, "w");
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d\n", e, ev[e]);
    fclose(f);
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    fprintf(f, "%d\n", NB * k);
    for (int e = 0; e < NE; e++)
        for (int x = 0; x < k; x++)
            fprintf(f, "%d %d\n", ea[e] * k + x, eb[e] * k + T[x * k + ev[e]]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: hx GROUP seconds seed T0 T1 OUTPREFIX [INITSOL]\n"); return 1; }
    load_group(argv[1]);
    double secs = atof(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    const char *outp = argv[6];
    load_base("base.txt");
    for (int e = 0; e < NE; e++) ev[e] = tree_[e] ? 0 : (int)(rnd() % k);
    if (argc > 7) {
        FILE *f = fopen(argv[7], "r");
        int e, g;
        while (f && fscanf(f, "%d %d", &e, &g) == 2) ev[e] = g;
        if (f) fclose(f);
    }
    int cur = eval_cost(), best = cur;
    int bestv[NE]; memcpy(bestv, ev, sizeof ev);
    char path[512];
    clock_t t0 = clock();
    double T = T0;
    long it = 0, acc = 0;
    fprintf(stderr, "start cost %d k=%d ncot=%d\n", cur, k, ncot);
    while (1) {
        if ((it & 15) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            double fr = el / secs;
            T = T0 * pow(T1 / T0, fr);
            if ((it & 4095) == 0) fprintf(stderr, "P it=%ld t=%.0f T=%.3f cur=%d best=%d acc=%ld\n", it, el, T, cur, best, acc);
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
                best = cur; memcpy(bestv, ev, sizeof ev);
                fprintf(stderr, "NEWBEST %d at it=%ld\n", best, it);
                if (best == 0) break;
            }
        } else {
            ev[e] = old;
        }
    }
    memcpy(ev, bestv, sizeof ev);
    int chk = eval_cost();
    snprintf(path, sizeof path, "%s.best", outp);
    write_sol(path);
    if (chk == 0 || getenv("WRITE_EDGES")) { snprintf(path, sizeof path, "%s.edges", outp); write_edges(path); }
    printf("RESULT best=%d k=%d n=%d it=%ld acc=%ld check=%d\n", best, k, NB * k, it, acc, chk);
    return 0;
}
