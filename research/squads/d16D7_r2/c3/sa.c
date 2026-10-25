/* sa.c - penalised simulated annealing for a maximum independent set (MIS) of an orbit graph.
 *
 * Energy of a vertex subset S:  E(S) = -|S| + lambda * e(S),  e(S) = number of edges inside S.
 * conf[v] = |N(v) cap S| is kept up to date incrementally, and so is e(S).
 * Moves (Metropolis on E):
 *   - flip: a uniformly random vertex v is added (if outside S) or removed (if inside S);
 *     dE(add v) = -1 + lambda*conf[v],  dE(remove v) = +1 - lambda*conf[v];
 *   - neighbour swap (probability pswap): random member x, random neighbour y of x outside S;
 *     dE = lambda * (conf[y] - conf[x] - 1).
 * Schedule: a seed phase starting from the start solution at low temperature (10% of the budget),
 * then NCYC reheats, each a geometric cooling from T_HOT to T_COLD over its CPU-time slice.
 * Every valid state (e(S) = 0) larger than the best is saved at once (atomic rename).
 * At the end of every cycle: repair (drop the member with most conflicts until e(S) = 0), add free
 * vertices in random order, polish with (1,2)-swaps, save if better.
 *
 * usage: sa GRAPH START_SOL OUT_SOL CPU_SECONDS [LAMBDA=1.5] [RNG_SEED=1] [PSWAP=0.3]
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int M, W, MAXD;
static int *deg, *off, *lst;   /* CSR adjacency lists */
static u64 *bits;              /* adjacency bit matrix, row v at bits + v*W */

static char *inS;
static int *conf, *mem, *pos, *perm, *Lbuf, *bestv;
static int ns, bestn = 0;
static long long ein;          /* e(S): number of edges inside S */

static double lam, pswap;
static double *tAdd, *tRem, *tSw;
static const char *outpath;

/* xoroshiro128+ */
static u64 rs0, rs1;
static inline u64 rotl(u64 x, int k) { return (x << k) | (x >> (64 - k)); }
static inline u64 rng(void) {
    u64 s0 = rs0, s1 = rs1, r = s0 + s1;
    s1 ^= s0;
    rs0 = rotl(s0, 24) ^ s1 ^ (s1 << 16);
    rs1 = rotl(s1, 37);
    return r;
}
static inline double urand(void) { return (double)(rng() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int n) { return (int)(((rng() >> 32) * (u64)n) >> 32); }
static u64 splitmix(u64 *x) {
    u64 z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static inline int isadj(int u, int v) { return (int)((bits[(size_t)u * W + (v >> 6)] >> (v & 63)) & 1ULL); }
static double cpu_now(void) { return (double)clock() / CLOCKS_PER_SEC; }
static void die(const char *msg) { fprintf(stderr, "sa: %s\n", msg); exit(1); }

static void load_graph(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) die("cannot open graph");
    int E;
    if (fscanf(f, "%d %d", &M, &E) != 2) die("bad header");
    int **nb = malloc(sizeof(int *) * M);
    deg = calloc(M, sizeof(int));
    for (int r = 0; r < M; r++) {
        int idx, rep, d;
        if (fscanf(f, "%d %d %d", &idx, &rep, &d) != 3 || idx < 0 || idx >= M || d < 0) die("bad vertex line");
        nb[idx] = malloc(sizeof(int) * (d + 1));
        for (int i = 0; i < d; i++)
            if (fscanf(f, "%d", &nb[idx][i]) != 1) die("bad neighbour");
        deg[idx] = d;
    }
    fclose(f);
    off = malloc(sizeof(int) * (M + 1));
    off[0] = 0;
    for (int v = 0; v < M; v++) off[v + 1] = off[v] + deg[v];
    lst = malloc(sizeof(int) * (size_t)off[M]);
    W = (M + 63) / 64;
    bits = calloc((size_t)M * W, sizeof(u64));
    MAXD = 0;
    for (int v = 0; v < M; v++) {
        if (deg[v] > MAXD) MAXD = deg[v];
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            if (u < 0 || u >= M || u == v) die("bad edge");
            lst[off[v] + i] = u;
            bits[(size_t)v * W + (u >> 6)] |= 1ULL << (u & 63);
        }
        free(nb[v]);
    }
    free(nb);
    for (int v = 0; v < M; v++)
        for (int i = 0; i < deg[v]; i++)
            if (!isadj(lst[off[v] + i], v)) die("graph is not symmetric");
    fprintf(stderr, "graph M=%d E=%d (header %d) maxdeg=%d\n", M, off[M] / 2, E, MAXD);
}

static void alloc_state(void) {
    inS = calloc(M, 1);
    conf = calloc(M, sizeof(int));
    mem = malloc(sizeof(int) * M);
    pos = malloc(sizeof(int) * M);
    perm = malloc(sizeof(int) * M);
    Lbuf = malloc(sizeof(int) * (MAXD + 1));
    bestv = malloc(sizeof(int) * M);
    tAdd = malloc(sizeof(double) * (MAXD + 2));
    tRem = malloc(sizeof(double) * (MAXD + 2));
    tSw = malloc(sizeof(double) * (MAXD + 2));
}

static inline void add_v(int v) {
    const int *a = lst + off[v];
    int d = deg[v];
    ein += conf[v];
    inS[v] = 1;
    pos[v] = ns;
    mem[ns++] = v;
    for (int i = 0; i < d; i++) conf[a[i]]++;
}

static inline void rem_v(int v) {
    const int *a = lst + off[v];
    int d = deg[v];
    inS[v] = 0;
    int p = pos[v], last = mem[--ns];
    mem[p] = last;
    pos[last] = p;
    ein -= conf[v];
    for (int i = 0; i < d; i++) conf[a[i]]--;
}

/* acceptance tables for the current temperature, indexed by conf value */
static void update_tables(double T) {
    for (int c = 0; c <= MAXD + 1; c++) {
        double da = -1.0 + lam * c; /* add a non-member with c member neighbours */
        double dr = 1.0 - lam * c;  /* remove a member with c member neighbours  */
        tAdd[c] = da <= 0.0 ? 1.0 : exp(-da / T);
        tRem[c] = dr <= 0.0 ? 1.0 : exp(-dr / T);
        tSw[c] = exp(-lam * c / T); /* swap with conf difference c > 0 */
    }
}

static int cmp_int(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

static void save_if_better(void) {
    if (ein != 0 || ns <= bestn) return;
    for (int i = 0; i < ns; i++)
        for (int j = i + 1; j < ns; j++)
            if (isadj(mem[i], mem[j])) die("internal error: saved set is not independent");
    memcpy(bestv, mem, sizeof(int) * ns);
    bestn = ns;
    qsort(bestv, bestn, sizeof(int), cmp_int);
    char tmp[1100];
    snprintf(tmp, sizeof tmp, "%s.tmp", outpath);
    FILE *f = fopen(tmp, "w");
    if (!f) die("cannot write output");
    for (int i = 0; i < bestn; i++) fprintf(f, "%d\n", bestv[i]);
    fclose(f);
    rename(tmp, outpath);
    fprintf(stderr, "  new best %d (cpu %.1f s)\n", bestn, cpu_now());
}

static inline void step(void) {
    if (urand() < pswap) {
        if (ns == 0) return;
        int x = mem[irand(ns)];
        int y = lst[off[x] + irand(deg[x])];
        if (inS[y]) return;
        int k = conf[y] - conf[x] - 1;
        if (k > 0 && urand() >= tSw[k]) return;
        rem_v(x);
        add_v(y);
    } else {
        int v = irand(M);
        int c = conf[v];
        if (inS[v]) {
            if (!(urand() < tRem[c])) return;
            rem_v(v);
        } else {
            if (!(urand() < tAdd[c])) return;
            add_v(v);
        }
    }
    if (ein == 0 && ns > bestn) save_if_better();
}

/* drop the member with the most conflicts until S is independent */
static void repair(void) {
    while (ein > 0) {
        int bv = -1, bc = -1;
        for (int i = 0; i < ns; i++) {
            int v = mem[i];
            if (conf[v] > bc) { bc = conf[v]; bv = v; }
        }
        rem_v(bv);
    }
}

/* add every free vertex (no member neighbour), in random order */
static void fill_free(void) {
    for (int i = 0; i < M; i++) perm[i] = i;
    for (int i = M - 1; i > 0; i--) {
        int j = irand(i + 1), t = perm[i];
        perm[i] = perm[j];
        perm[j] = t;
    }
    for (int i = 0; i < M; i++) {
        int v = perm[i];
        if (!inS[v] && conf[v] == 0) add_v(v);
    }
}

/* (1,2)-swap at x: two non-adjacent 1-tight neighbours u, w of x (their only member neighbour is x) */
static int try12(int x) {
    const int *a = lst + off[x];
    int d = deg[x], cnt = 0;
    for (int i = 0; i < d; i++) {
        int u = a[i];
        if (!inS[u] && conf[u] == 1) Lbuf[cnt++] = u;
    }
    for (int i = 0; i < cnt; i++)
        for (int j = i + 1; j < cnt; j++) {
            int u = Lbuf[i], w = Lbuf[j];
            if (!isadj(u, w)) {
                rem_v(x);
                add_v(u);
                add_v(w);
                for (int k = 0; k < d; k++) {
                    int y = a[k];
                    if (!inS[y] && conf[y] == 0) add_v(y);
                }
                return 1;
            }
        }
    return 0;
}

static void polish(void) {
    int improved = 1;
    while (improved) {
        improved = 0;
        for (int i = 0; i < ns; i++)
            if (try12(mem[i])) improved = 1;
    }
}

static void anneal(const char *tag, int cyc, double T0, double T1, double secs) {
    const int CHUNK = 1 << 16;
    double t0 = cpu_now(), next_log = 0.0;
    long long steps = 0;
    update_tables(T0);
    for (;;) {
        for (int it = 0; it < CHUNK; it++) step();
        steps += CHUNK;
        double f = (cpu_now() - t0) / secs;
        if (f >= 1.0) break;
        double T = T0 * pow(T1 / T0, f);
        update_tables(T);
        if (f >= next_log) {
            fprintf(stderr, "%s%d f=%.2f T=%.4f ns=%d ein=%lld bestn=%d\n", tag, cyc, f, T, ns, ein, bestn);
            next_log += 0.2;
        }
    }
    repair();
    fill_free();
    polish();
    save_if_better();
    fprintf(stderr, "%s%d end steps=%lld polished=%d best=%d\n", tag, cyc, steps, ns, bestn);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: sa GRAPH START_SOL OUT_SOL CPU_SECONDS [LAMBDA=1.5] [RNG_SEED=1] [PSWAP=0.3]\n");
        return 1;
    }
    const char *gpath = argv[1], *spath = argv[2];
    outpath = argv[3];
    double budget = atof(argv[4]);
    lam = argc > 5 ? atof(argv[5]) : 1.5;
    u64 seed = argc > 6 ? strtoull(argv[6], NULL, 10) : 1;
    pswap = argc > 7 ? atof(argv[7]) : 0.3;

    load_graph(gpath);
    u64 sm = seed * 0x2545F4914F6CDD1DULL + 12345;
    rs0 = splitmix(&sm);
    rs1 = splitmix(&sm);
    alloc_state();

    FILE *f = fopen(spath, "r");
    if (!f) die("cannot open start solution");
    char line[256];
    int nstart = 0;
    while (fgets(line, sizeof line, f)) {
        int v;
        if (line[0] == '#' || sscanf(line, "%d", &v) != 1) continue;
        if (v < 0 || v >= M) die("bad start vertex");
        if (!inS[v]) { add_v(v); nstart++; }
    }
    fclose(f);
    fprintf(stderr, "start: %d vertices, %lld internal edges, lambda=%.3f pswap=%.3f budget=%.1f\n",
            nstart, ein, lam, pswap, budget);
    repair();
    fill_free();
    polish();
    save_if_better();
    fprintf(stderr, "start polished: %d (best %d)\n", ns, bestn);

    /* seed phase: low temperature around the start solution */
    double s0 = 0.10 * budget;
    anneal("seed", 0, 0.20, 0.06, s0);

    /* reheat cycles */
    const int K = 5;
    double rest = budget - s0;
    for (int c = 1; c <= K; c++) anneal("reheat", c, 0.45, 0.08, rest / K);

    repair();
    fill_free();
    polish();
    save_if_better();
    fprintf(stderr, "FINAL best=%d cpu=%.1f\n", bestn, cpu_now());
    printf("%d\n", bestn);
    return 0;
}
