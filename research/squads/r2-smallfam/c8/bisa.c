/* bisa.c: simulated annealing over cubic bipartite graphs with 85 white + 85 black vertices (170 vertices).
   Moves: bipartite 2-switches (w1-b1, w2-b2 -> w1-b2, w2-b1; multi-edges rejected).
   Cost: number of ordered pairs (v,u), v != u, with dist(v,u) > DIAM (bit-parallel ball growth).
   Starts:
     splice  Conder's 168-vertex graph (file), try every single splice (delete w1-b1 and w2-b2, add W adj b1,b2,B and
             B adj w1,w2,W), keep the cheapest splice as the start;
     rand    random cubic bipartite graph (circulant offsets 0,1,3 mod 85, then random 2-switches).
   Usage: ./bisa splice|rand BASE168|- SEED SECS T0 T1 CYCLE OUTDIR TAG
   Writes OUTDIR/bisa_TAG_best.edges (first line 170, then "w b" lines; white 0..84, black 85..169).
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
#include <limits.h>

#define H 85
#define N 170
#define NW 3
#define DIAM 7
#define NE (H * 3)
typedef uint64_t u64;

static int E[NE][2];          /* E[k][0] white (0..84), E[k][1] black (85..169) */
static int nb[N][3];
static unsigned char A[N][N];
static u64 BA[N][NW], BB[N][NW];
static int BE[252][2];        /* Conder edges, 168-vertex labels: white 0..83, black 84..167 */
static int bestE[NE][2];

static u64 rs[2];
static u64 splitmix(u64 *x) {
    u64 z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static void seed_rng(u64 s) { rs[0] = splitmix(&s); rs[1] = splitmix(&s); }
static inline u64 rotl(u64 x, int k) { return (x << k) | (x >> (64 - k)); }
static inline u64 rnd(void) {
    u64 s0 = rs[0], s1 = rs[1];
    u64 r = s0 + s1;
    s1 ^= s0;
    rs[0] = rotl(s0, 55) ^ s1 ^ (s1 << 14);
    rs[1] = rotl(s1, 36);
    return r;
}
static inline double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int n) { return (int)((rnd() >> 1) % (u64)n); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void build_adj(void) {
    int deg[N];
    memset(deg, 0, sizeof deg);
    memset(A, 0, sizeof A);
    for (int k = 0; k < NE; k++) {
        int w = E[k][0], b = E[k][1];
        if (w < 0 || w >= H || b < H || b >= N) { fprintf(stderr, "bad edge %d %d\n", w, b); exit(1); }
        if (A[w][b]) { fprintf(stderr, "multi-edge %d %d\n", w, b); exit(1); }
        if (deg[w] >= 3 || deg[b] >= 3) { fprintf(stderr, "degree overflow at edge %d\n", k); exit(1); }
        A[w][b] = A[b][w] = 1;
        nb[w][deg[w]++] = b;
        nb[b][deg[b]++] = w;
    }
    for (int v = 0; v < N; v++)
        if (deg[v] != 3) { fprintf(stderr, "deg %d = %d\n", v, deg[v]); exit(1); }
}

/* number of ordered pairs at distance > DIAM */
static int cost_D(void) {
    u64 (*cur)[NW] = BA, (*nxt)[NW] = BB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(cur[v]));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < DIAM; k++) {
        for (int v = 0; v < N; v++) {
            const u64 *c0 = cur[v], *c1 = cur[nb[v][0]], *c2 = cur[nb[v][1]], *c3 = cur[nb[v][2]];
            u64 *o = nxt[v];
            for (int w = 0; w < NW; w++) o[w] = c0[w] | c1[w] | c2[w] | c3[w];
        }
        u64 (*t)[NW] = cur;
        cur = nxt;
        nxt = t;
    }
    int cnt = 0;
    for (int v = 0; v < N; v++) {
        int s = 0;
        for (int w = 0; w < NW; w++) s += __builtin_popcountll(cur[v][w]);
        cnt += N - s;
    }
    return cnt;
}

static void repl(int v, int old, int nw) {
    for (int k = 0; k < 3; k++)
        if (nb[v][k] == old) { nb[v][k] = nw; return; }
    fprintf(stderr, "repl failed at %d\n", v);
    exit(1);
}
/* 2-switch on edges i, j: (w1,b1),(w2,b2) -> (w1,b2),(w2,b1). Applying it again to the same (i,j) undoes it. */
static void do_switch(int i, int j) {
    int w1 = E[i][0], b1 = E[i][1], w2 = E[j][0], b2 = E[j][1];
    A[w1][b1] = A[b1][w1] = 0;
    A[w2][b2] = A[b2][w2] = 0;
    A[w1][b2] = A[b2][w1] = 1;
    A[w2][b1] = A[b1][w2] = 1;
    repl(w1, b1, b2);
    repl(w2, b2, b1);
    repl(b1, w1, w2);
    repl(b2, w2, w1);
    E[i][0] = w1; E[i][1] = b2;
    E[j][0] = w2; E[j][1] = b1;
}
static int can_switch(int i, int j) {
    int w1 = E[i][0], b1 = E[i][1], w2 = E[j][0], b2 = E[j][1];
    if (w1 == w2 || b1 == b2) return 0;
    return !A[w1][b2] && !A[w2][b1];
}

static void load_base(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(1); }
    int n;
    if (fscanf(f, "%d", &n) != 1 || n != 168) { fprintf(stderr, "expected 168 vertices\n"); exit(1); }
    for (int k = 0; k < 252; k++) {
        int a, b;
        if (fscanf(f, "%d %d", &a, &b) != 2) { fprintf(stderr, "short file\n"); exit(1); }
        if (a > b) { int t = a; a = b; b = t; }
        if (!(a < 84 && b >= 84 && b < 168)) { fprintf(stderr, "bad labelling %d %d\n", a, b); exit(1); }
        BE[k][0] = a; BE[k][1] = b;
    }
    fclose(f);
}

/* Conder graph minus edges i, j, plus W=84 (white) adj b1, b2, B; B=169 (black) adj w1, w2, W.
   Black labels of the 168-graph shift by +1 so that blacks are 85..168. */
static void build_splice(int i, int j) {
    int w1 = BE[i][0], b1 = BE[i][1], w2 = BE[j][0], b2 = BE[j][1];
    int idx = 0;
    for (int k = 0; k < 252; k++) {
        if (k == i || k == j) continue;
        E[idx][0] = BE[k][0];
        E[idx][1] = BE[k][1] + 1;
        idx++;
    }
    int W = 84, B = 169;
    E[idx][0] = W; E[idx][1] = b1 + 1; idx++;
    E[idx][0] = W; E[idx][1] = b2 + 1; idx++;
    E[idx][0] = w1; E[idx][1] = B; idx++;
    E[idx][0] = w2; E[idx][1] = B; idx++;
    E[idx][0] = W; E[idx][1] = B; idx++;
    build_adj();
}

static void circ_start(void) {
    int offs[3] = {0, 1, 3}, idx = 0;
    for (int i = 0; i < H; i++)
        for (int o = 0; o < 3; o++) {
            E[idx][0] = i;
            E[idx][1] = H + ((i + offs[o]) % H);
            idx++;
        }
    build_adj();
    for (int t = 0; t < 50000; t++) {
        int i = irand(NE), j = irand(NE);
        if (i != j && can_switch(i, j)) do_switch(i, j);
    }
}

static void write_graph(const char *fn, int EE[][2]) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); exit(1); }
    fprintf(f, "%d\n", N);
    for (int k = 0; k < NE; k++) fprintf(f, "%d %d\n", EE[k][0], EE[k][1]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 10) {
        fprintf(stderr, "usage: %s splice|rand BASE168|- SEED SECS T0 T1 CYCLE OUTDIR TAG\n", argv[0]);
        return 1;
    }
    const char *mode = argv[1], *basefn = argv[2];
    u64 seed = strtoull(argv[3], 0, 10);
    double secs = atof(argv[4]), T0 = atof(argv[5]), T1 = atof(argv[6]);
    long cyc = atol(argv[7]);
    const char *outdir = argv[8], *tag = argv[9];
    seed_rng(seed);
    double t0 = now();

    if (!strcmp(mode, "splice")) {
        load_base(basefn);
        int bi = -1, bj = -1, bc = INT_MAX, nsp = 0, nmin = 0;
        for (int i = 0; i < 252; i++)
            for (int j = i + 1; j < 252; j++) {
                if (BE[i][0] == BE[j][0] || BE[i][1] == BE[j][1]) continue;
                build_splice(i, j);
                int c = cost_D();
                nsp++;
                if (c < bc) { bc = c; bi = i; bj = j; nmin = 1; }
                else if (c == bc) nmin++;
            }
        printf("SPLICE all=%d best_cost=%d (attained by %d splices) t=%.2f\n", nsp, bc, nmin, now() - t0);
        build_splice(bi, bj);
        printf("SPLICE chosen: removed (%d,%d) and (%d,%d)\n", BE[bi][0], BE[bi][1], BE[bj][0], BE[bj][1]);
    } else {
        circ_start();
    }

    int C = cost_D();
    int bestC = C;
    memcpy(bestE, E, sizeof E);
    printf("START cost=%d t=%.2f\n", C, now() - t0);
    fflush(stdout);

    double tstart = now(), lastprint = tstart;
    long it = 0, acc = 0;
    while (C > 0) {
        if ((it & 4095) == 0) {
            double t = now();
            if (t - tstart > secs) break;
            if (t - lastprint > 15) {
                printf("t=%.0f it=%ld C=%d best=%d acc=%.4f\n", t - tstart, it, C, bestC,
                       (double)acc / (double)(it + 1));
                fflush(stdout);
                lastprint = t;
            }
        }
        double T = T0 * pow(T1 / T0, (double)(it % cyc) / (double)cyc);
        int i = irand(NE), j = irand(NE);
        it++;
        if (i == j || !can_switch(i, j)) continue;
        do_switch(i, j);
        int C2 = cost_D();
        int d = C2 - C;
        if (d <= 0 || urand() < exp(-d / T)) {
            C = C2;
            acc++;
            if (C < bestC) { bestC = C; memcpy(bestE, E, sizeof E); }
        } else {
            do_switch(i, j);
        }
    }
    char fn[1024];
    snprintf(fn, sizeof fn, "%s/bisa_%s_best.edges", outdir, tag);
    write_graph(fn, bestE);
    printf("RESULT tag=%s mode=%s seed=%llu best=%d final=%d iters=%ld acc=%.4f secs=%.1f file=%s\n", tag, mode,
           (unsigned long long)seed, bestC, C, it, (double)acc / (double)(it + 1), now() - t0, fn);
    return 0;
}
