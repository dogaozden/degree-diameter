/* rsolve (worker c3, squad handsoff-37): randomized restarts of the exact Z_p voltage-lift tree search.
   Usage: rsolve p k D seed budget0 tlim_sec [maxsol]
     A lift: cubic bipartite base on k+k vertices, voltages in Z_p, lifted graph on 2kp vertices, vertex (x,g) = x*p+g,
     base edge a-b with voltage t gives (a,g)~(b,g+t). Solutions of the lift have bipartite diameter <= D (D odd).
   Same tree and pruning as shared/prior/exact_jsearch.c (its header explains the construction and the collision bound:
   collisions(u) <= delta = 2^D - 1 - k p for every base vertex u, checked on every edge insertion). The difference:
   at every node the children are SHUFFLED (they partition the completions, so any order is exhaustive), the search is
   restarted with a Luby sequence of node budgets (budget0 * luby(i)) and a fresh random seed each time. A restart that
   finishes without hitting its budget has searched the whole tree, so "EXHAUSTED" then means no (further) solutions.
   Each solution is lifted, checked for far (unordered pairs at distance > D) by an in-process BFS, and written to
   out/sol_p<p>_k<k>_<idx>_far<far>.edges when far = 0 (or always for far <= 0). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXV 64
#define MAXE 96
#define BIG (1 << 20)

static int p, k, D, L, delta;
static int nv, ne, side_[MAXV], deg_[MAXV], nside[2];
static int adjv[MAXV][3], adje[MAXV][3];
static int ea[MAXE], eb[MAXE], et[MAXE]; /* ea side 0, eb side 1, voltage a->b */
static int anynz;
static uint64_t seen_[MAXV][MAXV][2];   /* [start][end] voltage bitsets, p <= 128 */
static int coll[MAXV];
typedef struct { short u, v, g; char c; } Rec;
static Rec *logbuf; static long lsp, lcap;

typedef struct { short x, g, len; } PW;
static PW pre[4096], suf[4096]; static int npre, nsuf;
static int enew, bad;

static inline int dartv(int x, int j, int *g) { int e = adje[x][j]; *g = (side_[x] == 0) ? et[e] : (p - et[e]) % p; return adjv[x][j]; }
static void gen_pre(int x, int laste, int len, int g, int maxlen) { /* NB walks from tail avoiding enew */
    pre[npre].x = x; pre[npre].g = g; pre[npre].len = len; npre++;
    if (len == maxlen) return;
    for (int j = 0; j < 3 && j < deg_[x]; j++) { int e = adje[x][j]; if (e == laste || e == enew) continue;
        int dg; int y = dartv(x, j, &dg); gen_pre(y, e, len + 1, (g + dg) % p, maxlen); }
}
static void gen_suf(int x, int laste, int len, int g, int maxlen) { /* NB walks from head, first edge != enew */
    suf[nsuf].x = x; suf[nsuf].g = g; suf[nsuf].len = len; nsuf++;
    if (len == maxlen) return;
    for (int j = 0; j < 3 && j < deg_[x]; j++) { int e = adje[x][j]; if (e == laste) continue;
        int dg; int y = dartv(x, j, &dg); gen_suf(y, e, len + 1, (g + dg) % p, maxlen); }
}
static inline void record(int u, int v, int g) {
    uint64_t m = 1ULL << (g & 63); int w = g >> 6;
    Rec r; r.u = u; r.v = v; r.g = g;
    if (seen_[u][v][w] & m) { r.c = 1; coll[u]++; if (coll[u] > delta) bad = 1; }
    else { r.c = 0; seen_[u][v][w] |= m; }
    if (lsp == lcap) { lcap *= 2; logbuf = realloc(logbuf, sizeof(Rec) * lcap); }
    logbuf[lsp++] = r;
}
static void through(int tail, int head, int gt) {
    npre = 0; nsuf = 0;
    gen_pre(tail, enew, 0, 0, L - 1);
    gen_suf(head, enew, 0, 0, L - 1);
    static int sb[16][4096], sn[16];
    for (int l = 0; l < L; l++) sn[l] = 0;
    for (int j = 0; j < nsuf; j++) { int l = suf[j].len; sb[l][sn[l]++] = j; }
    for (int i = 0; i < npre && !bad; i++) {
        int u = pre[i].x, g1 = (p - pre[i].g + gt) % p, li = pre[i].len;
        for (int l = (li & 1) ? 0 : 1; li + 1 + l <= L; l += 2)
            for (int jj = 0; jj < sn[l]; jj++) { int j = sb[l][jj];
                record(u, suf[j].x, (g1 + suf[j].g) % p);
                if (bad) return; }
    }
}
static void undo_to(long mark) {
    while (lsp > mark) { Rec r = logbuf[--lsp];
        if (r.c) coll[r.u]--; else seen_[r.u][r.v][r.g >> 6] &= ~(1ULL << (r.g & 63)); }
}
static void add_edge(int a, int b, int t) {
    int e = ne++; ea[e] = a; eb[e] = b; et[e] = t;
    adjv[a][deg_[a]] = b; adje[a][deg_[a]++] = e; adjv[b][deg_[b]] = a; adje[b][deg_[b]++] = e;
}
static void del_edge(void) { int e = --ne; deg_[ea[e]]--; deg_[eb[e]]--; }
static int check_new_edge(void) { /* walks through the newest edge; 0 if some u has collisions > delta */
    enew = ne - 1; bad = 0;
    int a = ea[enew], b = eb[enew], t = et[enew];
    through(a, b, t);
    if (!bad) through(b, a, (p - t) % p);
    return !bad;
}
/* cheap test of adding edge x-y with voltage tx seen from x (no state change): returns stored voltage or -1 */
static inline int cheap_ok(int x, int y, int tx) {
    int s = side_[x]; int vt = (s == 0) ? tx : (p - tx) % p;
    if (!anynz && vt > 1) return -1;
    for (int j = 0; j < deg_[x]; j++) if (adjv[x][j] == y && et[adje[x][j]] == vt) return -1;
    return vt;
}

/* ---- random number generation ---- */
static uint64_t rng = 88172645463325252ULL;
static inline uint32_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (uint32_t)(rng >> 11); }

/* ---- statistics ---- */
static long nodes, budget, nsol, maxsol = 1000000, sols_written = 0; static int aborted;
static int maxne = 0; static long hist_ne[MAXE + 1];
static int nv_full;

/* ---- lift + independent far count (BFS from every vertex of the lifted graph) ---- */
static long lift_far(int *out_n, int *ledges_a, int *ledges_b, int *nedges) {
    int N = 2 * k * p; *out_n = N; int E = 0;
    static int A[4096], B[4096];
    for (int e = 0; e < ne; e++) for (int g = 0; g < p; g++) {
        A[E] = ea[e] * p + g; B[E] = eb[e] * p + (g + et[e]) % p; E++; }
    *nedges = E;
    static int adjL[MAXV * 8][3]; static int dgL[MAXV * 8];
    /* lifted graph is cubic, N <= 2*MAXV*... keep small */
    if (N > MAXV * 8) return -1;
    memset(dgL, 0, sizeof dgL);
    for (int i = 0; i < E; i++) { adjL[A[i]][dgL[A[i]]++] = B[i]; adjL[B[i]][dgL[B[i]]++] = A[i]; }
    static int dist[MAXV * 8], q[MAXV * 8];
    long far2 = 0;
    for (int s = 0; s < N; s++) {
        for (int i = 0; i < N; i++) dist[i] = -1;
        int h = 0, t = 0; q[t++] = s; dist[s] = 0;
        while (h < t) { int x = q[h++]; for (int j = 0; j < dgL[x]; j++) { int y = adjL[x][j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        for (int i = 0; i < N; i++) if (i != s && (dist[i] < 0 || dist[i] > D)) far2++;
    }
    return far2 / 2;
}

static long nsolsave = 0;
static void report(void) {
    nsol++;
    int N, E; long far = lift_far(&N, NULL, NULL, &E);
    printf("SOL idx=%ld far=%ld nodes=%ld base:", nsol, far, nodes);
    for (int e = 0; e < ne; e++) printf(" %d-%d:%d", ea[e], eb[e], et[e]);
    printf("\n"); fflush(stdout);
    if ((far == 0 || far < 0) && sols_written < 30) {
        char fn[256]; sprintf(fn, "out/sol_p%d_k%d_%ld_far%ld.edges", p, k, nsol, far);
        FILE *f = fopen(fn, "w");
        if (f) { fprintf(f, "%d\n", N); for (int e = 0; e < ne; e++) for (int g = 0; g < p; g++)
                     fprintf(f, "%d %d\n", ea[e] * p + g, eb[e] * p + (g + et[e]) % p); fclose(f); sols_written++; }
    }
    if (nsol >= maxsol) aborted = 1;
}
static void next_vertex(void);
static void fill_node(int x, int minkey);
static void par_node(int x, int y, int lastt);

typedef struct { int type, y, t; } Ch; /* type 0: existing y voltage t; 1: new vertex; 2: stop parallels; 3: parallel t */
static void shuffle(Ch *c, int n) { for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); Ch tmp = c[i]; c[i] = c[j]; c[j] = tmp; } }

static void next_vertex(void) {
    int x = -1; for (int i = 0; i < nv; i++) if (deg_[i] < 3) { x = i; break; }
    if (x < 0) { if (nv == 2 * k) report(); return; }
    fill_node(x, 0);
}

static void fill_node(int x, int minkey) {
    if (aborted) return;
    nodes++; if (nodes > budget) { aborted = 1; return; }
    if (ne > maxne) maxne = ne; hist_ne[ne]++;
    if (deg_[x] == 3) { next_vertex(); return; }
    int s = side_[x], o = 1 - s;
    Ch c[160]; int nc = 0;
    if (minkey < BIG) for (int y = x + 1; y < nv; y++) {
        if (side_[y] != o || deg_[y] >= 3) continue;
        for (int t = 0; t < p; t++) {
            int key = y * p + t; if (key < minkey) continue;
            if (cheap_ok(x, y, t) < 0) continue;
            c[nc].type = 0; c[nc].y = y; c[nc].t = t; nc++;
        }
    }
    if (nv < 2 * k && nside[o] < k) { c[nc].type = 1; c[nc].y = 0; c[nc].t = 0; nc++; }
    shuffle(c, nc);
    for (int i = 0; i < nc && !aborted; i++) {
        if (c[i].type == 0) {
            int y = c[i].y, t = c[i].t;
            int was = anynz; int vt = cheap_ok(x, y, t); if (vt < 0) continue;
            add_edge(s == 0 ? x : y, s == 0 ? y : x, vt);
            if (vt) anynz = 1;
            long mark = lsp;
            if (check_new_edge()) fill_node(x, y * p + t + 1);
            undo_to(mark); del_edge(); anynz = was;
        } else {
            int y = nv++; side_[y] = o; deg_[y] = 0; nside[o]++;
            seen_[y][y][0] |= 1ULL;
            add_edge(s == 0 ? x : y, s == 0 ? y : x, 0);
            long mark = lsp;
            if (check_new_edge()) par_node(x, y, 0);
            undo_to(mark); del_edge();
            seen_[y][y][0] &= ~1ULL; nv--; nside[o]--;
        }
    }
}

/* after a new vertex y: stop adding parallel edges x-y (rest of x's edges go to new vertices), or add a parallel
   edge with voltage t > lastt */
static void par_node(int x, int y, int lastt) {
    if (aborted) return;
    Ch c[160]; int nc = 0;
    c[nc].type = 2; nc++;
    if (deg_[x] < 3 && deg_[y] < 3) for (int t = lastt + 1; t < p; t++) { c[nc].type = 3; c[nc].t = t; c[nc].y = y; nc++; }
    shuffle(c, nc);
    for (int i = 0; i < nc && !aborted; i++) {
        if (c[i].type == 2) { fill_node(x, BIG); }
        else {
            int t = c[i].t;
            int was = anynz; int vt = cheap_ok(x, y, t); if (vt < 0) continue;
            add_edge(side_[x] == 0 ? x : y, side_[x] == 0 ? y : x, vt);
            if (vt) anynz = 1;
            long mark = lsp;
            if (check_new_edge()) par_node(x, y, t);
            undo_to(mark); del_edge(); anynz = was;
        }
    }
}

static void reset_state(void) {
    memset(seen_, 0, sizeof seen_); memset(coll, 0, sizeof coll); lsp = 0;
    nv = 1; side_[0] = 0; deg_[0] = 0; nside[0] = 1; nside[1] = 0; ne = 0; anynz = 0;
    seen_[0][0][0] |= 1ULL;
}

static long luby(long i) { /* 1,1,2,1,1,2,4,... */
    for (;;) {
        long kk = 1; while ((1L << kk) - 1 < i) kk++;
        if (i == (1L << kk) - 1) return 1L << (kk - 1);
        i = i - (1L << (kk - 1)) + 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: rsolve p k D seed budget0 tlim_sec [maxsol]\n"); return 2; }
    p = atoi(argv[1]); k = atoi(argv[2]); D = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10); long budget0 = atol(argv[5]); double tlim = atof(argv[6]);
    if (argc > 7) maxsol = atol(argv[7]);
    if (D % 2 == 0 || p > 128 || 2 * k > MAXV / 2) { fprintf(stderr, "need D odd, p <= 128, 2k <= 32\n"); return 2; }
    L = D - 1; delta = (1 << D) - 1 - k * p;
    if (delta < 0) { printf("DONE delta<0\n"); return 0; }
    rng ^= seed * 0x9E3779B97F4A7C15ULL + 12345; for (int i = 0; i < 10; i++) rnd();
    lcap = 1 << 20; logbuf = malloc(sizeof(Rec) * lcap);
    clock_t c0 = clock();
    long total_nodes = 0; long restarts = 0; int exhausted = 0;
    for (long r = 1;; r++) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el > tlim || nsol >= maxsol) break;
        long bud = budget0 * luby(r);
        reset_state(); nodes = 0; budget = bud; aborted = 0;
        fill_node(0, 0);
        total_nodes += nodes; restarts++;
        if (!aborted) { exhausted = 1; break; }
        if (r % 20 == 0) fprintf(stderr, "restart %ld t=%.1fs nodes=%ld sols=%ld maxne=%d\n", r, el, total_nodes, nsol, maxne);
    }
    double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
    printf("%s p=%d k=%d D=%d n=%d delta=%d seed=%llu budget0=%ld restarts=%ld nodes=%ld sols=%ld time=%.1f maxne=%d (3k=%d)\n",
           exhausted ? "EXHAUSTED" : "STOP", p, k, D, 2 * k * p, delta, (unsigned long long)seed, budget0, restarts, total_nodes, nsol, el, maxne, 3 * k);
    printf("HIST");
    for (int e = 0; e <= 3 * k; e++) printf(" %ld", hist_ne[e]);
    printf("\n");
    return 0;
}
