/* mwis_bb.c (card c6, squad d16D7_r3): exact maximum-weight independent set by branch and bound.
 *
 * Independent sets of G are the cliques of H = complement(G). Vertices are relabelled (weight descending, then
 * G-degree ascending). At each node the candidate set is coloured greedily in H; a colour class is a clique of G,
 * so a clique of H (an independent set of G) meets each class at most once, and the weighted colouring bound of a
 * prefix of the colour order is the sum of the class maxima up to its class. Branching goes from the last position
 * downwards (BBMC style): branch k covers the sets inside positions 0..k that contain position k, and the node is
 * pruned when cw + cum[k] <= best (cum is nondecreasing, so all smaller k are pruned too).
 * The incumbent starts from INIT (an independent set, checked). Bitsets: up to 1024 vertices.
 *
 * usage: mwis_bb GRAPH INIT OUT CPU_SECONDS [ORDER]
 *   GRAPH: "n" then per vertex "w deg nbr1 ... nbr_deg"
 *   INIT : independent set (quotient ids, one per line) or "-"
 *   OUT  : best set so far (quotient ids, one per line), rewritten (atomic rename) at every improvement
 * At the end: stdout "RESULT best=W status=COMPLETE|TIMEOUT bound=U nodes=N cpu=T top=k/m". On TIMEOUT, U is an upper
 * bound on the optimum: the maximum over the open nodes on the stack of (cw + colour bound of the unexplored prefix).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXW 16
static int n, W;
static long long *wt;
static int *orig;
static uint64_t (*NH)[MAXW];
static int **ord;
static long long **cum;
static uint64_t (*Pset)[MAXW];
static int *clq, *kcur, *mcount;
static long long *cwd;
static long long best;
static int bestN;
static int *bestSet;
static const char *outf;
static long long nodes;
static double budget, t0, next_log = 30.0;
static int aborted;
static long long frontier;
static int m0;

static double cpu_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void write_sol(const char *of, const int *S, int k) {
    char tmp[1024];
    snprintf(tmp, sizeof tmp, "%s.tmp", of);
    FILE *o = fopen(tmp, "w");
    if (!o) { perror(tmp); exit(4); }
    for (int i = 0; i < k; i++) fprintf(o, "%d\n", S[i]);
    fclose(o);
    rename(tmp, of);
}

static void record(int size) {
    bestN = size;
    for (int i = 0; i < size; i++) bestSet[i] = orig[clq[i]];
    write_sol(outf, bestSet, bestN);
    fprintf(stderr, "improved best=%lld size=%d nodes=%lld t=%.1f\n", best, bestN, nodes, cpu_now() - t0);
}

/* greedy colouring of P = Pset[d] in H; fills ord[d] (positions) and cum[d] (prefix bounds); returns m */
static int colour(int d) {
    uint64_t U[MAXW], Q[MAXW];
    int m = 0;
    long long cumsum = 0;
    memcpy(U, Pset[d], sizeof(uint64_t) * W);
    for (;;) {
        int any = 0;
        for (int j = 0; j < W; j++) if (U[j]) { any = 1; break; }
        if (!any) break;
        memcpy(Q, U, sizeof(uint64_t) * W);
        int start = m;
        long long cmax = 0;
        for (;;) {
            int j = 0;
            while (j < W && Q[j] == 0) j++;
            if (j == W) break;
            int b = __builtin_ctzll(Q[j]);
            int v = j * 64 + b;
            U[j] &= ~(1ULL << b);
            Q[j] &= ~(1ULL << b);
            for (int t = 0; t < W; t++) Q[t] &= ~NH[v][t];   /* keep the class independent in H */
            ord[d][m++] = v;
            if (wt[v] > cmax) cmax = wt[v];
        }
        cumsum += cmax;
        for (int k = start; k < m; k++) cum[d][k] = cumsum;
    }
    return m;
}

static void expand(int d) {
    int m = colour(d);
    mcount[d] = m;
    if (d == 0) m0 = m;
    for (int k = m - 1; k >= 0; k--) {
        if (cwd[d] + cum[d][k] <= best) return;
        kcur[d] = k;
        if ((++nodes & 0x3FFF) == 0) {
            double el = cpu_now() - t0;
            if (el >= budget) {
                aborted = 1;
                frontier = 0;
                for (int e = 0; e <= d; e++) {
                    long long u = cwd[e] + cum[e][kcur[e]];
                    if (u > frontier) frontier = u;
                }
                return;
            }
            if (el >= next_log) {
                next_log += 30.0;
                fprintf(stderr, "t=%.0f best=%lld nodes=%lld depth=%d top=%d/%d\n", el, best, nodes, d, kcur[0], m0);
            }
        }
        int v = ord[d][k];
        clq[d] = v;
        long long nw = cwd[d] + wt[v];
        if (nw > best) { best = nw; record(d + 1); }
        int nonempty = 0;
        for (int j = 0; j < W; j++) {
            Pset[d + 1][j] = Pset[d][j] & NH[v][j];
            nonempty |= (Pset[d + 1][j] != 0);
        }
        if (nonempty) {
            cwd[d + 1] = nw;
            expand(d + 1);
            if (aborted) return;
        }
        Pset[d][v >> 6] &= ~(1ULL << (v & 63));
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: mwis_bb GRAPH INIT OUT CPU_SECONDS [ORDER]\n"); return 1; }
    budget = atof(argv[4]);
    int rev = argc > 5 ? atoi(argv[5]) : 0;
    outf = argv[3];
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror(argv[1]); return 1; }
    int N;
    if (fscanf(f, "%d", &N) != 1) return 1;
    if (N > 64 * MAXW) { fprintf(stderr, "too many vertices\n"); return 1; }
    long long *w0 = malloc(sizeof(long long) * N);
    int *deg0 = malloc(sizeof(int) * N);
    int **nb0 = malloc(sizeof(int *) * N);
    for (int i = 0; i < N; i++) {
        int wi, di;
        if (fscanf(f, "%d %d", &wi, &di) != 2) return 1;
        w0[i] = wi; deg0[i] = di;
        nb0[i] = malloc(sizeof(int) * (di + 1));
        for (int k = 0; k < di; k++) if (fscanf(f, "%d", &nb0[i][k]) != 1) return 1;
    }
    fclose(f);
    n = N;
    W = (n + 63) / 64;
    /* adjacency bitsets in original ids */
    uint64_t (*AG)[MAXW] = calloc(n, sizeof(*AG));
    for (int i = 0; i < n; i++)
        for (int k = 0; k < deg0[i]; k++) { int u = nb0[i][k]; AG[i][u >> 6] |= 1ULL << (u & 63); AG[u][i >> 6] |= 1ULL << (i & 63); }
    /* relabel: weight descending, G-degree ascending, index ascending */
    orig = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) orig[i] = i;
    for (int i = 1; i < n; i++) {               /* insertion sort (n is small) */
        int x = orig[i], j = i - 1;
        while (j >= 0) {
            int y = orig[j];
            int before;
            if (!rev)   /* heavy first, then low G-degree first: heavy low-degree vertices are coloured first */
                before = (w0[x] > w0[y]) || (w0[x] == w0[y] && (deg0[x] < deg0[y] || (deg0[x] == deg0[y] && x < y)));
            else        /* reversed: heavy low-degree vertices get the highest colours and are branched first */
                before = (w0[x] < w0[y]) || (w0[x] == w0[y] && (deg0[x] > deg0[y] || (deg0[x] == deg0[y] && x > y)));
            if (!before) break;
            orig[j + 1] = y; j--;
        }
        orig[j + 1] = x;
    }
    int *newid = malloc(sizeof(int) * n);
    for (int r = 0; r < n; r++) newid[orig[r]] = r;
    wt = malloc(sizeof(long long) * n);
    for (int r = 0; r < n; r++) wt[r] = w0[orig[r]];
    NH = calloc(n, sizeof(*NH));
    for (int r = 0; r < n; r++) {
        int a = orig[r];
        for (int s = 0; s < n; s++) {
            int b = orig[s];
            if (s == r) continue;
            if (!((AG[a][b >> 6] >> (b & 63)) & 1ULL)) NH[r][s >> 6] |= 1ULL << (s & 63);
        }
    }
    /* incumbent */
    bestSet = malloc(sizeof(int) * n);
    best = 0; bestN = 0;
    if (strcmp(argv[2], "-") != 0) {
        FILE *g = fopen(argv[2], "r");
        if (!g) { perror(argv[2]); return 1; }
        int *in = calloc(n, sizeof(int)), cnt = 0, v;
        while (fscanf(g, "%d", &v) == 1) {
            if (v < 0 || v >= n || in[v]) { fprintf(stderr, "bad init\n"); return 1; }
            in[v] = 1; cnt++;
        }
        fclose(g);
        for (int v1 = 0; v1 < n; v1++) if (in[v1])
            for (int v2 = v1 + 1; v2 < n; v2++) if (in[v2] && ((AG[v1][v2 >> 6] >> (v2 & 63)) & 1ULL)) {
                fprintf(stderr, "init not independent: %d %d\n", v1, v2); return 1;
            }
        int k = 0;
        for (int v1 = 0; v1 < n; v1++) if (in[v1]) { bestSet[k++] = v1; best += w0[v1]; }
        bestN = k;
        free(in);
    }
    write_sol(outf, bestSet, bestN);
    fprintf(stderr, "init best=%lld size=%d\n", best, bestN);
    /* search state */
    ord = malloc(sizeof(int *) * (n + 2)); cum = malloc(sizeof(long long *) * (n + 2));
    for (int d = 0; d < n + 2; d++) { ord[d] = malloc(sizeof(int) * n); cum[d] = malloc(sizeof(long long) * n); }
    Pset = calloc(n + 2, sizeof(*Pset));
    clq = malloc(sizeof(int) * (n + 2)); kcur = malloc(sizeof(int) * (n + 2)); mcount = malloc(sizeof(int) * (n + 2));
    cwd = malloc(sizeof(long long) * (n + 2));
    for (int r = 0; r < n; r++) Pset[0][r >> 6] |= 1ULL << (r & 63);
    cwd[0] = 0;
    t0 = cpu_now();
    /* the root colour bound before the search (for the log) */
    expand(0);
    double el = cpu_now() - t0;
    long long U = aborted ? (frontier > best ? frontier : best) : best;
    if (aborted) {
        printf("RESULT best=%lld status=TIMEOUT bound=%lld nodes=%lld cpu=%.1f top=%d/%d\n",
               best, U, nodes, el, kcur[0], m0);
    } else {
        printf("RESULT best=%lld status=COMPLETE bound=%lld nodes=%lld cpu=%.1f top=%d/%d\n",
               best, best, nodes, el, m0, m0);
    }
    return 0;
}
