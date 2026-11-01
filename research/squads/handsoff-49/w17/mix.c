/* w17 mix.c: mixed-orbit bipartite graphs.
 *
 * G (order N, regular on side A) acts on B = disjoint union of coset spaces G/H_i (|H_i| = h_i).
 * Edge orbit j (j = 0..3) joins A-vertex g to B-vertex (i_j, g s_j H_i) for all g in G, where s_j is a
 * coset representative. Each A-vertex gets degree 4; B-vertex (i, xH_i) gets h_i * (4/h_i) = 4 edges, provided
 * sum_i 1/h_i = 1 (types {1}, {2,2}, {2,4,4}, {4,4,4,4}); orbit i receives c_i = 4/h_i edge orbits.
 * The graph has n = 2N vertices. Vertex ids: A = g (0..N-1); B-orbit i coset c = off_i + c.
 * WLOG the first edge orbit of B-orbit 0 has the identity coset (left multiplication of all s_j is an isomorphism).
 *
 * Cost = number of unordered pairs at distance > D (D = 9 target), computed from one root per G-orbit:
 *   totalFar = N * far(root_A) + sum_i (N/h_i) * far(root_Bi), cost = totalFar / 2.
 *
 * Usage: mix TABLE.bin CFG SECONDS SEED D ITERS T0 T1 [OUT.edges]
 *   TABLE.bin : int32 N, then N*N uint16 (row g: g*h), identity index 0 (tools/groups.py format).
 *   CFG       : first token k (number of B-orbits), then k lines "h e_1 ... e_h" (H_i as element indices, e_1 = 0).
 *   Runs restarts of ITERS annealing steps (geometric cooling T0 -> T1) until SECONDS have passed.
 *   Prints "BEST cost=<far pairs> c=<coset choices>" and "BESTLINE ..." at each new best; writes OUT.edges when
 *   the best cost is 0 (the file is the edge list of the best graph, n = 2N).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define DEG 4
#define NORB_MAX 4

static int N, K;                 /* group order, number of B-orbits */
static uint16_t *mul;            /* mul[g*N+h] = g*h */
static uint16_t *mulT;           /* mulT[h*N+g] = g*h (transpose, so right multiplication by h is contiguous) */
static int h[NORB_MAX];          /* stabilizer orders */
static int M[NORB_MAX];          /* number of cosets N/h */
static int *cid[NORB_MAX];       /* cid[i][x] = coset index of x in G/H_i */
static int *rep[NORB_MAX];       /* rep[i][c] = element of coset c */
static int off[NORB_MAX];        /* vertex offset of B-orbit i */
static int V;                    /* total vertices 2N */
static int E = DEG;              /* edge orbits, equals DEG */
static int oj[DEG];              /* B-orbit of edge orbit j */
static int *adj;                 /* adj[v*DEG + k] */
static int *cnt;
static unsigned *stamp;
static unsigned gen = 0;
static int *queue_;
static int D = 9;
static int *sj;

static uint64_t rng_state = 88172645463325252ULL;
static inline uint64_t rnd64(void) {
    rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state;
}
static inline double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static int bfs_reach(int root) {
    gen++;
    if (gen == 0) { memset(stamp, 0, sizeof(unsigned) * V); gen = 1; }
    int head = 0, tail = 0;
    queue_[tail++] = root; stamp[root] = gen;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        for (; head < end; head++) {
            int v = queue_[head];
            const int *a = adj + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                int w = a[k];
                if (stamp[w] != gen) { stamp[w] = gen; queue_[tail++] = w; }
            }
        }
    }
    return tail;
}

/* returns unordered far pairs; fills adjacency for coset choice c[] */
static long long eval(const int *c, int build_only_check) {
    for (int j = 0; j < E; j++) sj[j] = rep[oj[j]][c[j]];
    for (int v = N; v < V; v++) cnt[v] = 0;
    for (int g = 0; g < N; g++) {
        for (int j = 0; j < E; j++) {
            int i = oj[j];
            int x = mulT[(size_t)sj[j] * N + g];
            int v = off[i] + cid[i][x];
            adj[g * DEG + j] = v;
            if (cnt[v] >= DEG) return -1; /* should never happen */
            adj[v * DEG + cnt[v]++] = g;
        }
    }
    if (build_only_check) {
        for (int v = N; v < V; v++) if (cnt[v] != DEG) return -2;
    }
    long long total = (long long)N * (V - bfs_reach(0));
    for (int i = 0; i < K; i++) {
        total += (long long)M[i] * (V - bfs_reach(off[i]));
    }
    if (total & 1) return -3;
    return total / 2;
}

static void write_edges(const char *path, const int *c) {
    eval(c, 1);
    FILE *f = fopen(path, "w");
    if (!f) { perror("fopen"); return; }
    fprintf(f, "%d\n", V);
    for (int g = 0; g < N; g++)
        for (int j = 0; j < E; j++) fprintf(f, "%d %d\n", g, adj[g * DEG + j]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: mix TABLE.bin CFG SECONDS SEED D ITERS T0 T1 [OUT.edges]\n");
        return 1;
    }
    FILE *tf = fopen(argv[1], "rb");
    if (!tf) { perror("table"); return 1; }
    int32_t n32; if (fread(&n32, 4, 1, tf) != 1) return 1;
    N = n32;
    mul = malloc((size_t)N * N * sizeof(uint16_t));
    if (fread(mul, 2, (size_t)N * N, tf) != (size_t)N * N) { fprintf(stderr, "short table\n"); return 1; }
    fclose(tf);
    mulT = malloc((size_t)N * N * sizeof(uint16_t));
    for (int g = 0; g < N; g++) for (int h2 = 0; h2 < N; h2++) mulT[(size_t)h2 * N + g] = mul[(size_t)g * N + h2];

    FILE *cf = fopen(argv[2], "r");
    if (!cf) { perror("cfg"); return 1; }
    if (fscanf(cf, "%d", &K) != 1 || K < 1 || K > NORB_MAX) { fprintf(stderr, "bad cfg\n"); return 1; }
    double inv_sum_num = 0; /* sum 1/h_i must be 1 */
    int cnt_sum = 0;
    int ok_sum = 1;
    int *elems[NORB_MAX];
    for (int i = 0; i < K; i++) {
        if (fscanf(cf, "%d", &h[i]) != 1 || h[i] < 1) { fprintf(stderr, "bad cfg line\n"); return 1; }
        elems[i] = malloc(sizeof(int) * h[i]);
        for (int t = 0; t < h[i]; t++) if (fscanf(cf, "%d", &elems[i][t]) != 1) { fprintf(stderr, "bad elems\n"); return 1; }
        if (DEG % h[i] != 0) ok_sum = 0;
        else cnt_sum += DEG / h[i];
        inv_sum_num += 1.0 / h[i];
    }
    fclose(cf);
    if (!ok_sum || cnt_sum != DEG || fabs(inv_sum_num - 1.0) > 1e-9) {
        fprintf(stderr, "cfg does not satisfy sum 1/h_i = 1 with h_i | 4\n"); return 1;
    }
    /* edge orbits: orbit i gets DEG/h_i of them */
    {
        int j = 0;
        for (int i = 0; i < K; i++) for (int t = 0; t < DEG / h[i]; t++) oj[j++] = i;
    }
    V = 0;
    for (int i = 0; i < K; i++) {
        M[i] = N / h[i];
    }
    /* vertex offsets: A = [0,N), B-orbit i starts at N + sum_{i'<i} M[i'] */
    {
        int acc = N;
        for (int i = 0; i < K; i++) { off[i] = acc; acc += M[i]; }
        V = acc;
    }
    if (V != 2 * N) { fprintf(stderr, "vertex count %d != 2N\n", V); return 1; }
    for (int i = 0; i < K; i++) {
        cid[i] = malloc(sizeof(int) * N);
        rep[i] = malloc(sizeof(int) * M[i]);
        for (int x = 0; x < N; x++) cid[i][x] = -1;
        int c = 0;
        for (int x = 0; x < N; x++) {
            if (cid[i][x] != -1) continue;
            for (int t = 0; t < h[i]; t++) {
                int y = mul[(size_t)x * N + elems[i][t]];
                if (cid[i][y] != -1) { fprintf(stderr, "H_%d is not a subgroup\n", i); return 1; }
                cid[i][y] = c;
            }
            rep[i][c] = x; c++;
        }
        if (c != M[i]) { fprintf(stderr, "coset count mismatch\n"); return 1; }
    }
    adj = malloc(sizeof(int) * (size_t)V * DEG);
    cnt = malloc(sizeof(int) * V);
    stamp = calloc(V, sizeof(unsigned));
    queue_ = malloc(sizeof(int) * V);
    sj = malloc(sizeof(int) * DEG);

    if (getenv("CVEC")) {  /* evaluate one given coset vector and exit (debug) */
        int cc[DEG]; char *q = getenv("CVEC");
        for (int j = 0; j < E; j++) { cc[j] = (int)strtol(q, &q, 10); if (*q == ',') q++; }
        long long v = eval(cc, 1);
        printf("CVEC cost=%lld\n", v);
        if (argc > 9) write_edges(argv[9], cc);
        return 0;
    }
    double secs = atof(argv[3]);
    rng_state ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rng_state) rng_state = 1;
    for (int t = 0; t < 10; t++) rnd64();
    D = atoi(argv[5]);
    long iters = atol(argv[6]);
    double T0 = atof(argv[7]), T1 = atof(argv[8]);
    const char *outpath = argc > 9 ? argv[9] : NULL;

    int c[DEG], bestc[DEG];
    long long gbest = -1;
    double t0 = now_sec();
    int restarts = 0;
    long long evals = 0;
    do {
        /* random start: c_0 pinned to 0 */
        for (int j = 0; j < E; j++) c[j] = (j == 0) ? 0 : (int)(rnd64() % M[oj[j]]);
        long long cur = eval(c, 0);
        evals++;
        long long rbest = cur; int rbc[DEG]; memcpy(rbc, c, sizeof(c));
        for (long it = 0; it < iters; it++) {
            double frac = iters > 1 ? (double)it / (iters - 1) : 1.0;
            double T = T0 * pow(T1 / T0, frac);
            int j = 1 + (int)(rnd64() % (E - 1));
            int oldc = c[j];
            int newc = (int)(rnd64() % M[oj[j]]);
            if (newc == oldc) continue;
            c[j] = newc;
            long long val = eval(c, 0);
            evals++;
            long long d = val - cur;
            if (d <= 0 || rnd01() < exp(-(double)d / T)) {
                cur = val;
                if (cur < rbest) { rbest = cur; memcpy(rbc, c, sizeof(c)); }
            } else {
                c[j] = oldc;
            }
            if (rbest == 0) break;
            if ((it & 1023) == 1023 && now_sec() - t0 > secs) break;
        }
        restarts++;
        if (gbest < 0 || rbest < gbest) {
            gbest = rbest; memcpy(bestc, rbc, sizeof(c));
            printf("BEST cost=%lld restart=%d time=%.1f c=", gbest, restarts, now_sec() - t0);
            for (int j = 0; j < E; j++) printf("%d%s", bestc[j], j + 1 < E ? "," : "");
            printf("\n");
            fflush(stdout);
            if (gbest == 0 && outpath) { write_edges(outpath, bestc); printf("WROTE %s\n", outpath); }
        }
    } while (now_sec() - t0 < secs && gbest != 0);
    printf("FINAL cost=%lld restarts=%d evals=%lld time=%.1f N=%d n=%d\n", gbest, restarts, evals, now_sec() - t0, N, V);
    return 0;
}
