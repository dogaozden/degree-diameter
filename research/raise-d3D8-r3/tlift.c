/* tlift.c: exhaustive voltage lifts over ANY finite group given by its multiplication table.

   Lift of a bipartite cubic base B (k vertices, white = colour 0 in a BFS 2-colouring from vertex 0) with
   voltages in G (|G| = N):  vertices (u,g) = u*N + g;  for every base edge e = (x white, y black), voltage a_e:
       (x,g) ~ (y, a_e g).
   Right multiplication is an automorphism, so diam = max over base vertices u of ecc((u,e)).
   Gauge: edges of a BFS spanning tree of B get the identity; the other ("free") edges range over all of G.
   Parallel edges must carry distinct voltages (else the lift is not simple); such assignments are skipped.

   Usage:  tlift GROUPFILE BASEFILE D OUTDIR SHARD NSHARDS [ONLY_N|-1 [REPSFILE]]
     REPSFILE (optional): lines "R n i count codes...": Aut(G)-orbit representatives; the first free voltage ranges over them only (valid: automorphisms of G act on all voltages at once).
     GROUPFILE: "G n i N" then N lines of N codes (table[a][b] = code of a*b; identity code 0).
     BASEFILE : "k E" then E lines "x y".
     Groups are split across shards by index (group index % NSHARDS == SHARD).  Every solution found is written to
     OUTDIR/sol_n<n>_g<i>_k<k>_<seq>.txt with the voltage of each base edge (code), and reported on stdout.
     Prints one line per group: "RES n i N k free cands found".  cands = number of assignments tested.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 512
#define MAXK 16
#define MAXE 64
#ifndef NEAR
#define NEAR 2
#endif

static int N, K, E, D;
static int *M;            /* mult table, N*N */
static int inv_[MAXN];
static int ex[MAXE], ey[MAXE];   /* base edges, ex white, ey black */
static int tree[MAXE];          /* 1 if spanning tree edge */
static int freeidx[MAXE], nfree;
static int volt[MAXE];
static int adj[MAXK * MAXN][3];
static int cnt[MAXK * MAXN];
static int seen[MAXK * MAXN], gen = 0;
static int q[MAXK * MAXN];

static int read_group(FILE *f, int *n_out, int *i_out) {
    char tag[4];
    int n, i, N_;
    if (fscanf(f, "%3s %d %d %d", tag, &n, &i, &N_) != 4) return 0;
    if (tag[0] != 'G') { fprintf(stderr, "bad group header\n"); exit(2); }
    N = N_;
    if (N > MAXN) { fprintf(stderr, "N too big %d\n", N); exit(2); }
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++)
            if (fscanf(f, "%d", &M[a * N + b]) != 1) { fprintf(stderr, "short table\n"); exit(2); }
    for (int a = 0; a < N; a++)
        for (int b = 0; b < N; b++)
            if (M[a * N + b] == 0) inv_[a] = b;
    *n_out = n; *i_out = i;
    return 1;
}

static int base_setup(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(2); }
    if (fscanf(f, "%d %d", &K, &E) != 2) exit(2);
    for (int e = 0; e < E; e++)
        if (fscanf(f, "%d %d", &ex[e], &ey[e]) != 2) exit(2);
    fclose(f);
    /* 2-colour by BFS from 0; spanning tree = BFS tree */
    int col[MAXK], vis[MAXK];
    for (int u = 0; u < K; u++) { col[u] = -1; vis[u] = 0; }
    for (int e = 0; e < E; e++) tree[e] = 0;
    col[0] = 0; vis[0] = 1;
    int changed = 1;
    /* BFS over edges */
    int qq[MAXK], h = 0, t = 0; qq[t++] = 0;
    while (h < t) {
        int u = qq[h++];
        for (int e = 0; e < E; e++) {
            int w = -1;
            if (ex[e] == u) w = ey[e];
            else if (ey[e] == u) w = ex[e];
            else continue;
            if (!vis[w]) {
                vis[w] = 1; col[w] = 1 - col[u]; tree[e] = 1; qq[t++] = w;
            }
        }
    }
    (void)changed;
    for (int u = 0; u < K; u++) if (!vis[u]) { fprintf(stderr, "base disconnected\n"); exit(2); }
    /* orient: x must be white (colour 0) */
    for (int e = 0; e < E; e++) {
        if (col[ex[e]] == 1) { int tmp = ex[e]; ex[e] = ey[e]; ey[e] = tmp; }
        if (col[ex[e]] != 0 || col[ey[e]] != 1) { fprintf(stderr, "base not bipartite\n"); exit(2); }
    }
    nfree = 0;
    for (int e = 0; e < E; e++) if (!tree[e]) freeidx[nfree++] = e;
    return 1;
}

/* BFS from source s: returns 1 iff every lift vertex is within D */
static int ecc_reached(int s) {
    gen++;
    int head = 0, tail = 1;
    q[0] = s; seen[s] = gen;
    for (int d = 0; d < D; d++) {       /* after d+1 rounds, q[0..tail) = ball of radius d+1 */
        int end = tail;
        if (head == end) break;
        for (; head < end; head++) {
            int v = q[head];
            for (int j = 0; j < 3; j++) {
                int w = adj[v][j];
                if (seen[w] != gen) { seen[w] = gen; q[tail++] = w; }
            }
        }
    }
    return tail;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: tlift GROUPFILE BASEFILE D OUTDIR SHARD NSHARDS [ONLY_N]\n"); return 2; }
    const char *gpath = argv[1], *bpath = argv[2];
    D = atoi(argv[3]);
    const char *outdir = argv[4];
    int shard = atoi(argv[5]), nshards = atoi(argv[6]);
    int only_n = argc > 7 ? atoi(argv[7]) : -1;
    const char *rpath = argc > 8 ? argv[8] : NULL;
    FILE *nearfile = getenv("NEARFILE") ? fopen(getenv("NEARFILE"), "a") : NULL;
    static int repn[4096], repi[4096], repc[4096], repv[4096][MAXN];
    int nrep = 0;
    if (rpath) {
        FILE *rf = fopen(rpath, "r");
        if (!rf) { perror(rpath); return 2; }
        char tg[4];
        while (fscanf(rf, "%3s %d %d %d", tg, &repn[nrep], &repi[nrep], &repc[nrep]) == 4) {
            for (int j = 0; j < repc[nrep]; j++) fscanf(rf, "%d", &repv[nrep][j]);
            nrep++;
        }
        fclose(rf);
    }
    M = malloc(sizeof(int) * MAXN * MAXN);
    base_setup(bpath);
    FILE *f = fopen(gpath, "r");
    if (!f) { perror(gpath); return 2; }
    int gi = 0;
    int n_, i_;
    int seq = 0;
    while (read_group(f, &n_, &i_)) {
        int idx = gi++;
        if (idx % nshards != shard) continue;
        if (only_n >= 0 && n_ != only_n) continue;
        int nv = K * N;
        if (nv > MAXK * MAXN) { fprintf(stderr, "too big\n"); return 2; }
        /* odometer over free voltages */
        int dig[MAXE];
        int dom0 = N, *reps0 = NULL;
        for (int r = 0; r < nrep; r++)
            if (repn[r] == n_ && repi[r] == i_) { dom0 = repc[r]; reps0 = repv[r]; }
        for (int j = 0; j < nfree; j++) dig[j] = 0;
        for (int e = 0; e < E; e++) volt[e] = 0;
        long long cands = 0, found = 0, nearcount = 0;
        int bestcost = 1 << 30;
        int done = 0;
        while (!done) {
            cands++;
            for (int j = 0; j < nfree; j++) volt[freeidx[j]] = dig[j];
            if (reps0) volt[freeidx[0]] = reps0[dig[0]];
            /* simplicity: parallel edges (same x,y) need distinct voltages */
            int simple = 1;
            for (int e = 0; e < E && simple; e++)
                for (int e2 = e + 1; e2 < E; e2++)
                    if (ex[e] == ex[e2] && ey[e] == ey[e2] && volt[e] == volt[e2]) { simple = 0; break; }
            if (simple) {
                for (int v = 0; v < nv; v++) cnt[v] = 0;
                for (int e = 0; e < E; e++) {
                    int x = ex[e], y = ey[e], a = volt[e], ia = inv_[a];
                    for (int g = 0; g < N; g++) {
                        int vx = x * N + g, vy = y * N + M[a * N + g];
                        adj[vx][cnt[vx]++] = vy;
                        int hy = y * N + g, wx = x * N + M[ia * N + g];
                        adj[hy][cnt[hy]++] = wx;
                    }
                }
                int ok = 1, cost = 0;
                for (int u = 0; u < K && ok; u++) {
                    int r = ecc_reached(u * N);
                    if (r < nv) { ok = 0; cost = nv - r; }
                }
                if (!ok && cost <= NEAR) {
                    nearcount++;
                    if (cost < bestcost) bestcost = cost;
                    if (nearfile) {
                        fprintf(nearfile, "NEAR n %d g %d N %d k %d cost %d volt", n_, i_, N, K, cost);
                        for (int e = 0; e < E; e++) fprintf(nearfile, " %d", volt[e]);
                        fprintf(nearfile, "\n");
                    }
                }
                if (ok) {
                    found++;
                    seq++;
                    char path[1024];
                    snprintf(path, sizeof path, "%s/sol_n%d_g%d_k%d_%d.txt", outdir, n_, i_, K, seq);
                    FILE *o = fopen(path, "w");
                    if (o) {
                        fprintf(o, "# tlift solution: group G %d %d N %d, base k %d E %d, D %d\n", n_, i_, N, K, E, D);
                        fprintf(o, "k %d E %d\n", K, E);
                        for (int e = 0; e < E; e++) fprintf(o, "%d %d %d\n", ex[e], ey[e], volt[e]);
                        fclose(o);
                    }
                    printf("FOUND n %d g %d N %d k %d file %s\n", n_, i_, N, K, path);
                    fflush(stdout);
                }
            }
            /* advance odometer */
            int j = 0;
            while (j < nfree) {
                dig[j]++;
                if (dig[j] < (j == 0 ? dom0 : N)) break;
                dig[j] = 0; j++;
            }
            if (j == nfree) done = 1;
        }
        printf("RES n %d g %d N %d k %d free %d cands %lld found %lld near%d %lld best %d\n", n_, i_, N, K, nfree, cands, found, NEAR, nearcount, bestcost);
        fflush(stdout);
    }
    fclose(f);
    return 0;
}
