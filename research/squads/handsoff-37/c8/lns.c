/* c8 LNS: ruin-and-recreate by exhaustive stub re-matching on cubic bipartite graphs, target (3,7).
   Build: gcc -O3 -march=native -o lns lns.c -lm
   Usage: lns n seed seconds s T pb R outprefix [init.edges]
     n        even, A = 0..n/2-1, B = n/2..n-1 (ignored if init file given; then n comes from the file)
     s        number of edges removed per move (s! re-matchings enumerated)
     T        Boltzmann temperature in far-pair units (0 = greedy with random ties)
     pb       probability of choosing the centre among vertices that have far pairs
     R        max ball radius for the region (region radius uniform in 1..R, grown until s edges)
   [init.edges or - for random] [Tend: geometric cooling of T to Tend over the run]
   Writes outprefix_best.edges whenever the best far improves (and final). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 256
#define MAXS 9
static int n, m;
static int adj[MAXN][3];
static unsigned char M[MAXN][MAXN];
static int stamp[MAXN][MAXN]; static int curstamp = 1;
static uint64_t vis[MAXN], fr[MAXN], nx[MAXN];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int k) { return (int)(rnd() % (uint64_t)k); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* far pairs (unordered, distance > 7 or unreachable). unr[x] = ordered count of vertices unreached from x, if unr != NULL */
static long long far_eval(int *unr) {
    long long total = 0;
    for (int s0 = 0; s0 < n; s0 += 64) {
        int ns = n - s0 < 64 ? n - s0 : 64;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < 7; lev++) {
            memset(nx, 0, n * 8);
            for (int x = 0; x < n; x++) { uint64_t f = fr[x]; if (!f) continue;
                nx[adj[x][0]] |= f; nx[adj[x][1]] |= f; nx[adj[x][2]] |= f; }
            int any = 0;
            for (int y = 0; y < n; y++) { uint64_t z = nx[y] & ~vis[y]; vis[y] |= z; fr[y] = z; any |= (z != 0); }
            if (!any) break;
        }
        for (int y = 0; y < n; y++) total += __builtin_popcountll(vis[y]);
        if (unr) for (int k = 0; k < ns; k++) { int c = 0; for (int y = 0; y < n; y++) c += (vis[y] >> k) & 1; unr[s0 + k] = n - c; }
    }
    return ((long long)n * n - total) / 2;
}

static int slot_of(int x, int y) { for (int t = 0; t < 3; t++) if (adj[x][t] == y) return t; return -1; }

static void build_M(void) {
    memset(M, 0, sizeof M);
    for (int x = 0; x < n; x++) for (int t = 0; t < 3; t++) M[x][adj[x][t]] = 1;
}

static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); exit(1); }
    fprintf(f, "%d\n", n);
    for (int a = 0; a < m; a++) for (int t = 0; t < 3; t++) fprintf(f, "%d %d\n", a, adj[a][t]);
    fclose(f);
}

static void twoswitch_randomize(int iters) {
    for (int it = 0; it < iters; it++) {
        int a = irand(m), t = irand(3), b = adj[a][t];
        int a2 = irand(m), t2 = irand(3), b2 = adj[a2][t2];
        if (a == a2 || b == b2) continue;
        if (M[a][b2] || M[a2][b]) continue;
        adj[a][t] = b2; adj[b][slot_of(b, a)] = a2;
        adj[a2][t2] = b; adj[b2][slot_of(b2, a2)] = a;
        M[a][b] = M[b][a] = 0; M[a2][b2] = M[b2][a2] = 0;
        M[a][b2] = M[b2][a] = 1; M[a2][b] = M[b][a2] = 1;
    }
}

static int load_graph(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int nn; if (fscanf(f, "%d", &nn) != 1) exit(1);
    static int E[4096][2]; int ne = 0, a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { E[ne][0] = a; E[ne][1] = b; ne++; }
    fclose(f);
    int deg[MAXN] = {0}; int nb[MAXN][3];
    for (int i = 0; i < ne; i++) { int x = E[i][0], y = E[i][1];
        if (deg[x] >= 3 || deg[y] >= 3) { fprintf(stderr, "not cubic\n"); exit(1); }
        nb[x][deg[x]++] = y; nb[y][deg[y]++] = x; }
    for (int x = 0; x < nn; x++) if (deg[x] != 3) { fprintf(stderr, "not cubic at %d\n", x); exit(1); }
    /* bipartition by BFS colouring */
    int col[MAXN]; for (int x = 0; x < nn; x++) col[x] = -1;
    int q[MAXN], h = 0, t = 0;
    for (int s = 0; s < nn; s++) if (col[s] < 0) { col[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int k = 0; k < 3; k++) { int y = nb[x][k];
            if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); exit(1); } } } }
    int mp[MAXN], ca = 0, cb = 0, nA = 0;
    for (int x = 0; x < nn; x++) if (col[x] == 0) nA++;
    if (nA * 2 != nn) { fprintf(stderr, "unbalanced sides (%d of %d)\n", nA, nn); exit(1); }
    for (int x = 0; x < nn; x++) mp[x] = col[x] == 0 ? ca++ : nA + cb++;
    n = nn; m = nA;
    for (int x = 0; x < nn; x++) for (int k = 0; k < 3; k++) adj[mp[x]][k] = mp[nb[x][k]];
    build_M();
    return n;
}

static void init_circulant(int nn) {
    n = nn; m = nn / 2;
    int offs[3] = {0, 1, 3};
    for (int a = 0; a < m; a++) for (int k = 0; k < 3; k++) { int b = m + (a + offs[k]) % m; adj[a][k] = b; adj[b][k] = 0; }
    /* fill B slots: B vertex m+j is adjacent to A vertices a with (a+o) % m == j */
    int cnt[MAXN] = {0};
    for (int a = 0; a < m; a++) for (int k = 0; k < 3; k++) { int b = adj[a][k]; adj[b][cnt[b]++] = a; }
    build_M();
}

/* ---- stub re-matching ---- */
static int S;
static int SA[MAXS], SAslot[MAXS], SB[MAXS], SBslot[MAXS];
static int perm[MAXS], used[MAXS];
static unsigned char *pstore; static int *fstore; static long nleaf, capleaf;

static void dfs(int i) {
    if (i == S) {
        for (int t = 0; t < S; t++) { int a = SA[t], b = SB[perm[t]];
            adj[a][SAslot[t]] = b; adj[b][SBslot[perm[t]]] = a; }
        long long f = far_eval(NULL);
        if (nleaf >= capleaf) { fprintf(stderr, "leaf overflow\n"); exit(1); }
        for (int t = 0; t < S; t++) pstore[nleaf * S + t] = (unsigned char)perm[t];
        fstore[nleaf] = (int)f; nleaf++;
        return;
    }
    int a = SA[i];
    for (int j = 0; j < S; j++) {
        if (used[j]) continue;
        int b = SB[j];
        if (M[a][b]) continue;
        M[a][b] = M[b][a] = 1; used[j] = 1; perm[i] = j;
        dfs(i + 1);
        M[a][b] = M[b][a] = 0; used[j] = 0;
    }
}

static long long hist[16];
static double fact_d(int k) { double r = 1; for (int i = 2; i <= k; i++) r *= i; return r; }

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: lns n seed seconds s T pb R outprefix [init.edges]\n"); return 2; }
    int nn = atoi(argv[1]); rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[3]); int s = atoi(argv[4]); double T = atof(argv[5]);
    double pb = atof(argv[6]); int R = atoi(argv[7]); const char *outp = argv[8];
    double Tend = argc >= 11 ? atof(argv[10]) : -1;   /* optional: geometric cooling from T to Tend over the run */
    double T0 = T;
    if (argc >= 10 && strcmp(argv[9], "-") != 0) load_graph(argv[9]); else { init_circulant(nn); twoswitch_randomize(20000 + 50 * nn * nn); }
    if (s > MAXS) s = MAXS;
    capleaf = 1; for (int i = 2; i <= s; i++) capleaf *= i;
    pstore = malloc((size_t)capleaf * s + 16); fstore = malloc(sizeof(int) * (capleaf + 16));
    int *unr = malloc(sizeof(int) * MAXN);
    int *cand_a = malloc(sizeof(int) * 4096), *cand_b = malloc(sizeof(int) * 4096);
    long long cur = far_eval(unr);
    long long best = cur;
    char fn[512]; snprintf(fn, sizeof fn, "%s_best.edges", outp);
    write_graph(fn);
    fprintf(stderr, "init n=%d far=%lld s=%d T=%g pb=%g R=%d\n", n, cur, s, T, pb, R);
    double t0 = now(), tlast = t0; long long moves = 0, leaves = 0, accepted = 0;
    double *w = malloc(sizeof(double) * (capleaf + 16));
    while (now() - t0 < secs) {
        /* choose centre */
        if (Tend > 0 && T0 > 0) T = T0 * pow(Tend / T0, (now() - t0) / secs);
        int v = -1;
        if (urand() < pb) {
            int cnt = 0; for (int x = 0; x < n; x++) if (unr[x] > 0) cnt++;
            if (cnt) { int pick = irand(cnt); for (int x = 0; x < n; x++) if (unr[x] > 0) { if (pick-- == 0) { v = x; break; } } }
        }
        if (v < 0) v = irand(n);
        int rad = 1 + irand(R);
        /* ball of radius rad (BFS), collect edges incident to ball, choose s distinct ones */
        int ball[MAXN], inb[MAXN]; memset(inb, 0, sizeof inb);
        int bh = 0, bt = 0; ball[bt++] = v; inb[v] = 1;
        int dist[MAXN]; dist[v] = 0;
        while (bh < bt) { int x = ball[bh++]; if (dist[x] >= rad) continue;
            for (int k = 0; k < 3; k++) { int y = adj[x][k]; if (!inb[y]) { inb[y] = 1; dist[y] = dist[x] + 1; ball[bt++] = y; } } }
        curstamp++;
        int nc = 0;
        for (int i = 0; i < bt; i++) { int x = ball[i];
            for (int k = 0; k < 3; k++) { int y = adj[x][k]; int a = x < m ? x : y, b = x < m ? y : x;
                if (stamp[a][b] != curstamp) { stamp[a][b] = curstamp; cand_a[nc] = a; cand_b[nc] = b; nc++; } } }
        if (nc < s) continue;
        for (int i = 0; i < s; i++) { int j = i + irand(nc - i); int ta = cand_a[i], tb = cand_b[i];
            cand_a[i] = cand_a[j]; cand_b[i] = cand_b[j]; cand_a[j] = ta; cand_b[j] = tb; }
        /* remove the s chosen edges, record stubs */
        for (int i = 0; i < s; i++) { int a = cand_a[i], b = cand_b[i];
            SA[i] = a; SAslot[i] = slot_of(a, b); SB[i] = b; SBslot[i] = slot_of(b, a);
            M[a][b] = M[b][a] = 0; }
        S = s; memset(used, 0, sizeof used); nleaf = 0;
        dfs(0);
        leaves += nleaf; moves++;
        for (long l = 0; l < nleaf; l++) { int d = fstore[l] - (int)cur + 5; if (d < 0) d = 0; if (d > 15) d = 15; hist[d]++; }
        { int ident = 0; (void)ident; }
        /* Boltzmann choice */
        int fmin = fstore[0]; for (long l = 1; l < nleaf; l++) if (fstore[l] < fmin) fmin = fstore[l];
        long pick = -1;
        if (T <= 0) {
            long cntmin = 0; for (long l = 0; l < nleaf; l++) if (fstore[l] == fmin) cntmin++;
            long r = irand((int)cntmin); for (long l = 0; l < nleaf; l++) if (fstore[l] == fmin) { if (r-- == 0) { pick = l; break; } }
        } else {
            double tot = 0;
            for (long l = 0; l < nleaf; l++) { w[l] = exp(-(fstore[l] - fmin) / T); tot += w[l]; }
            double r = urand() * tot;
            for (long l = 0; l < nleaf; l++) { r -= w[l]; if (r <= 0) { pick = l; break; } }
            if (pick < 0) pick = nleaf - 1;
        }
        /* apply chosen re-matching */
        for (int t = 0; t < S; t++) { int a = SA[t], b = SB[pstore[pick * S + t]];
            adj[a][SAslot[t]] = b; adj[b][SBslot[pstore[pick * S + t]]] = a; M[a][b] = M[b][a] = 1; }
        long long f = fstore[pick];
        if (f != cur) accepted++;
        cur = f;
        far_eval(unr);
        if (cur < best) { best = cur; write_graph(fn);
            fprintf(stderr, "  NEW BEST far=%lld at t=%.1fs move=%lld\n", best, now() - t0, moves); }
        if (now() - tlast > 20) { tlast = now();
            fprintf(stderr, "t=%.0f T=%.3f moves=%lld leaves/s=%.0f cur=%lld best=%lld acc=%lld\n", now() - t0, T, moves,
                    leaves / (now() - t0), cur, best, accepted); }
    }
    fprintf(stderr, "leaf delta hist (delta-5 .. ): "); for (int d = 0; d < 16; d++) fprintf(stderr, "%lld ", hist[d]); fprintf(stderr, "\n");
    fprintf(stderr, "DONE moves=%lld leaves=%lld cur=%lld best=%lld secs=%.0f\n", moves, leaves, cur, best, now() - t0);
    (void)fact_d;
    printf("n=%d best=%lld file=%s\n", n, best, fn);
    return 0;
}
