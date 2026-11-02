/* surgsa.c (w6, handsoff-49): annealing over the CHOICE of removed edges for the 2-vertex surgery.
   Base graph (bipartite, 4-regular, n0 vertices) minus k disjoint edges (u_i in A, v_i in B), plus a in A joined to all v_i
   and b in B joined to all u_i (MODE 4: k=4), or k=3 with the extra edge a-b (MODE 3). Cost = far pairs (D=9).
   usage: surgsa BASE OUT SECONDS SEED MODE T0 T1
   sa.c (base code): simulated annealing on a bipartite graph with max degree DEG, cost = number of unordered
   vertex pairs at distance > D (unreachable pairs included). Moves keep degrees and bipartiteness:
   - targeted shortcut (prob PT): a far pair (s,t) is found by one BFS from a random root s; x = random walk of length
     0..R from s, y = random walk of length 0..R from t, x and y on opposite sides; the 2-switch removes {x,x2},{y,y2}
     and adds {x,y},{x2,y2} (x2, y2 random neighbours).
   - random 2-switch otherwise.
   Acceptance: Metropolis on the far count, implemented as "draw u, threshold = cur - T ln u", with the bit-parallel
   all-pairs BFS aborting as soon as the partial count exceeds the threshold.
   usage: sa IN.edges OUT.edges SECONDS SEED T0 T1 [PT=0.7] [R=2] [D=9]
   Writes OUT.edges whenever the best cost improves; prints a status line every 20 s and a final BEST line. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 8192
#define MAXDEG 8
static int n, D = 9, DEGMAX = 4;
static int adj[MAXN][MAXDEG], deg[MAXN], side[MAXN];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static inline double rnd01(void) { return ((rnd64() >> 11) + 0.5) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int has_edge(int x, int y) { for (int i = 0; i < deg[x]; i++) if (adj[x][i] == y) return 1; return 0; }
static void rep(int x, int old, int nw) {
    for (int i = 0; i < deg[x]; i++) if (adj[x][i] == old) { adj[x][i] = nw; return; }
    fprintf(stderr, "internal error: no edge %d-%d\n", x, old); exit(1);
}
/* remove {p,q},{r,s}; add {p,r},{q,s} */
static void swap_edges(int p, int q, int r, int s) {
    rep(p, q, r); rep(q, p, s); rep(r, s, p); rep(s, r, q);
}

/* ordered far count W = sum over sources of #vertices at distance > D or unreachable; aborts (returns partial) when
   the partial sum exceeds cap. Full value is exact when the return value is <= cap. */
static uint64_t VA[MAXN], FA[MAXN], NA[MAXN];
static long long far_ordered(long long cap) {
    uint64_t *vis = VA, *fr = FA, *nx = NA;
    long long far = 0;
    for (int s0 = 0; s0 < n; s0 += 64) {
        int ns = n - s0 < 64 ? n - s0 : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 1; lev <= D; lev++) {
            int any = 0;
            for (int x = 0; x < n; x++) {
                uint64_t acc = 0;
                for (int i = 0; i < deg[x]; i++) acc |= fr[adj[x][i]];
                acc &= ~vis[x]; nx[x] = acc; any |= (acc != 0);
            }
            if (!any) break;
            for (int x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        for (int x = 0; x < n; x++) far += __builtin_popcountll(full & ~vis[x]);
        if (far > cap) return far;
    }
    return far;
}

/* random vertex at distance > D from s (or -1) */
static int far_partner(int s) {
    static int dist[MAXN], q[MAXN];
    for (int i = 0; i < n; i++) dist[i] = -1;
    dist[s] = 0; int h = 0, t = 0; q[t++] = s;
    while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
    int cnt = 0;
    for (int i = 0; i < n; i++) if (dist[i] < 0 || dist[i] > D) cnt++;
    if (!cnt) return -1;
    int r = rndint(cnt);
    for (int i = 0; i < n; i++) if (dist[i] < 0 || dist[i] > D) { if (r == 0) return i; r--; }
    return -1;
}

static int walk(int v, int L) { for (int i = 0; i < L; i++) v = adj[v][rndint(deg[v])]; return v; }

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w"); if (!f) return;
    long m = 0; for (int x = 0; x < n; x++) m += deg[x];
    fprintf(f, "%d\n", n);
    for (int x = 0; x < n; x++) for (int i = 0; i < deg[x]; i++) if (side[x] == 0 && adj[x][i] > x) {} /* placeholder */
    for (int x = 0; x < n; x++) if (side[x] == 0) for (int i = 0; i < deg[x]; i++) fprintf(f, "%d %d\n", x, adj[x][i]);
    fclose(f);
}


static int n0, m0, EU0[MAXN * MAXDEG], EV0[MAXN * MAXDEG];   /* base graph, oriented u in A (side 0), v in B */
static int K, MODE, rem[8];      /* removed base edge indices */
static int isrem[MAXN * MAXDEG];
static int bcol[MAXN];

static void build_surgery(void) {
    /* rebuild adj/deg/side from base minus removed plus new vertices a=n0, b=n0+1 */
    n = n0 + 2;
    for (int x = 0; x < n; x++) deg[x] = 0;
    for (int i = 0; i < m0; i++) isrem[i] = 0;
    for (int i = 0; i < K; i++) isrem[rem[i]] = 1;
    int a = n0, b = n0 + 1;
    for (int i = 0; i < m0; i++) if (!isrem[i]) { adj[EU0[i]][deg[EU0[i]]++] = EV0[i]; adj[EV0[i]][deg[EV0[i]]++] = EU0[i]; }
    for (int i = 0; i < K; i++) {
        int u = EU0[rem[i]], v = EV0[rem[i]];
        adj[a][deg[a]++] = v; adj[v][deg[v]++] = a;
        adj[b][deg[b]++] = u; adj[u][deg[u]++] = b;
    }
    if (MODE == 3) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
    for (int x = 0; x < n0; x++) side[x] = bcol[x];
    side[n0] = 0; side[n0 + 1] = 1;
}
static int disjoint_choice(int idx) {
    /* idx must not be already removed and must not share an endpoint with the other removed edges */
    if (isrem[idx]) return 0;
    for (int i = 0; i < K; i++) { int r = rem[i]; if (r == idx) return 0;
        if (EU0[r] == EU0[idx] || EV0[r] == EV0[idx]) return 0; }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: surgsa BASE OUT SECONDS SEED MODE T0 T1\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    const char *out = argv[2];
    double secs = atof(argv[3]); rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 2654435761ULL; for (int i = 0; i < 10; i++) rnd64();
    MODE = atoi(argv[5]); K = MODE == 3 ? 3 : 4;
    double T0 = atof(argv[6]), T1 = atof(argv[7]);
    if (fscanf(f, "%d", &n0) != 1) return 2;
    static int dg[MAXN];
    int a, b; m0 = 0;
    while (fscanf(f, "%d %d", &a, &b) == 2) { EU0[m0] = a; EV0[m0] = b; m0++; dg[a]++; dg[b]++; }
    fclose(f);
    /* orient: u in side 0 */
    static int col[MAXN]; for (int x = 0; x < n0; x++) col[x] = -1;
    { /* adjacency for colouring */
        static int badj[MAXN][MAXDEG], bd[MAXN]; for (int i = 0; i < m0; i++) { badj[EU0[i]][bd[EU0[i]]++] = EV0[i]; badj[EV0[i]][bd[EV0[i]]++] = EU0[i]; }
        for (int s = 0; s < n0; s++) if (col[s] < 0) { static int q[MAXN]; int h = 0, t = 0; col[s] = 0; q[t++] = s;
            while (h < t) { int x = q[h++]; for (int i = 0; i < bd[x]; i++) { int y = badj[x][i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } } } }
    }
    for (int x = 0; x < n0; x++) bcol[x] = col[x];
    for (int i = 0; i < m0; i++) if (col[EU0[i]] != 0) { int t = EU0[i]; EU0[i] = EV0[i]; EV0[i] = t; }
    /* initial random disjoint choice */
    for (int i = 0; i < K; ) { int c = rndint(m0); int ok = 1; for (int j = 0; j < i; j++) if (rem[j] == c || EU0[rem[j]] == EU0[c] || EV0[rem[j]] == EV0[c]) ok = 0;
        if (ok) rem[i++] = c; }
    for (int i = 0; i < m0; i++) isrem[i] = 0;
    build_surgery();
    long long curW = far_ordered((long long)1 << 60), cur = curW / 2, best = cur;
    int brem[8]; memcpy(brem, rem, sizeof(rem));
    fprintf(stderr, "start n=%d K=%d far=%lld\n", n, K, cur);
    FILE *fo = NULL;
    double t0 = now(), tl = now(), T = T0; long long it = 0, acc = 0;
    while (1) {
        double el = now() - t0; if (el > secs) break;
        T = T0 * pow(T1 / T0, el / secs);
        if (now() - tl > 30) { tl = now(); fprintf(stderr, "t=%.0f it=%lld cur=%lld best=%lld T=%.2f acc=%.3f\n", el, it, cur, best, T, acc ? (double)acc / it : 0.0); }
        it++;
        int i = rndint(K); int old = rem[i]; int nw = rndint(m0);
        if (!disjoint_choice(nw)) continue;
        rem[i] = nw;
        build_surgery();
        double u = rnd01(); double thr = (double)cur - T * log(u); long long cap = (long long)floor(2.0 * thr);
        long long W = far_ordered(cap);
        if (W <= cap) { cur = W / 2; acc++;
            if (cur < best) { best = cur; memcpy(brem, rem, sizeof(rem));
                fo = fopen(out, "w");
                if (fo) { /* write the best surgery graph (rebuilt from base with brem) */
                    int saved[8]; memcpy(saved, rem, sizeof(rem)); memcpy(rem, brem, sizeof(rem)); build_surgery();
                    fprintf(fo, "%d\n", n); for (int x = 0; x < n; x++) if (side[x] == 0) for (int j = 0; j < deg[x]; j++) fprintf(fo, "%d %d\n", x, adj[x][j]);
                    fclose(fo); memcpy(rem, saved, sizeof(rem)); build_surgery(); }
                fprintf(stderr, "t=%.0f it=%lld NEW BEST far=%lld rem=", el, it, best);
                for (int j = 0; j < K; j++) fprintf(stderr, "%d(%d,%d) ", rem[j], EU0[rem[j]], EV0[rem[j]]);
                fprintf(stderr, "\n");
            }
        } else { rem[i] = old; build_surgery(); }
    }
    printf("BEST %lld iterations %lld accepted %lld\n", best, it, acc);
    return 0;
}
