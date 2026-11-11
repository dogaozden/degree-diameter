/* tabu.c (w6, handsoff-49): best-of-K tabu search (same move set and far count as sa.c). Derived from sa.c.
   sa.c: simulated annealing on a bipartite graph with max degree DEG, cost = number of unordered
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


static int adjB[MAXN][MAXDEG], degB[MAXN];
static void save_best(void) { memcpy(adjB, adj, sizeof(adj)); memcpy(degB, deg, sizeof(deg)); }
static void restore_best(void) { memcpy(adj, adjB, sizeof(adj)); memcpy(deg, degB, sizeof(deg)); }

/* tabu list: recently removed edges (u,v) with expiry step */
#define TL 4096
static int tlu[TL], tlv[TL]; static long tle[TL]; static int tlcount = 0;
static int tabu_edge(int u, int v, long step) {
    for (int i = 0; i < TL; i++) if (tle[i] > step && ((tlu[i] == u && tlv[i] == v) || (tlu[i] == v && tlv[i] == u))) return 1;
    return 0;
}
static void add_tabu(int u, int v, long until) {
    tlu[tlcount] = u; tlv[tlcount] = v; tle[tlcount] = until; tlcount = (tlcount + 1) % TL;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: tabu IN OUT SECONDS SEED [K=150] [R=3] [TENURE=40] [STAG=400] [D=9]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 2; }
    const char *out = argv[2];
    double secs = atof(argv[3]); rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 2654435761ULL; for (int i = 0; i < 10; i++) rnd64();
    int K = argc > 5 ? atoi(argv[5]) : 150; int R = argc > 6 ? atoi(argv[6]) : 3;
    long TEN = argc > 7 ? atol(argv[7]) : 40; long STAG = argc > 8 ? atol(argv[8]) : 400; if (argc > 9) D = atoi(argv[9]);
    if (fscanf(f, "%d", &n) != 1) return 2;
    int m = 0; static int EU[MAXN * MAXDEG], EV[MAXN * MAXDEG]; int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (m >= MAXN * MAXDEG) return 2; EU[m] = a; EV[m] = b; m++; deg[a]++; deg[b]++; }
    fclose(f);
    for (int x = 0; x < n; x++) { if (deg[x] > DEGMAX) { fprintf(stderr, "degree too large\n"); return 2; } deg[x] = 0; }
    for (int i = 0; i < m; i++) { adj[EU[i]][deg[EU[i]]++] = EV[i]; adj[EV[i]][deg[EV[i]]++] = EU[i]; }
    for (int x = 0; x < n; x++) side[x] = -1;
    for (int s = 0; s < n; s++) if (side[s] < 0) {
        static int q[MAXN]; int h = 0, t = 0; side[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i];
            if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } else if (side[y] == side[x]) { fprintf(stderr, "not bipartite\n"); return 2; } } }
    }
    long long curW = far_ordered((long long)1 << 60);
    long long bestW = curW;
    save_best(); write_edges(out);
    fprintf(stderr, "start n=%d m=%d far=%lld D=%d K=%d R=%d tenure=%ld\n", n, m, curW / 2, D, K, R, TEN);
    double t0 = now(), tl = now();
    long step = 0, stag = 0;
    while (curW > 0) {
        double el = now() - t0; if (el > secs) break;
        step++;
        if (now() - tl > 30) { tl = now(); fprintf(stderr, "t=%.0f step=%ld cur=%lld best=%lld stag=%ld\n", el, step, curW / 2, bestW / 2, stag); }
        int s0 = rndint(n); int s = s0; int t = far_partner(s0);
        if (t < 0) continue;
        /* candidate search: best of K random targeted switches around the far pair (s,t) */
        long long candW = (long long)1 << 60; int bp[4] = {0, 0, 0, 0}; int found = 0;
        for (int k = 0, tries = 0; k < K && tries < 20 * K; tries++) {
            int x = walk(s, rndint(R + 1)), y = walk(t, rndint(R + 1));
            if (side[x] == side[y] || x == y) continue;
            if (deg[x] == 0 || deg[y] == 0) continue;
            int x2 = adj[x][rndint(deg[x])], y2 = adj[y][rndint(deg[y])];
            if (has_edge(x, y) || has_edge(x2, y2) || x2 == y || y2 == x) continue;
            if (tabu_edge(x, y, step) || tabu_edge(x2, y2, step)) continue;
            k++;
            swap_edges(x, x2, y, y2);
            long long W = far_ordered(candW);
            if (W <= candW) { candW = W; bp[0] = x; bp[1] = x2; bp[2] = y; bp[3] = y2; found = 1; }
            swap_edges(x, y, x2, y2); /* undo: edges {x,y},{x2,y2} -> {x,x2},{y,y2} */
        }
        if (!found) continue;
        swap_edges(bp[0], bp[1], bp[2], bp[3]);
        add_tabu(bp[0], bp[1], step + TEN); add_tabu(bp[2], bp[3], step + TEN);
        curW = candW;
        if (curW < bestW) {
            bestW = curW; save_best(); write_edges(out); stag = 0;
            fprintf(stderr, "t=%.0f step=%ld NEW BEST far=%lld\n", el, step, bestW / 2);
        } else stag++;
        if (stag > STAG) { /* restart from best with a few random switches */
            restore_best();
            for (int r = 0; r < 3; r++) {
                int A1 = rndint(n); if (side[A1]) continue; int B1 = adj[A1][rndint(deg[A1])];
                int A2 = rndint(n); if (side[A2]) continue; int B2 = adj[A2][rndint(deg[A2])];
                if (A1 == A2 || B1 == B2 || has_edge(A1, B2) || has_edge(B1, A2)) continue;
                swap_edges(A1, B1, B2, A2);
            }
            curW = far_ordered((long long)1 << 60); stag = 0;
        }
    }
    printf("BEST %lld steps %ld n %d\n", bestW / 2, step, n);
    return 0;
}
