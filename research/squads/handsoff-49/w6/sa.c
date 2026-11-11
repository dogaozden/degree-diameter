/* sa.c (w6, handsoff-49): simulated annealing on a bipartite graph with max degree DEG, cost = number of unordered
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

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: sa IN OUT SECONDS SEED T0 T1 [PT=0.7] [R=2] [D=9]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 2; }
    const char *out = argv[2];
    double secs = atof(argv[3]); rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 2654435761ULL; for (int i = 0; i < 10; i++) rnd64();
    double T0 = atof(argv[5]), T1 = atof(argv[6]);
    double PT = argc > 7 ? atof(argv[7]) : 0.7; int R = argc > 8 ? atoi(argv[8]) : 2; if (argc > 9) D = atoi(argv[9]);
    if (fscanf(f, "%d", &n) != 1) return 2;
    int m = 0; static int EU[MAXN * MAXDEG], EV[MAXN * MAXDEG]; int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (m >= MAXN * MAXDEG) return 2; EU[m] = a; EV[m] = b; m++; deg[a]++; deg[b]++; }
    fclose(f);
    for (int x = 0; x < n; x++) { if (deg[x] > DEGMAX) { fprintf(stderr, "degree too large\n"); return 2; } deg[x] = 0; }
    for (int i = 0; i < m; i++) { adj[EU[i]][deg[EU[i]]++] = EV[i]; adj[EV[i]][deg[EV[i]]++] = EU[i]; }
    /* 2-colouring */
    for (int x = 0; x < n; x++) side[x] = -1;
    for (int s = 0; s < n; s++) if (side[s] < 0) {
        static int q[MAXN]; int h = 0, t = 0; side[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i];
            if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } else if (side[y] == side[x]) { fprintf(stderr, "not bipartite\n"); return 2; } } }
    }
    long long cur2 = far_ordered((long long)1 << 60);
    long long cur = cur2 / 2, best = cur;
    write_edges(out);
    fprintf(stderr, "start n=%d m=%d far=%lld D=%d\n", n, m, cur, D);
    double t0 = now(), tl = now(), T = T0;
    long long it = 0, acc = 0, tries = 0;
    while (cur > 0) {
        double el = now() - t0; if (el > secs) break;
        T = T0 * pow(T1 / T0, el / secs);
        if (now() - tl > 20) { tl = now(); fprintf(stderr, "t=%.0f it=%lld cur=%lld best=%lld T=%.3f acc=%.3f\n", el, it, cur, best, T, acc ? (double)acc / it : 0.0); }
        it++;
        int kind; int p1, p2, p3, p4; /* swap_edges(p1,p2,p3,p4) */
        if (rnd01() < PT) {
            int s = rndint(n); int t = far_partner(s); if (t < 0) { tries++; continue; }
            int x = walk(s, rndint(R + 1)), y = walk(t, rndint(R + 1));
            if (side[x] == side[y] || x == y) continue;
            if (deg[x] == 0 || deg[y] == 0) continue;
            int x2 = adj[x][rndint(deg[x])], y2 = adj[y][rndint(deg[y])];
            if (has_edge(x, y) || has_edge(x2, y2)) continue;
            if (x2 == y || y2 == x) continue;
            kind = 0; p1 = x; p2 = x2; p3 = y; p4 = y2;
        } else {
            int e1 = rndint(n); int A1, B1;
            if (side[e1] == 0) A1 = e1; else continue;
            B1 = adj[A1][rndint(deg[A1])];
            int A2 = rndint(n); if (side[A2] != 0) continue;
            int B2 = adj[A2][rndint(deg[A2])];
            if (A1 == A2 || B1 == B2) continue;
            if (has_edge(A1, B2) || has_edge(B1, A2)) continue;
            kind = 1; p1 = A1; p2 = B1; p3 = B2; p4 = A2; /* remove {A1,B1},{B2,A2}; add {A1,B2},{B1,A2} */
        }
        /* apply: kind 0: swap(x,x2,y,y2) adds {x,y},{x2,y2}; kind 1: swap(A1,B1,B2,A2) adds {A1,B2},{B1,A2} */
        swap_edges(p1, p2, p3, p4);
        double u = rnd01(); double thr = (double)cur - T * log(u);
        long long cap = (long long)floor(2.0 * thr);
        long long W = far_ordered(cap);
        if (W <= cap) {
            cur = W / 2; acc++;
            if (cur < best) {
                best = cur; write_edges(out);
                fprintf(stderr, "t=%.0f it=%lld NEW BEST far=%lld\n", el, it, best);
            }
        } else {
            /* undo: after swap(p1,p2,p3,p4) the edges are {p1,p3},{p2,p4} */
            swap_edges(p1, p3, p2, p4);
        }
        (void)kind;
    }
    printf("BEST %lld iterations %lld accepted %lld tries %lld n %d\n", best, it, acc, tries, n);
    return 0;
}
