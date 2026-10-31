/* reg.c (r2b): exact region re-solve for bipartite cubic graphs, goal diameter <= 7.
   Region S = ball of radius R around a centre c. R_edges = all edges inside S (K of them).
   Their 2K endpoint stubs are re-matched: A-stub i (the A end of removed edge i) gets a new
   B-neighbour = B end of removed edge pi(i). Every full permutation (checked for simplicity)
   gives a cubic bipartite simple graph. All permutations are enumerated by DFS and the full
   graph is scored by far (unordered pairs at distance > 7), as in bin/score37.

   Usage:
     reg scan  IN.edges RADIUS [KMAX] [OUTPREFIX]
         for every centre: best far over all re-matchings of the ball's internal edges
     reg walk  IN.edges RADIUS ITERS SEED SLACK [KMAX] [OUTPREFIX]
         LNS walk: random centre, exhaustive re-match, take a uniformly random minimal-far
         rewiring if far <= cur + SLACK (plateau moves allowed), log global best.
   Build: gcc -O3 -march=native -o reg reg.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 256
#define MAXK 14

static int n;
static int dg[MAXN];
static int ad[MAXN][3];
static int sd[MAXN];
static int odg[MAXN];
static int oad[MAXN][3];
static uint64_t vis[MAXN], fr[MAXN], nx[MAXN];

static long far_count(void) {
    long long fo = 0;
    for (int s0 = 0; s0 < n; s0 += 64) {
        int ns = n - s0 < 64 ? n - s0 : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, sizeof(uint64_t) * n);
        memset(fr, 0, sizeof(uint64_t) * n);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < 7; lev++) {
            int any = 0;
            for (int x = 0; x < n; x++) {
                uint64_t acc = 0;
                for (int i = 0; i < dg[x]; i++) acc |= fr[ad[x][i]];
                acc &= ~vis[x];
                nx[x] = acc;
                any |= (acc != 0);
            }
            if (!any) break;
            for (int x = 0; x < n; x++) { vis[x] |= nx[x]; fr[x] = nx[x]; }
        }
        for (int x = 0; x < n; x++) fo += __builtin_popcountll(full & ~vis[x]);
    }
    return (long)(fo / 2);
}

static void save_orig(void) { memcpy(odg, dg, sizeof dg); memcpy(oad, ad, sizeof ad); }
static void restore_orig(void) { memcpy(dg, odg, sizeof dg); memcpy(ad, oad, sizeof ad); }

static int has_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++) if (ad[a][i] == b) return 1;
    return 0;
}
static void del_edge(int u, int v) {
    for (int i = 0; i < dg[u]; i++) if (ad[u][i] == v) { ad[u][i] = ad[u][--dg[u]]; break; }
    for (int i = 0; i < dg[v]; i++) if (ad[v][i] == u) { ad[v][i] = ad[v][--dg[v]]; break; }
}
static void add_edge(int u, int v) { ad[u][dg[u]++] = v; ad[v][dg[v]++] = u; }
static void pop_edge(int u, int v) { dg[u]--; dg[v]--; }

/* region data */
static int K;
static int ea[MAXK], eb[MAXK];   /* removed edges: A end, B end */
static int usedB[MAXK];
static int cur_perm[MAXK];
static long leaves, leafcap;
static long best_far;
static int best_perm[MAXK];
static long cur_far;
static long hist_min_count;
static int pick_mode;           /* 0: keep best; 1: walk (random among minimal, given thr) */
static long walk_thr;
static unsigned long long rng_state = 88172645463325252ULL;
static unsigned long long rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }
static long nmin_seen;          /* number of leaves achieving the current minimal far (walk reservoir) */
static long walk_min;
static int walk_perm[MAXK];

static void dfs(int i) {
    if (leafcap && leaves >= leafcap) return;
    if (i == K) {
        long f = far_count();
        leaves++;
        if (pick_mode == 0) {
            if (f < best_far) { best_far = f; memcpy(best_perm, cur_perm, sizeof(int) * K); }
        } else {
            if (f < walk_min) { walk_min = f; nmin_seen = 1; memcpy(walk_perm, cur_perm, sizeof(int) * K); }
            else if (f == walk_min) { nmin_seen++; if (rnd() % nmin_seen == 0) memcpy(walk_perm, cur_perm, sizeof(int) * K); }
        }
        return;
    }
    int a = ea[i];
    for (int j = 0; j < K; j++) {
        if (usedB[j]) continue;
        int b = eb[j];
        if (dg[a] >= 3 || dg[b] >= 3) continue;
        if (has_edge(a, b)) continue;
        add_edge(a, b);
        usedB[j] = 1; cur_perm[i] = j;
        dfs(i + 1);
        usedB[j] = 0;
        pop_edge(a, b);
    }
}

/* ball of radius r around c; inS marks members */
static int inS[MAXN];
static int ball(int c, int r, int *list) {
    int q[MAXN], dist[MAXN], h = 0, t = 0, cnt = 0;
    for (int i = 0; i < n; i++) dist[i] = -1;
    q[t++] = c; dist[c] = 0;
    while (h < t) {
        int x = q[h++];
        list[cnt++] = x;
        if (dist[x] == r) continue;
        for (int i = 0; i < odg[x]; i++) {
            int y = oad[x][i];
            if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; }
        }
    }
    for (int i = 0; i < n; i++) inS[i] = 0;
    for (int i = 0; i < cnt; i++) inS[list[i]] = 1;
    return cnt;
}

/* build region: removed edges = edges of G inside S (original graph, restored state) */
static int build_region(int cnt, int *list) {
    K = 0;
    for (int i = 0; i < cnt; i++) {
        int v = list[i];
        for (int j = 0; j < odg[v]; j++) {
            int w = oad[v][j];
            if (w <= v || !inS[w]) continue;
            if (sd[v] == 0) { ea[K] = v; eb[K] = w; } else { ea[K] = w; eb[K] = v; }
            K++;
        }
    }
    return K;
}

/* enumerate all re-matchings of the region; pick_mode 0: best; 1: walk */
static void enumerate_region(void) {
    for (int i = 0; i < K; i++) del_edge(ea[i], eb[i]);
    for (int j = 0; j < K; j++) usedB[j] = 0;
    leaves = 0;
    dfs(0);
    /* restoring is done by the caller */
}

static void apply_perm(const int *perm) {
    for (int i = 0; i < K; i++) add_edge(ea[i], eb[perm[i]]);
}

static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++) for (int i = 0; i < dg[v]; i++) if (ad[v][i] > v) fprintf(f, "%d %d\n", v, ad[v][i]);
    fclose(f);
}

static int read_graph(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(2); }
    if (fscanf(f, "%d", &n) != 1) exit(2);
    memset(dg, 0, sizeof dg);
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (dg[a] >= 3 || dg[b] >= 3) { fprintf(stderr, "not cubic\n"); exit(2); }
        ad[a][dg[a]++] = b; ad[b][dg[b]++] = a;
    }
    fclose(f);
    /* sides by BFS */
    for (int i = 0; i < n; i++) sd[i] = -1;
    int q[MAXN], h = 0, t = 0; sd[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < dg[x]; i++) { int y = ad[x][i]; if (sd[y] < 0) { sd[y] = 1 - sd[x]; q[t++] = y; } } }
    save_orig();
    return n;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: reg scan|walk IN RADIUS ...\n"); return 2; }
    const char *mode = argv[1];
    read_graph(argv[2]);
    int R = atoi(argv[3]);
    static int list[MAXN];
    long base = far_count();
    fprintf(stderr, "n=%d start far=%ld\n", n, base);
    if (!strcmp(mode, "scan")) {
        int kmax = argc > 4 ? atoi(argv[4]) : MAXK;
        const char *pref = argc > 5 ? argv[5] : NULL;
        long gbest = 1L << 40; int gcen = -1;
        long nimp = 0;
        for (int c = 0; c < n; c++) {
            int cnt = ball(c, R, list);
            build_region(cnt, list);
            if (K > kmax) continue;
            pick_mode = 0; best_far = 1L << 40; leafcap = 0;
            enumerate_region();
            long lb = best_far;
            restore_orig();
            printf("centre %d side %d ball %d K %d leaves %ld best %ld\n", c, sd[c], cnt, K, leaves, lb);
            fflush(stdout);
            if (lb < gbest) { gbest = lb; gcen = c; }
            if (lb < base && pref) {
                /* rebuild best and write */
                for (int i = 0; i < K; i++) del_edge(ea[i], eb[i]);
                apply_perm(best_perm);
                char fn[512]; snprintf(fn, sizeof fn, "%s_c%d_f%ld.edges", pref, c, lb);
                write_graph(fn);
                restore_orig();
                nimp++;
            }
        }
        printf("SCAN DONE radius %d: global best %ld at centre %d (start %ld), improvements written %ld\n", R, gbest, gcen, base, nimp);
    } else if (!strcmp(mode, "walk")) {
        long iters = atol(argv[4]);
        rng_state ^= (unsigned long long)atol(argv[5]) * 2654435761ULL + 1;
        long slack = atol(argv[6]);
        int kmax = argc > 7 ? atoi(argv[7]) : MAXK;
        const char *pref = argc > 8 ? argv[8] : "out/walk";
        long cur = base, gbest = base;
        char fn[512];
        long accepted = 0, tried = 0;
        for (long it = 0; it < iters; it++) {
            int c = rnd() % n;
            int cnt = ball(c, R, list);
            build_region(cnt, list);
            if (K > kmax || K == 0) continue;
            pick_mode = 1; walk_min = 1L << 40; nmin_seen = 0; leafcap = 0;
            enumerate_region();
            restore_orig();
            tried++;
            if (walk_min <= cur + slack) {
                /* apply the chosen rewiring to the current graph */
                for (int i = 0; i < K; i++) del_edge(ea[i], eb[i]);
                apply_perm(walk_perm);
                save_orig();
                cur = walk_min; accepted++;
                if (cur < gbest) {
                    gbest = cur;
                    snprintf(fn, sizeof fn, "%s_best%ld.edges", pref, cur);
                    write_graph(fn);
                    fprintf(stderr, "it %ld: new best %ld (centre %d K %d)\n", it, cur, c, K);
                }
            }
            if (it % 50 == 0) { fprintf(stderr, "it %ld cur %ld best %ld tried %ld acc %ld\n", it, cur, gbest, tried, accepted); }
        }
        printf("WALK DONE: iters %ld tried %ld accepted %ld cur %ld best %ld\n", iters, tried, accepted, cur, gbest);
    }
    return 0;
}
