/* surg.c: "plus 2" surgery on a valid 6-regular bipartite diameter-5 graph.
   Cost = number of unordered same-side pairs at distance > 4 (or unreachable).
   Cost 0 <=> diameter <= 5 (for a connected bipartite graph with every vertex of degree >= 1).

   Modes:
     surg analyze EDGES           reliance per edge, zero-reliance count, greedy joint removal, distance-profile classes
     surg sa EDGES XY SECS SEED OUTPREFIX [T0]
                                  simulated annealing over matchings M (size K=6, or 5 if XY=1).
                                  New A-vertex x=N0 joined to the B-ends of M; new B-vertex y=N0+1 joined to the A-ends.
                                  If XY=1 also edge x-y.                                              */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int *deg_, *st_, *adj_, *pos_;
static u64 *vA, *fA, *nA;

static void alloc_work(int nmax, int mmax) {
    deg_ = calloc(nmax + 2, sizeof(int)); st_ = calloc(nmax + 3, sizeof(int)); pos_ = calloc(nmax + 2, sizeof(int));
    adj_ = malloc(sizeof(int) * (2 * (size_t)mmax + 4));
    vA = malloc(sizeof(u64) * (nmax + 2)); fA = malloc(sizeof(u64) * (nmax + 2)); nA = malloc(sizeof(u64) * (nmax + 2));
}

/* number of unordered same-side pairs at distance > 4 (unreachable counts as bad) */
static long eval_cost(int N, int m, const int *EU, const int *EW, const int *side) {
    memset(deg_, 0, sizeof(int) * (N + 1));
    for (int i = 0; i < m; i++) { deg_[EU[i]]++; deg_[EW[i]]++; }
    st_[0] = 0;
    for (int x = 0; x < N; x++) st_[x + 1] = st_[x] + deg_[x];
    memset(pos_, 0, sizeof(int) * (N + 1));
    for (int i = 0; i < m; i++) {
        int u = EU[i], w = EW[i];
        adj_[st_[u] + pos_[u]++] = w; adj_[st_[w] + pos_[w]++] = u;
    }
    long bad = 0;
    for (int s0 = 0; s0 < N; s0 += 64) {
        int ns = (N - s0 < 64) ? (N - s0) : 64;
        u64 sm[2] = {0, 0};
        u64 *fr = fA, *nx = nA;
        memset(vA, 0, sizeof(u64) * N); memset(fr, 0, sizeof(u64) * N);
        for (int k = 0; k < ns; k++) { int v = s0 + k; u64 b = 1ULL << k; vA[v] |= b; fr[v] |= b; sm[side[v]] |= b; }
        for (int lev = 0; lev < 4; lev++) {
            for (int x = 0; x < N; x++) {
                u64 acc = 0;
                for (int j = st_[x]; j < st_[x + 1]; j++) acc |= fr[adj_[j]];
                nx[x] = acc & ~vA[x];
            }
            for (int x = 0; x < N; x++) vA[x] |= nx[x];
            u64 *t = fr; fr = nx; nx = t;
        }
        for (int t = 0; t < N; t++) bad += __builtin_popcountll(sm[side[t]] & ~vA[t]);
    }
    return bad / 2;
}

static u64 rng_s = 88172645463325252ULL;
static u64 rnd(void) { rng_s ^= rng_s >> 12; rng_s ^= rng_s << 25; rng_s ^= rng_s >> 27; return rng_s * 2685821657736338717ULL; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int N0, M0;
static int *EU0, *EW0, *SIDE0;

static void load(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f || fscanf(f, "%d", &N0) != 1) { fprintf(stderr, "bad file\n"); exit(1); }
    int cap = 1 << 16; EU0 = malloc(sizeof(int) * cap); EW0 = malloc(sizeof(int) * cap); M0 = 0;
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (M0 == cap) { cap *= 2; EU0 = realloc(EU0, sizeof(int) * cap); EW0 = realloc(EW0, sizeof(int) * cap); }
        EU0[M0] = a; EW0[M0] = b; M0++;
    }
    fclose(f);
    /* bipartition by BFS from 0 */
    SIDE0 = malloc(sizeof(int) * (N0 + 2));
    for (int i = 0; i < N0; i++) SIDE0[i] = -1;
    int *dg = calloc(N0 + 1, sizeof(int));
    for (int i = 0; i < M0; i++) { dg[EU0[i]]++; dg[EW0[i]]++; }
    int *s = calloc(N0 + 1, sizeof(int)); for (int i = 0; i < N0; i++) s[i + 1] = s[i] + dg[i];
    int *ad = malloc(sizeof(int) * (2 * M0 + 1)); int *p = calloc(N0 + 1, sizeof(int));
    for (int i = 0; i < M0; i++) { int u = EU0[i], w = EW0[i]; ad[s[u] + p[u]++] = w; ad[s[w] + p[w]++] = u; }
    int *q = malloc(sizeof(int) * N0); int h = 0, t = 0;
    SIDE0[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int j = s[x]; j < s[x + 1]; j++) { int y = ad[j]; if (SIDE0[y] < 0) { SIDE0[y] = 1 - SIDE0[x]; q[t++] = y; } } }
    if (t != N0) { fprintf(stderr, "disconnected input\n"); exit(1); }
    fprintf(stderr, "loaded n=%d m=%d\n", N0, M0);
}

/* distance-1..5 profiles per vertex, for orbit-like classes */
static int cmp_prof(const void *a, const void *b) { return memcmp(a, b, 7 * sizeof(int)); }
static void profiles(void) {
    int *prof = malloc(sizeof(int) * 7 * N0);
    int *dist = malloc(sizeof(int) * N0), *q = malloc(sizeof(int) * N0);
    int *s = calloc(N0 + 1, sizeof(int)), *dg = calloc(N0 + 1, sizeof(int)), *p = calloc(N0 + 1, sizeof(int));
    int *ad = malloc(sizeof(int) * (2 * M0));
    for (int i = 0; i < M0; i++) { dg[EU0[i]]++; dg[EW0[i]]++; }
    for (int i = 0; i < N0; i++) s[i + 1] = s[i] + dg[i];
    for (int i = 0; i < M0; i++) { int u = EU0[i], w = EW0[i]; ad[s[u] + p[u]++] = w; ad[s[w] + p[w]++] = u; }
    for (int src = 0; src < N0; src++) {
        for (int i = 0; i < N0; i++) dist[i] = -1;
        int h = 0, t = 0; dist[src] = 0; q[t++] = src;
        int *pr = prof + 7 * src; memset(pr, 0, sizeof(int) * 7);
        while (h < t) { int x = q[h++]; for (int j = s[x]; j < s[x + 1]; j++) { int y = ad[j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; if (dist[y] <= 6) pr[dist[y]]++; q[t++] = y; } } }
    }
    /* sort copies to count classes */
    int *tmp = malloc(sizeof(int) * 7 * N0); memcpy(tmp, prof, sizeof(int) * 7 * N0);
    qsort(tmp, N0, 7 * sizeof(int), cmp_prof);
    int classes = 0, runs[700]; int nr = 0; int run = 1;
    for (int i = 1; i <= N0; i++) {
        if (i < N0 && memcmp(tmp + 7 * i, tmp + 7 * (i - 1), 7 * sizeof(int)) == 0) run++;
        else { if (nr < 700) runs[nr++] = run; classes++; run = 1; }
    }
    printf("distance-profile classes: %d (sizes:", classes);
    for (int i = 0; i < nr && i < 40; i++) printf(" %d", runs[i]);
    printf(")\n");
    printf("sample profile (d=1..5, >5) of vertex 0: %d %d %d %d %d %d\n", prof[1], prof[2], prof[3], prof[4], prof[5], prof[6]);
    free(prof); free(dist); free(q); free(s); free(dg); free(p); free(ad); free(tmp);
}

static void build_base(int *EU, int *EW, int *m_out, const int *deleted) {
    int m = 0;
    for (int i = 0; i < M0; i++) if (!deleted[i]) { EU[m] = EU0[i]; EW[m] = EW0[i]; m++; }
    *m_out = m;
}

static void analyze(void) {
    int *EU = malloc(sizeof(int) * (M0 + 40)), *EW = malloc(sizeof(int) * (M0 + 40));
    int *del = calloc(M0 + 1, sizeof(int));
    int *SIDE = SIDE0;
    alloc_work(N0 + 2, M0 + 40);
    long base = eval_cost(N0, M0, EU0, EW0, SIDE);
    printf("base cost = %ld\n", base);
    profiles();
    /* reliance: same-side bad pairs after deleting edge e */
    int *rel = malloc(sizeof(int) * M0); int zero = 0; long hist[64] = {0};
    for (int e = 0; e < M0; e++) {
        memset(del, 0, sizeof(int) * M0); del[e] = 1;
        int m; build_base(EU, EW, &m, del);
        long c = eval_cost(N0, m, EU, EW, SIDE);
        rel[e] = (int)c; if (c == 0) zero++;
        hist[c < 63 ? c : 63]++;
    }
    printf("reliance (bad pairs after deleting one edge): zero-reliance edges = %d of %d\n", zero, M0);
    printf("reliance histogram (value:count):");
    for (int v = 0; v < 64; v++) if (hist[v]) printf(" %d:%ld", v, hist[v]);
    printf("\n");
    /* greedy joint removal among zero-reliance edges, several random orders */
    int best_joint = 0;
    for (int trial = 0; trial < 20; trial++) {
        int *ord = malloc(sizeof(int) * M0); for (int i = 0; i < M0; i++) ord[i] = i;
        for (int i = M0 - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        memset(del, 0, sizeof(int) * M0); int cnt = 0;
        for (int k = 0; k < M0; k++) {
            int e = ord[k]; if (rel[e] != 0) continue;
            del[e] = 1; int m; build_base(EU, EW, &m, del);
            if (eval_cost(N0, m, EU, EW, SIDE) == 0) cnt++; else del[e] = 0;
        }
        if (cnt > best_joint) best_joint = cnt;
        free(ord);
    }
    printf("greedy jointly removable edges (cost stays 0, 20 random orders, best): %d\n", best_joint);
}

/* ---------- surgery SA ---------- */
static int K_, XY_;
static int Mat[16];
static char *inM;

static int endpoints_ok(int e, int skip) {
    int a = EU0[e], b = EW0[e];
    for (int j = 0; j < K_; j++) {
        if (j == skip) continue;
        int f = Mat[j]; if (f < 0) continue; int c = EU0[f], d = EW0[f];
        if (a == c || a == d || b == c || b == d) return 0;
    }
    return 1;
}

static long cost_of_matching(int *EU, int *EW, int *SIDE2) {
    int N = N0 + 2, x = N0, y = N0 + 1;
    int m = 0;
    static int *del = NULL; if (!del) del = calloc(M0 + 1, sizeof(int));
    memset(del, 0, sizeof(int) * M0);
    for (int j = 0; j < K_; j++) del[Mat[j]] = 1;
    for (int i = 0; i < M0; i++) if (!del[i]) { EU[m] = EU0[i]; EW[m] = EW0[i]; m++; }
    for (int j = 0; j < K_; j++) {
        int e = Mat[j]; int a, b;
        if (SIDE0[EU0[e]] == 0) { a = EU0[e]; b = EW0[e]; } else { a = EW0[e]; b = EU0[e]; }
        EU[m] = x; EW[m] = b; m++;   /* x (side 0) ~ b (side 1) */
        EU[m] = y; EW[m] = a; m++;   /* y (side 1) ~ a (side 0) */
    }
    if (XY_) { EU[m] = x; EW[m] = y; m++; }
    SIDE2[x] = 0; SIDE2[y] = 1;
    return eval_cost(N, m, EU, EW, SIDE2);
}

static void write_matching(const char *fn, const int *M) {
    int N = N0 + 2, x = N0, y = N0 + 1;
    FILE *f = fopen(fn, "w");
    int *del = calloc(M0 + 1, sizeof(int));
    for (int j = 0; j < K_; j++) del[M[j]] = 1;
    fprintf(f, "%d\n", N);
    for (int i = 0; i < M0; i++) if (!del[i]) fprintf(f, "%d %d\n", EU0[i], EW0[i]);
    for (int j = 0; j < K_; j++) {
        int e = M[j]; int a, b;
        if (SIDE0[EU0[e]] == 0) { a = EU0[e]; b = EW0[e]; } else { a = EW0[e]; b = EU0[e]; }
        fprintf(f, "%d %d\n%d %d\n", x, b, y, a);
    }
    if (XY_) fprintf(f, "%d %d\n", x, y);
    fclose(f); (void)N;
}

static void anneal(int secs, double T0, const char *outp) {
    int N = N0 + 2;
    int *EU = malloc(sizeof(int) * (M0 + 40)), *EW = malloc(sizeof(int) * (M0 + 40)), *SIDE2 = malloc(sizeof(int) * (N + 2));
    alloc_work(N + 2, M0 + 40);
    memcpy(SIDE2, SIDE0, sizeof(int) * N0);
    inM = calloc(M0 + 1, 1);
    /* random initial matching */
    for (int j = 0; j < 16; j++) Mat[j] = -1;
    for (int j = 0; j < K_; j++) {
        for (;;) { int e = rnd() % M0; if (endpoints_ok(e, j) && !inM[e]) { Mat[j] = e; break; } }
        /* endpoints_ok compares against Mat[j'] for j'!=j; Mat[j] set after check */
        inM[Mat[j]] = 1;
    }
    /* rebuild inM properly */
    memset(inM, 0, M0);
    for (int j = 0; j < K_; j++) inM[Mat[j]] = 1;
    long cur = cost_of_matching(EU, EW, SIDE2);
    long best = cur; int bestM[16]; memcpy(bestM, Mat, sizeof(Mat));
    double Tend = 0.05;
    clock_t c0 = clock(); long it = 0; double el = 0;
    fprintf(stderr, "init cost %ld\n", cur);
    while (1) {
        if ((it & 255) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            if ((it & 16383) == 0) fprintf(stderr, "t=%.0fs it=%ld cur=%ld best=%ld\n", el, it, cur, best);
        }
        it++;
        double frac = el / secs;
        double T = T0 * pow(Tend / T0, frac);
        int j = rnd() % K_;
        int e = rnd() % M0;
        if (inM[e] || !endpoints_ok(e, j)) continue;
        int old = Mat[j];
        Mat[j] = e;
        long nc = cost_of_matching(EU, EW, SIDE2);
        long d = nc - cur;
        if (d <= 0 || urand() < exp(-(double)d / T)) {
            inM[old] = 0; inM[e] = 1; cur = nc;
            if (cur < best) {
                best = cur; memcpy(bestM, Mat, sizeof(Mat));
                if (best == 0) break;
            }
        } else Mat[j] = old;
    }
    fprintf(stderr, "done it=%ld best=%ld\n", it, best);
    printf("RESULT best_cost=%ld n=%d K=%d XY=%d iters=%ld\n", best, N0 + 2, K_, XY_, it);
    memcpy(Mat, bestM, sizeof(Mat));
    char fn[512]; snprintf(fn, sizeof fn, "%s.%s.edges", outp, best == 0 ? "cost0" : "best");
    write_matching(fn, bestM);
    printf("wrote %s\n", fn);
    printf("matching (deleted edges a-b):");
    for (int j = 0; j < K_; j++) printf(" %d-%d", EU0[bestM[j]], EW0[bestM[j]]);
    printf("\n");
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: surg analyze EDGES | surg sa EDGES XY SECS SEED OUTPREFIX [T0]\n"); return 1; }
    load(argv[2]);
    if (!strcmp(argv[1], "analyze")) { analyze(); return 0; }
    if (!strcmp(argv[1], "sa") && argc >= 7) {
        XY_ = atoi(argv[3]); K_ = XY_ ? 5 : 6;
        int secs = atoi(argv[4]); rng_s ^= (u64)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
        double T0 = argc >= 8 ? atof(argv[7]) : 1.0;
        anneal(secs, T0, argv[6]);
        return 0;
    }
    fprintf(stderr, "bad args\n"); return 1;
}
