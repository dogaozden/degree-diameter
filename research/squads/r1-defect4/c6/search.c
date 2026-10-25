/*
 * c6/search.c -- custom backtracking search for bipartite (k,3,-4)-graphs (card c6).
 *
 * Model: n = k^2-k-1 points; lines are k-subsets (bitmasks), n of them; every point on k
 * lines. Diameter 3 <=> every two points share a line and every two lines share a point.
 * E := k(k-1)-(n-1) (= 2 here). Monotone (hence sound) pruning facts:
 *   - point x: excess(x) = deg(x)(k-1) - |covered(x)| <= E. This is exactly the count bound
 *     "uncovered(x) <= (k-deg x)(k-1)"; at the end deg = k forces excess = E.
 *   - line l: excess(l) = sum over chosen l' != l of (|l & l'| - 1) <= E (budget per line).
 *   - every two chosen lines meet (|l & l'| >= 1).
 *   - deg(x) <= k.
 * Node pruning (sound): the candidates after the current choice must be able to supply the
 * remaining degree r(x) = k-deg(x) of every point, and for every point x the union of the
 * candidate lines through x must contain all points not yet collinear with x.
 *
 * Symmetry breaking (both valid, any graph can be relabelled to satisfy them):
 *   (a) Normal form: line 0 = {0..k-1}. Lines are numbered in lexicographic order of their
 *       sorted point lists. Lines through point 0 all precede the others and line 0 is the
 *       lex-smallest k-set, so lines 0..k-1 are exactly the lines through point 0 (the "star").
 *   (b) mode canon: the star is replaced by its canonical labelling. Blocks B_j = L_j \ {0}
 *       are listed in order; the points of each block are either old (already used by an
 *       earlier block; only possible for the E excess incidences) or new (get the next unused
 *       labels, consecutively). Every star is a relabelling of at least one such sequence
 *       (process the blocks in the given order and name new points as they appear), so this
 *       is complete. Afterwards the remaining lines (not through 0) are searched in lex order.
 *   mode lex: no canonical star; the first k lines of the lex search are forced to pass
 *       through point 0 (valid by (a)), otherwise the same search.
 *
 * Usage: ./search K [canon|lex] [time_limit_s=850] [maxsol=1] [N=K*K-K-1]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;
#define MAXN 48

static int K, N, E, NLINES, NALL, CANON;   /* CANON: 0 = lex (no canonical star), 1 = canon + lex rest, 2 = canon + pt branching */
static const char *MODENAME[] = {"lex", "canon", "pt"};
static u64 *LM;          /* all k-subsets in lex order of sorted lists */
static int *ALL;         /* candidate line indices (ascending) for the rest search */
static int *buf[MAXN + 2];
static u64 FULL;
static long long nodes = 0, pruned = 0, stars = 0, sols = 0, maxsol = 1;
static int stop = 0, timed_out = 0;
static double tlimit;
static struct timespec t0;
static u64 firstsol[MAXN];

typedef struct {
    int nch;
    int deg[MAXN];
    u64 cov[MAXN];   /* points (other than x) collinear with x so far */
    int bud[MAXN];   /* remaining line-excess budget of each chosen line */
    u64 lm[MAXN];    /* chosen lines */
} State;

static double now(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)(t.tv_sec - t0.tv_sec) + 1e-9 * (double)(t.tv_nsec - t0.tv_nsec);
}

/* May line m be added to state S? (meets all chosen lines, budgets, point excess, degree) */
static int feasible(const State *S, u64 m)
{
    int sumex = 0;
    for (int i = 0; i < S->nch; i++) {
        int inter = __builtin_popcountll(m & S->lm[i]);
        if (inter < 1 || inter - 1 > S->bud[i]) return 0;
        sumex += inter - 1;
    }
    if (sumex > E) return 0;
    for (u64 t = m; t; t &= t - 1) {
        int p = __builtin_ctzll(t);
        if (S->deg[p] >= K) return 0;
        u64 nc = S->cov[p] | (m & ~(1ULL << p));
        if ((S->deg[p] + 1) * (K - 1) - __builtin_popcountll(nc) > E) return 0;
    }
    return 1;
}

static void apply(State *S, u64 m)
{
    int sumex = 0;
    for (int i = 0; i < S->nch; i++) {
        int inter = __builtin_popcountll(m & S->lm[i]);
        S->bud[i] -= inter - 1;
        sumex += inter - 1;
    }
    S->lm[S->nch] = m;
    S->bud[S->nch] = E - sumex;
    S->nch++;
    for (u64 t = m; t; t &= t - 1) {
        int p = __builtin_ctzll(t);
        S->deg[p]++;
        S->cov[p] |= m & ~(1ULL << p);
    }
}

/* candidates cands[from..nc-1] that are feasible for S (order kept, i.e. lex order) */
static int filter(const State *S, const int *cands, int from, int nc, int *out)
{
    int c = 0;
    for (int t = from; t < nc; t++) {
        int li = cands[t];
        if (feasible(S, LM[li])) out[c++] = li;
    }
    return c;
}

/* sound node test on the child state C with candidate list out[0..c-1] */
static int node_ok(const State *C, const int *out, int c)
{
    int need = N - C->nch;
    if (c < need) return 0;
    int cnt[MAXN];
    u64 orm[MAXN];
    memset(cnt, 0, sizeof cnt);
    memset(orm, 0, sizeof orm);
    for (int t = 0; t < c; t++) {
        u64 m = LM[out[t]];
        for (u64 x = m; x; x &= x - 1) {
            int p = __builtin_ctzll(x);
            cnt[p]++;
            orm[p] |= m;
        }
    }
    for (int p = 0; p < N; p++) {
        int r = K - C->deg[p];
        if (r <= 0) continue;
        if (cnt[p] < r) return 0;
        u64 unc = FULL & ~C->cov[p] & ~(1ULL << p);
        if (unc & ~orm[p]) return 0;
    }
    return 1;
}

/* independent check: incidence graph of the N chosen lines, BFS; returns diameter */
static int check_solution(const State *S, int *maxdeg)
{
    static unsigned char A[2 * MAXN][2 * MAXN];
    int V = 2 * N;
    memset(A, 0, sizeof A);
    for (int j = 0; j < N; j++)
        for (u64 t = S->lm[j]; t; t &= t - 1) {
            int p = __builtin_ctzll(t);
            A[p][N + j] = A[N + j][p] = 1;
        }
    *maxdeg = 0;
    for (int v = 0; v < V; v++) {
        int dg = 0;
        for (int w = 0; w < V; w++) dg += A[v][w];
        if (dg > *maxdeg) *maxdeg = dg;
    }
    int diam = 0;
    for (int s = 0; s < V; s++) {
        int dist[2 * MAXN], q[2 * MAXN], h = 0, tl = 0;
        for (int v = 0; v < V; v++) dist[v] = -1;
        dist[s] = 0;
        q[tl++] = s;
        while (h < tl) {
            int v = q[h++];
            for (int w = 0; w < V; w++)
                if (A[v][w] && dist[w] < 0) { dist[w] = dist[v] + 1; q[tl++] = w; }
        }
        if (tl < V) return -1;
        if (dist[q[tl - 1]] > diam) diam = dist[q[tl - 1]];
    }
    return diam;
}

static void leaf(const State *S)
{
    for (int p = 0; p < N; p++) {
        if (S->deg[p] != K) return;
        if (__builtin_popcountll(S->cov[p]) != N - 1) return;
    }
    int md;
    int diam = check_solution(S, &md);
    if (diam != 3 || md > K) {
        fprintf(stderr, "BUG: leaf fails independent check (diam=%d maxdeg=%d)\n", diam, md);
        exit(2);
    }
    sols++;
    if (sols == 1) memcpy(firstsol, S->lm, sizeof(u64) * N);
    if (sols >= maxsol) stop = 1;
}

static void rec(const State *S, const int *cands, int nc)
{
    nodes++;
    if ((nodes & ((1LL << 18) - 1)) == 0 && now() > tlimit) { stop = 1; timed_out = 1; }
    if (stop) return;
    int need = N - S->nch;
    if (need == 0) { leaf(S); return; }
    if (nc < need) return;
    int *out = buf[S->nch + 1];
    for (int j = 0; j <= nc - need; j++) {          /* lines chosen in increasing lex order */
        /* lex mode: the first k chosen lines must pass through point 0; lines are lex-sorted,
           so the lines through 0 are a prefix of cands and the first non-0 line ends the star */
        if (!CANON && S->nch < K && !(LM[cands[j]] & 1ULL)) break;
        State C = *S;
        apply(&C, LM[cands[j]]);
        int c = filter(&C, cands, j + 1, nc, out);
        if (!node_ok(&C, out, c)) { pruned++; continue; }
        rec(&C, out, c);
        if (stop) return;
    }
}

/* mode pt (variant, same normal form and star, no lex branching):
   pick the point x with r_x = k-deg(x) > 0 and smallest slack cnt(x)-r_x; branch on the first
   chosen candidate through x, at position q in the lex list. Branch q excludes the candidates
   through x that precede q, so each completion is generated exactly once and no line is
   duplicated. Complete: every completion has some line through x, and the first such line
   defines the branch. */
static void rec_pt(const State *S, const int *cands, int nc)
{
    nodes++;
    if ((nodes & ((1LL << 18) - 1)) == 0 && now() > tlimit) { stop = 1; timed_out = 1; }
    if (stop) return;
    int need = N - S->nch;
    if (need == 0) { leaf(S); return; }
    if (nc < need) return;
    int cnt[MAXN];
    memset(cnt, 0, sizeof cnt);
    for (int t = 0; t < nc; t++)
        for (u64 x = LM[cands[t]]; x; x &= x - 1) cnt[__builtin_ctzll(x)]++;
    int bx = -1, bslack = 1 << 30;
    for (int p = 0; p < N; p++) {
        int r = K - S->deg[p];
        if (r <= 0) continue;
        int slack = cnt[p] - r;
        if (slack < bslack || (slack == bslack && r > K - S->deg[bx])) { bslack = slack; bx = p; }
    }
    if (bx < 0) return;
    if (bslack < 0) return;
    int *out = buf[S->nch + 1];
    for (int q = 0; q < nc && !stop; q++) {
        u64 mq = LM[cands[q]];
        if (!((mq >> bx) & 1ULL)) continue;
        State C = *S;
        apply(&C, mq);
        int c = 0;
        for (int t = 0; t < nc; t++) {
            if (t == q) continue;
            int li = cands[t];
            if (t < q && ((LM[li] >> bx) & 1ULL)) continue;   /* excluded: tried before */
            if (feasible(&C, LM[li])) out[c++] = li;
        }
        if (!node_ok(&C, out, c)) { pruned++; continue; }
        rec_pt(&C, out, c);
    }
}

static void search(const State *S, const int *cands, int nc)
{
    if (CANON == 2) rec_pt(S, cands, nc);
    else rec(S, cands, nc);
}

static void run_root(const State *S, int from)
{
    stars++;
    if (CANON && stars % 25 == 0)
        fprintf(stderr, "progress: stars=%lld nodes=%lld t=%.1fs\n", stars, nodes, now());
    int d = S->nch;
    int c = filter(S, ALL, from, NALL, buf[d]);
    if (node_ok(S, buf[d], c)) search(S, buf[d], c);
}

/* canonical star enumeration: block j has t old labels (from 1..u) and K-1-t new labels */
static void gen_star(const State *S, int j, int u, int oldused);

static void gen_block(const State *S, int j, int u, int oldused, int t, int start,
                      u64 oldmask, int rem)
{
    if (stop) return;
    if (rem == 0) {
        int nnew = K - 1 - t;
        u64 m = oldmask | 1ULL;                       /* point 0 */
        for (int x = 1; x <= nnew; x++) m |= 1ULL << (u + x);
        if (!feasible(S, m)) return;
        State T = *S;
        apply(&T, m);
        gen_star(&T, j + 1, u + nnew, oldused + t);
        return;
    }
    for (int x = start; x <= u; x++)
        gen_block(S, j, u, oldused, t, x + 1, oldmask | (1ULL << x), rem - 1);
}

static void gen_star(const State *S, int j, int u, int oldused)
{
    if (stop) return;
    if (j == K) {
        if (oldused == E && u == N - 1) run_root(S, 0);
        return;
    }
    int maxt = E - oldused;
    if (maxt > K - 1) maxt = K - 1;
    for (int t = 0; t <= maxt; t++) {
        if (u + (K - 1 - t) > N - 1) continue;
        gen_block(S, j, u, oldused, t, 1, 0, t);
    }
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "usage: %s K [canon|lex|pt] [time_limit_s=850] [maxsol=1] [N=K*K-K-1]\n", argv[0]);
        return 1;
    }
    clock_gettime(CLOCK_MONOTONIC, &t0);
    K = atoi(argv[1]);
    CANON = 1;
    if (argc > 2 && strcmp(argv[2], "lex") == 0) CANON = 0;
    if (argc > 2 && strcmp(argv[2], "pt") == 0) CANON = 2;
    tlimit = argc > 3 ? atof(argv[3]) : 850.0;
    maxsol = argc > 4 ? atoll(argv[4]) : 1;
    N = argc > 5 ? atoi(argv[5]) : K * K - K - 1;
    if (K < 3 || N > MAXN || N <= K) { fprintf(stderr, "bad K/N\n"); return 1; }
    E = K * (K - 1) - (N - 1);
    if (E < 0) { fprintf(stderr, "E<0\n"); return 1; }
    FULL = (1ULL << N) - 1;

    double cnt = 1;
    for (int i = 0; i < K; i++) cnt = cnt * (N - i) / (i + 1);
    NLINES = (int)(cnt + 0.5);
    LM = malloc(sizeof(u64) * NLINES);
    int c[MAXN];
    for (int i = 0; i < K; i++) c[i] = i;
    int idx = 0;
    for (;;) {                                        /* lex order of sorted lists */
        u64 m = 0;
        for (int i = 0; i < K; i++) m |= 1ULL << c[i];
        LM[idx++] = m;
        int i = K - 1;
        while (i >= 0 && c[i] == N - K + i) i--;
        if (i < 0) break;
        c[i]++;
        for (int jj = i + 1; jj < K; jj++) c[jj] = c[jj - 1] + 1;
    }
    ALL = malloc(sizeof(int) * NLINES);
    NALL = 0;
    for (int i = 0; i < NLINES; i++)
        if (!CANON || !(LM[i] & 1ULL)) ALL[NALL++] = i;
    for (int d = 0; d <= N + 1; d++) buf[d] = malloc(sizeof(int) * (NALL + 1));

    fprintf(stderr, "k=%d n=%d E=%d lines=%d mode=%s\n", K, N, E, NLINES, MODENAME[CANON]);

    State S0;
    memset(&S0, 0, sizeof S0);
    if (CANON) {
        apply(&S0, (1ULL << K) - 1);                  /* line 0 = {0..K-1} */
        gen_star(&S0, 1, K - 1, 0);
    } else {
        apply(&S0, LM[0]);                            /* line 0 = {0..K-1} */
        run_root(&S0, 1);
    }

    double T = now();
    const char *status = sols > 0 ? "FOUND" : (timed_out ? "TIMEOUT" : "EXHAUSTED_NO_SOLUTION");
    printf("RESULT k=%d n=%d E=%d mode=%s maxsol=%lld stars=%lld nodes=%lld pruned=%lld "
           "solutions=%lld time=%.2f status=%s\n",
           K, N, E, MODENAME[CANON], maxsol, stars, nodes, pruned, sols, T, status);
    if (sols > 0) {
        int md;
        State F;
        memset(&F, 0, sizeof F);
        for (int j = 0; j < N; j++) apply(&F, firstsol[j]);
        int diam = check_solution(&F, &md);
        printf("solution lines (points), independent BFS: diameter=%d maxdeg=%d\n", diam, md);
        for (int j = 0; j < N; j++) {
            printf("L%d:", j);
            for (u64 t = firstsol[j]; t; t &= t - 1) printf(" %d", __builtin_ctzll(t));
            printf("\n");
        }
    }
    return 0;
}
