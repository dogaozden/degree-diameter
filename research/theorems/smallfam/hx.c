/* hx.c: exhaustive Haar-graph search H(G,S), S = {e, s1, s2, ...}, diameter <= D, over a plan of (s1, s2) pairs.

   G is either a metacyclic group Z_m x|_r Z_k ((a,j)(b,l) = (a + r^j b, j + l), index a*k + j) or any group given by a
   multiplication table file (from GAP: first line "N e", then N lines of N 0-based entries, row x = x*y for all y).
   Haar graph: (g,A) ~ (s g, B).  Right multiplication is transitive on each side, so
     D even: every (g,B) within D-1 of (e,A);
     D odd : every (g,A) within D-1 of (e,A) and every (g,B) within D-1 of (e,B).
   Cost = number of uncovered targets (0 = diameter <= D).

   Usage:
     hx meta m k r  DELTA D PLAN [MAXPRINT]
     hx tab FILE    DELTA D PLAN [MAXPRINT]
   PLAN: lines "s1 s2" (element indices).  The remaining DELTA-3 elements of S run over all unordered sets of elements
   other than e, s1, s2 (so the plan only needs s1 up to Aut(G) and s2 up to Stab(s1)).  PLAN "-" reads stdin.
   Output: one line per solution "SOL s1 s2 s3 ..." (up to MAXPRINT, default 50), then a summary line
   "DONE tested T solutions K best_cost C best_set ...".
   Env THREADS (default 1): OpenMP threads over plan lines.
*/
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static int N, E, *T = NULL, *INV;          /* table: T[x*N + y] = x*y */
static int MM, KK, RR, *RP;                 /* meta */
static int ISMETA = 0, DELTA, D;

static inline int mul(int x, int y) {
    if (!ISMETA) return T[(size_t)x * N + y];
    int a = x / KK, j = x % KK, b = y / KK, l = y % KK;
    return (int)((a + (long long)RP[j] * b) % MM) * KK + (j + l) % KK;
}

/* BFS from (e, side) to depth D-1, counting uncovered vertices of 'target side' within D-1.
   Lmul[i][g] = s_i g  (A -> B),  Linv[i][g] = s_i^-1 g  (B -> A). */
typedef struct { int *dA, *dB, *q; } work;

static int bfs_cost(int *const *Lm, int *const *Li, int startB, int targetA, work *w) {
    int *dA = w->dA, *dB = w->dB, *q = w->q;
    for (int i = 0; i < N; i++) { dA[i] = -1; dB[i] = -1; }
    int head = 0, tail = 0;
    /* queue entries: g*2 + side (0 = A, 1 = B) */
    if (startB) { dB[E] = 0; q[tail++] = E * 2 + 1; } else { dA[E] = 0; q[tail++] = E * 2; }
    while (head < tail) {
        int v = q[head++], g = v >> 1, side = v & 1;
        int d = side ? dB[g] : dA[g];
        if (d >= D - 1) continue;
        if (side == 0) {
            for (int i = 0; i < DELTA; i++) { int h = Lm[i][g]; if (dB[h] < 0) { dB[h] = d + 1; q[tail++] = h * 2 + 1; } }
        } else {
            for (int i = 0; i < DELTA; i++) { int h = Li[i][g]; if (dA[h] < 0) { dA[h] = d + 1; q[tail++] = h * 2; } }
        }
    }
    int unc = 0;
    if (targetA) { for (int i = 0; i < N; i++) if (dA[i] < 0) unc++; }
    else { for (int i = 0; i < N; i++) if (dB[i] < 0) unc++; }
    return unc;
}

static int **LM, **LI;   /* left-multiplication tables for every element: LM[x][g] = x g (computed lazily: all) */

/* ---- quotient filter (rigorous): walks of H(G,S) project to walks of H(Q, S-bar) for a quotient Q = G/K.  Every
   vertex within D-1 of the source is the end of a non-backtracking walk of length <= D-1, so each K-coset on the
   target side needs at least |K| such walks landing on it.  QMAP file: "q" then the q x q table of Q, then N lines
   "image of element".  For meta groups QFILTER=1 uses Q = Z_k (the j-part). */
static int QN = 0, *QT = NULL, *QINV = NULL, *QMAPV = NULL, QE = 0, QK = 0;
static long long *QCACHE_KEY = NULL; static signed char *QCACHE_VAL = NULL; static size_t QCAP = 0;
static long long qfiltered = 0;

static int qdp_ok(const int *sb, int startB) {
    /* counts[side][v][last] for last in 0..DELTA (DELTA = none) */
    int L = DELTA + 1;
    long long *cur = calloc((size_t)2 * QN * L, sizeof(long long)), *nxt = calloc((size_t)2 * QN * L, sizeof(long long));
    long long *tot = calloc((size_t)QN, sizeof(long long));
    int tside = (D % 2 == 0) ? !startB : startB;   /* D even: opposite side; D odd: same side */
#define IX(s, v, l) (((size_t)(s) * QN + (v)) * L + (l))
    cur[IX(startB, QE, DELTA)] = 1;
    if (tside == startB) tot[QE] += 1;
    for (int len = 1; len <= D - 1; len++) {
        memset(nxt, 0, sizeof(long long) * 2 * QN * L);
        for (int s = 0; s < 2; s++) for (int v = 0; v < QN; v++) for (int l = 0; l < L; l++) {
            long long c = cur[IX(s, v, l)]; if (!c) continue;
            for (int t = 0; t < DELTA; t++) {
                if (t == l) continue;
                int wv = s == 0 ? QT[sb[t] * QN + v] : QT[QINV[sb[t]] * QN + v];
                nxt[IX(1 - s, wv, t)] += c;
            }
        }
        long long *tmp = cur; cur = nxt; nxt = tmp;
        int side_now = (startB + len) & 1;
        if (side_now == tside) for (int v = 0; v < QN; v++) for (int l = 0; l < L; l++) tot[v] += cur[IX(side_now, v, l)];
    }
#undef IX
    int ok = 1;
    for (int v = 0; v < QN; v++) if (tot[v] < QK) { ok = 0; break; }
    free(cur); free(nxt); free(tot);
    return ok;
}

static int quotient_ok(const int *S) {
    if (!QN) return 1;
    int sb[16]; long long key = 0;
    for (int i = 0; i < DELTA; i++) { sb[i] = QMAPV[S[i]]; key = key * QN + sb[i]; }
    int res = -1;
    size_t h = (size_t)((unsigned long long)key * 0x9E3779B97F4A7C15ULL >> 17) & (QCAP - 1);
#pragma omp critical(qcache)
    {
        while (QCACHE_KEY[h] != -1 && QCACHE_KEY[h] != key) h = (h + 1) & (QCAP - 1);
        if (QCACHE_KEY[h] == key) res = QCACHE_VAL[h];
    }
    if (res < 0) {
        res = qdp_ok(sb, 0) && (D % 2 == 0 || qdp_ok(sb, 1));
#pragma omp critical(qcache)
        {
            size_t h2 = (size_t)((unsigned long long)key * 0x9E3779B97F4A7C15ULL >> 17) & (QCAP - 1);
            while (QCACHE_KEY[h2] != -1 && QCACHE_KEY[h2] != key) h2 = (h2 + 1) & (QCAP - 1);
            QCACHE_KEY[h2] = key; QCACHE_VAL[h2] = (signed char)res;
        }
    }
    return res;
}

static int cost_of(const int *S, work *w) {
    if (!quotient_ok(S)) {
#pragma omp atomic
        qfiltered++;
        return 1 << 29;
    }
    int *Lm[16], *Li[16];
    for (int i = 0; i < DELTA; i++) { Lm[i] = LM[S[i]]; Li[i] = LM[INV[S[i]]]; }
    if (D % 2 == 0) return bfs_cost(Lm, Li, 0, 0, w);
    int c = bfs_cost(Lm, Li, 0, 1, w);
    if (c > 0) return c + N;   /* do not bother with the second BFS; flag as >= N */
    return bfs_cost(Lm, Li, 1, 0, w);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: hx meta m k r DELTA D PLAN [MAXPRINT] | hx tab FILE DELTA D PLAN [MAXPRINT]\n"); return 2; }
    int ai = 1;
    if (!strcmp(argv[ai], "meta")) {
        ISMETA = 1; MM = atoi(argv[ai + 1]); KK = atoi(argv[ai + 2]); RR = atoi(argv[ai + 3]); ai += 4;
        N = MM * KK; E = 0;
        RP = malloc(sizeof(int) * KK); RP[0] = 1 % MM;
        for (int j = 1; j < KK; j++) RP[j] = (int)((long long)RP[j - 1] * RR % MM);
        if ((long long)RP[KK - 1] * RR % MM != 1 % MM) { fprintf(stderr, "r^k != 1\n"); return 2; }
    } else if (!strcmp(argv[ai], "tab")) {
        FILE *f = fopen(argv[ai + 1], "r"); if (!f) { perror("tab"); return 2; }
        if (fscanf(f, "%d %d", &N, &E) != 2) return 2;
        T = malloc(sizeof(int) * (size_t)N * N);
        for (size_t i = 0; i < (size_t)N * N; i++) if (fscanf(f, "%d", &T[i]) != 1) { fprintf(stderr, "short table\n"); return 2; }
        fclose(f); ai += 2;
    } else { fprintf(stderr, "group?\n"); return 2; }
    DELTA = atoi(argv[ai]); D = atoi(argv[ai + 1]); const char *plan = argv[ai + 2];
    int maxprint = argc > ai + 3 ? atoi(argv[ai + 3]) : 50;
    INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) { INV[x] = -1; }
    LM = malloc(sizeof(int *) * N);
    for (int x = 0; x < N; x++) { LM[x] = malloc(sizeof(int) * N); for (int g = 0; g < N; g++) { LM[x][g] = mul(x, g); if (LM[x][g] == E) INV[x] = g; } }
    for (int x = 0; x < N; x++) if (INV[x] < 0) { fprintf(stderr, "no inverse for %d\n", x); return 2; }
    /* quotient filter */
    if (ISMETA && getenv("QFILTER") && atoi(getenv("QFILTER"))) {
        QN = KK; QT = malloc(sizeof(int) * QN * QN);
        for (int x = 0; x < QN; x++) for (int y = 0; y < QN; y++) QT[x * QN + y] = (x + y) % QN;
        QMAPV = malloc(sizeof(int) * N); for (int x = 0; x < N; x++) QMAPV[x] = x % KK;
        QE = 0;
    } else if (getenv("QMAP")) {
        FILE *qf = fopen(getenv("QMAP"), "r"); if (!qf) { perror("QMAP"); return 2; }
        if (fscanf(qf, "%d", &QN) != 1) return 2;
        QT = malloc(sizeof(int) * QN * QN);
        for (int i = 0; i < QN * QN; i++) if (fscanf(qf, "%d", &QT[i]) != 1) return 2;
        QMAPV = malloc(sizeof(int) * N);
        for (int i = 0; i < N; i++) if (fscanf(qf, "%d", &QMAPV[i]) != 1) return 2;
        fclose(qf);
        QE = QMAPV[E];
    }
    if (QN) {
        if (N % QN) { fprintf(stderr, "quotient order does not divide N\n"); return 2; }
        QK = N / QN;
        QINV = malloc(sizeof(int) * QN);
        for (int x = 0; x < QN; x++) for (int y = 0; y < QN; y++) if (QT[x * QN + y] == QE) QINV[x] = y;
        QCAP = 1 << 22; QCACHE_KEY = malloc(sizeof(long long) * QCAP); QCACHE_VAL = malloc(QCAP);
        for (size_t i = 0; i < QCAP; i++) QCACHE_KEY[i] = -1;
    }
    /* read plan */
    FILE *pf = strcmp(plan, "-") ? fopen(plan, "r") : stdin; if (!pf) { perror("plan"); return 2; }
    int cap = 1024, np = 0, *P = malloc(sizeof(int) * 2 * cap);
    int a, b;
    while (fscanf(pf, "%d %d", &a, &b) == 2) { if (np == cap) { cap *= 2; P = realloc(P, sizeof(int) * 2 * cap); } P[2 * np] = a; P[2 * np + 1] = b; np++; }
    long long tested = 0, nsol = 0; int best = 1 << 30, bestS[16] = {0};
    int threads = getenv("THREADS") ? atoi(getenv("THREADS")) : 1;
#ifdef _OPENMP
    omp_set_num_threads(threads);
#endif
    (void)threads;
#pragma omp parallel
    {
        work w; w.dA = malloc(sizeof(int) * N); w.dB = malloc(sizeof(int) * N); w.q = malloc(sizeof(int) * 2 * N + 8);
        long long my_tested = 0, my_sol = 0; int my_best = 1 << 30, my_bestS[16] = {0};
#pragma omp for schedule(dynamic, 1)
        for (int pi = 0; pi < np; pi++) {
            int S[16]; S[0] = E; S[1] = P[2 * pi]; S[2] = P[2 * pi + 1];
            if (S[1] == E || S[2] == E || S[1] == S[2]) continue;
            int extra = DELTA - 3;
            if (extra < 0) continue;
            int idx[16];
            /* enumerate unordered extra elements c1 < c2 < ... from G \ {e, s1, s2} */
            for (int t = 0; t < extra; t++) idx[t] = t;   /* positions in the list of allowed elements */
            int allowed_n = N - 3;
            if (extra > 0 && allowed_n < extra) continue;
            /* map position -> element skipping e, s1, s2 */
            int skip[3] = {E, S[1], S[2]};
            /* sort skip */
            for (int u = 0; u < 3; u++) for (int v = u + 1; v < 3; v++) if (skip[v] < skip[u]) { int t = skip[u]; skip[u] = skip[v]; skip[v] = t; }
            for (;;) {
                for (int t = 0; t < extra; t++) {
                    int x = idx[t];
                    for (int u = 0; u < 3; u++) if (x >= skip[u]) x++;
                    S[3 + t] = x;
                }
                int c = cost_of(S, &w); my_tested++;
                if (c < my_best) { my_best = c; memcpy(my_bestS, S, sizeof(int) * DELTA); }
                if (c == 0) {
                    my_sol++;
#pragma omp critical
                    {
                        if (nsol + my_sol <= maxprint) { printf("SOL"); for (int t = 0; t < DELTA; t++) printf(" %d", S[t]); printf("\n"); fflush(stdout); }
                    }
                }
                if (extra == 0) break;
                /* next combination */
                int t = extra - 1;
                while (t >= 0 && idx[t] == allowed_n - extra + t) t--;
                if (t < 0) break;
                idx[t]++;
                for (int u = t + 1; u < extra; u++) idx[u] = idx[u - 1] + 1;
            }
        }
#pragma omp critical
        {
            tested += my_tested; nsol += my_sol;
            if (my_best < best) { best = my_best; memcpy(bestS, my_bestS, sizeof(int) * DELTA); }
        }
        free(w.dA); free(w.dB); free(w.q);
    }
    printf("DONE tested %lld solutions %lld best_cost %d best_set", tested, nsol, best);
    for (int t = 0; t < DELTA; t++) printf(" %d", bestS[t]);
    printf(" quotient_filtered %lld\n", qfiltered);
    return 0;
}
