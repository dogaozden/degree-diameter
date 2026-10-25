/* flagls.c: simulated-annealing local search over a set of K freed flags (p_i on l_i, distinct points, distinct lines).
 * Cost = N - (maximum matching of the exact-coverage bipartite graph), exactly as flaggreedy.py matching() defines it
 * (allowed (x, M): for each flag, x in A_i (collinear with p_i, not on l_i) => M meets l_i; M in G_i (meets l_i, not
 * through p_i) => x collinear with p_i; freed points are forced to their lines, freed lines are unavailable).
 * Matching: Kuhn with bitsets, warm-started from the matching of the current state.
 * usage: flagls GQBIN K OUT   env: SEED, ITERS (default 4e6), T0 (1.0), T1 (0.1), CYC (cooling cycle, default 400000),
 *   SECS (wall limit, default 1e9), PL (prob. of moving a flag's line, 0.4), PP (prob. of moving its point, 0.4),
 *   INIT ("p:l p:l ..." full starting set), EVAL=1 (print the cost of INIT and exit).
 * On cost 0 writes OUT: "FLAGS k p:l ...\nSIGMA s_0 ... s_{N-1}\n" and exits.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 512
#define MAXW 8
#define MAXK 16
typedef uint64_t u64;

static int q, N, Q1, W;
static int *ln, *lo;                                  /* ln[l*Q1+k]: points on l; lo[p*Q1+k]: lines through p */
static u64 Pm[MAXN][MAXW], Lm[MAXN][MAXW], onl[MAXN][MAXW], thr[MAXN][MAXW], LlB[MAXN][MAXW], PpB[MAXN][MAXW];
static u64 ALLW[MAXW];
static u64 Adj[MAXN][MAXW];
static int Fo[MAXN];                                  /* forced line of a freed point, -1 otherwise */
static u64 visited[MAXW];
static uint64_t rs = 88172645463325252ULL;

static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int getb(const u64 *s, int i) { return (s[i >> 6] >> (i & 63)) & 1; }
static inline void setb(u64 *s, int i) { s[i >> 6] |= 1ULL << (i & 63); }
static inline void clrb(u64 *s, int i) { s[i >> 6] &= ~(1ULL << (i & 63)); }

typedef struct { int k; int fp[MAXK], fl[MAXK]; } FlagSet;
typedef struct { int mL[MAXN], mR[MAXN]; } Match;

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); int32_t h[3];
    if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "no gq file\n"); exit(1); }
    q = h[0]; N = h[1]; int L = h[2]; Q1 = q + 1; W = (N + 63) / 64;
    if (N > MAXN || W > MAXW) { fprintf(stderr, "N too large\n"); exit(1); }
    ln = malloc(sizeof(int) * L * Q1);
    for (int l = 0; l < L; l++) { int32_t t[16]; if (fread(t, 4, Q1, f) != (size_t)Q1) exit(1); for (int k = 0; k < Q1; k++) ln[l * Q1 + k] = t[k]; }
    fclose(f);
    lo = malloc(sizeof(int) * N * Q1); int *dg = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int k = 0; k < Q1; k++) { int p = ln[l * Q1 + k]; lo[p * Q1 + dg[p]++] = l; }
    free(dg);
    for (int x = 0; x < N; x++) setb(ALLW, x);
    for (int p = 0; p < N; p++) for (int k = 0; k < Q1; k++) {
        int l = lo[p * Q1 + k]; setb(thr[p], l);
        for (int j = 0; j < Q1; j++) setb(Pm[p], ln[l * Q1 + j]);
    }
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = ln[l * Q1 + k]; setb(onl[l], p);
        for (int j = 0; j < Q1; j++) setb(Lm[l], lo[p * Q1 + j]);
    }
    for (int p = 0; p < N; p++) { memcpy(PpB[p], Pm[p], sizeof(PpB[p])); clrb(PpB[p], p); }
    for (int l = 0; l < N; l++) { memcpy(LlB[l], Lm[l], sizeof(LlB[l])); clrb(LlB[l], l); }
}

/* allowed bipartite graph for a flag set; Adj[x] = allowed lines for point x (forced for freed points) */
static void build_adj(const FlagSet *fs) {
    static u64 lineok[MAXN][MAXW], ptok[MAXN][MAXW];
    u64 Fm[MAXW] = {0}, Flm[MAXW] = {0};
    for (int x = 0; x < N; x++) Fo[x] = -1;
    for (int i = 0; i < fs->k; i++) { setb(Fm, fs->fp[i]); setb(Flm, fs->fl[i]); Fo[fs->fp[i]] = fs->fl[i]; }
    for (int x = 0; x < N; x++) for (int w = 0; w < W; w++) lineok[x][w] = ALLW[w] & ~Flm[w];
    for (int M = 0; M < N; M++) for (int w = 0; w < W; w++) ptok[M][w] = ALLW[w] & ~Fm[w];
    for (int i = 0; i < fs->k; i++) {
        int p = fs->fp[i], l = fs->fl[i];
        u64 A[MAXW], G[MAXW];
        for (int w = 0; w < W; w++) { A[w] = Pm[p][w] & ~onl[l][w]; G[w] = Lm[l][w] & ~thr[p][w]; }
        for (int x = 0; x < N; x++) if (getb(A, x)) for (int w = 0; w < W; w++) lineok[x][w] &= LlB[l][w];
        for (int M = 0; M < N; M++) if (getb(G, M)) for (int w = 0; w < W; w++) ptok[M][w] &= PpB[p][w];
    }
    for (int x = 0; x < N; x++) {
        for (int w = 0; w < W; w++) Adj[x][w] = 0;
        if (Fo[x] >= 0) { setb(Adj[x], Fo[x]); continue; }
        for (int M = 0; M < N; M++) if (getb(lineok[x], M) && getb(ptok[M], x)) setb(Adj[x], M);
    }
}

static int dfs(int u, Match *m) {
    for (int M = 0; M < N; M++) {
        if (!getb(Adj[u], M) || getb(visited, M)) continue;
        setb(visited, M);
        if (m->mR[M] < 0 || dfs(m->mR[M], m)) { m->mR[M] = u; m->mL[u] = M; return 1; }
    }
    return 0;
}

/* maximum matching warm-started from old (may be NULL): forced flags first, then old edges still allowed, then Kuhn */
static int match_warm(Match *m, const Match *old, const FlagSet *fs) {
    for (int x = 0; x < N; x++) { m->mL[x] = -1; m->mR[x] = -1; }
    for (int i = 0; i < fs->k; i++) { m->mL[fs->fp[i]] = fs->fl[i]; m->mR[fs->fl[i]] = fs->fp[i]; }
    if (old) for (int x = 0; x < N; x++) if (Fo[x] < 0 && old->mL[x] >= 0) {
        int M = old->mL[x];
        if (getb(Adj[x], M) && m->mR[M] < 0) { m->mL[x] = M; m->mR[M] = x; }
    }
    int cnt = 0;
    for (int x = 0; x < N; x++) {
        if (m->mL[x] >= 0) { cnt++; continue; }
        memset(visited, 0, sizeof visited);
        if (dfs(x, m)) cnt++;
    }
    return cnt;
}

static void random_flags(FlagSet *fs, int K) {
    fs->k = 0;
    while (fs->k < K) {
        int p = rnd() % N, l = lo[p * Q1 + rnd() % Q1];
        int ok = 1;
        for (int i = 0; i < fs->k; i++) if (fs->fp[i] == p || fs->fl[i] == l) ok = 0;
        if (ok) { fs->fp[fs->k] = p; fs->fl[fs->k] = l; fs->k++; }
    }
}

static int propose(const FlagSet *cur, FlagSet *prop, double PL, double PP) {
    *prop = *cur;
    int i = rnd() % cur->k;
    int p = cur->fp[i], l = cur->fl[i], np = p, nl = l;
    double r = urand();
    if (r < PL) nl = lo[p * Q1 + rnd() % Q1];
    else if (r < PL + PP) np = ln[l * Q1 + rnd() % Q1];
    else { np = rnd() % N; nl = lo[np * Q1 + rnd() % Q1]; }
    if (np == p && nl == l) return 0;
    for (int j = 0; j < cur->k; j++) if (j != i && (cur->fp[j] == np || cur->fl[j] == nl)) return 0;
    prop->fp[i] = np; prop->fl[i] = nl;
    return 1;
}

static void print_flags(FILE *f, const FlagSet *fs) {
    fprintf(f, "FLAGS %d", fs->k);
    for (int i = 0; i < fs->k; i++) fprintf(f, " %d:%d", fs->fp[i], fs->fl[i]);
    fprintf(f, "\n");
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: flagls GQBIN K OUT\n"); return 1; }
    load(argv[1]);
    int K = atoi(argv[2]); const char *OUT = argv[3];
    if (K < 1 || K > MAXK) { fprintf(stderr, "bad K\n"); return 1; }
    for (int x = 0; x < N; x++) setb(ALLW, x);
    rs ^= (getenv("SEED") ? strtoull(getenv("SEED"), 0, 10) : 1) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    long iters = getenv("ITERS") ? atol(getenv("ITERS")) : 4000000;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.1;
    long CYC = getenv("CYC") ? atol(getenv("CYC")) : 400000;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 1e9;
    double PL = getenv("PL") ? atof(getenv("PL")) : 0.4, PP = getenv("PP") ? atof(getenv("PP")) : 0.4;

    FlagSet cur, prop, best;
    if (getenv("INIT")) {
        char *s = getenv("INIT"), *e; cur.k = 0;
        for (;;) {
            long p = strtol(s, &e, 10); if (e == s) break;
            long l = strtol(e + 1, &e, 10);
            cur.fp[cur.k] = (int)p; cur.fl[cur.k] = (int)l; cur.k++; s = e;
            while (*s == ' ' || *s == ',') s++;
        }
        K = cur.k;
    } else random_flags(&cur, K);
    build_adj(&cur);
    Match curM, newM;
    int curC = N - match_warm(&curM, NULL, &cur);
    if (getenv("EVAL")) { printf("EVAL k %d cost %d (deficiency)\n", cur.k, curC); return 0; }
    best = cur; int bestC = curC;
    struct timespec t0; clock_gettime(CLOCK_MONOTONIC, &t0);
    long it, acc = 0;
    for (it = 0; it < iters && curC > 0; it++) {
        if ((it & 4095) == 0) {
            struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
            if ((ts.tv_sec - t0.tv_sec) + 1e-9 * (ts.tv_nsec - t0.tv_nsec) > secs) break;
        }
        double T = T0 * pow(T1 / T0, (double)(it % CYC) / (double)CYC);
        if (!propose(&cur, &prop, PL, PP)) continue;
        build_adj(&prop);
        int c2 = N - match_warm(&newM, &curM, &prop);
        int d = c2 - curC;
        if (d <= 0 || urand() < exp(-d / T)) {
            cur = prop; curM = newM; curC = c2; acc++;
            if (curC < bestC) {
                bestC = curC; best = cur;
                fprintf(stderr, "it %ld T %.3f best deficiency %d\n", it, T, bestC);
            }
        }
    }
    printf("RESULT k %d iters %ld accepted %ld best deficiency %d\n", K, it, acc, bestC);
    if (curC == 0) {
        FILE *f = fopen(OUT, "w");
        print_flags(f, &cur);
        fprintf(f, "SIGMA");
        for (int x = 0; x < N; x++) fprintf(f, " %d", curM.mL[x]);
        fprintf(f, "\n"); fclose(f);
        printf("FOUND perfect matching, wrote %s\n", OUT);
        print_flags(stdout, &cur);
    } else {
        print_flags(stdout, &best);
    }
    return 0;
}
