/* gsym.c (r3d): generic G-invariant polarity-cover search.
   M = symmetric 0/1 matrix on m vertices (loops allowed, each counted once, row sums 3), invariant under a
   permutation group G (given by generators). State = list of edge-orbit representatives; the graph is the union of
   their G-orbits; a state is valid iff the union is 3-regular (loops count once) and simple.
   Cover G: A_i ~ B_j iff M_ij = 1; n = 2m. Cost = far of the cover = sum over ALL vertices i of (c_i + x_i), where
     c_i = #{j != i : no even walk <= 6 from i to j}, x_i = #{j : no odd walk <= 7 from i to j}.
   Usage: gsym GENFILE m seed seconds T0 T1 sweeps outprefix [init.edges|-] [pert]
     GENFILE: first line = number of generators g; then g lines of m integers (images of 0..m-1).
     Writes outprefix_best.reps (orbit reps) and outprefix_best.edges (cover edge list) on improvement.
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXM 128
#define MAXG 256
#define MAXR 512

typedef struct { uint64_t w[2]; } BS;
static int m, NG;
static double pvolt = 0.3;
static int useX = 1;
static double ploop = 0.05;
static long nsinv, nsval;
static int G[MAXG][MAXM];   /* group elements */
static int nG;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static inline int bit(const BS *b, int i) { return (b->w[i >> 6] >> (i & 63)) & 1; }
static inline void bset(BS *b, int i) { b->w[i >> 6] |= 1ULL << (i & 63); }
static inline int pc(const BS *b) { return __builtin_popcountll(b->w[0]) + __builtin_popcountll(b->w[1]); }
static inline void bor(BS *a, const BS *b) { a->w[0] |= b->w[0]; a->w[1] |= b->w[1]; }
static void orset(BS *out, const BS *src, const BS *R) {
    BS r = {{0, 0}};
    for (int w = 0; w < 2; w++) { uint64_t x = src->w[w]; while (x) { int i = __builtin_ctzll(x) + 64 * w; bor(&r, &R[i]); x &= x - 1; } }
    *out = r;
}

typedef struct { int p, q; } Rep;
typedef struct { Rep r[MAXR]; int n; } St;

/* union graph of the reps; returns 1 if it is simple-enough and 3-regular */
static int build(const St *s, BS *N, int *deg) {
    memset(N, 0, sizeof(BS) * m);
    for (int v = 0; v < m; v++) deg[v] = 0;
    for (int i = 0; i < s->n; i++) {
        for (int g = 0; g < nG; g++) {
            int a = G[g][s->r[i].p], b = G[g][s->r[i].q];
            if (bit(&N[a], b)) continue;          /* already present (same edge from another image) */
            bset(&N[a], b); bset(&N[b], a);
            if (a == b) { deg[a] += 1; } else { deg[a]++; deg[b]++; }
        }
    }
    return 1;
}
static int valid(const St *s, BS *N) {
    int deg[MAXM];
    build(s, N, deg);
    for (int v = 0; v < m; v++) if (deg[v] != 3) return 0;
    return 1;
}
/* far = sum over all sources i of c_i + x_i */
static int cost(const BS *N) {
    static BS R2[MAXM];
    for (int v = 0; v < m; v++) orset(&R2[v], &N[v], N);
    BS mask = {{0, 0}};
    for (int i = 0; i < m; i++) bset(&mask, i);
    long far = 0;
    for (int src = 0; src < m; src++) {
        BS R2s = R2[src], R4s, R6s, O3, O5, O7;
        orset(&R4s, &R2s, R2);
        orset(&R6s, &R4s, R2);
        BS E = R2s; bor(&E, &R4s); bor(&E, &R6s); bset(&E, src);
        int c = m - pc(&E);
        orset(&O3, &N[src], R2);
        orset(&O5, &O3, R2);
        orset(&O7, &O5, R2);
        BS Od = N[src]; bor(&Od, &O3); bor(&Od, &O5); bor(&Od, &O7);
        int x = m - pc(&Od);
        far += c + (useX ? x : 0);
    }
    return (int)far;
}

static void write_reps(const St *s, const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) return;
    for (int i = 0; i < s->n; i++) fprintf(f, "%d %d\n", s->r[i].p, s->r[i].q);
    fclose(f);
}
static void write_cover(const BS *N, const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) return;
    fprintf(f, "%d\n", 2 * m);
    for (int i = 0; i < m; i++) for (int j = i; j < m; j++) if (bit(&N[i], j)) {
        if (i == j) fprintf(f, "%d %d\n", i, m + i);
        else { fprintf(f, "%d %d\n", i, m + j); fprintf(f, "%d %d\n", j, m + i); }
    }
    fclose(f);
}

/* random greedy G-invariant cubic graph */
static int init_random(St *s, BS *N) {
    for (int attempt = 0; attempt < 2000; attempt++) {
        s->n = 0;
        int deg[MAXM]; memset(deg, 0, sizeof deg);
        int stuck = 0;
        while (stuck < 400) {
            int v = rndi(m), w = rndi(m);
            if (deg[v] >= 3 || deg[w] >= 3) { stuck++; continue; }
            if (v == w && rndu() < 0.5) { stuck++; continue; }
            St t = *s;
            t.r[t.n].p = v; t.r[t.n].q = w; t.n++;
            BS NN[MAXM]; int dd[MAXM];
            build(&t, NN, dd);
            int ok = 1;
            for (int u = 0; u < m; u++) if (dd[u] > 3) { ok = 0; break; }
            if (!ok) { stuck++; continue; }
            *s = t;
            memcpy(N, NN, sizeof(BS) * m);
            for (int u = 0; u < m; u++) deg[u] = dd[u];
            int full = 1; for (int u = 0; u < m; u++) if (deg[u] != 3) { full = 0; break; }
            if (full) return 1;
            stuck = 0;
        }
    }
    return 0;
}



/* sampled best-improvement tabu (env TABU=K samples per step, TTEN=tenure in steps) */
static int run_tabu(St *cur0, BS *N0, int K, int tten, double secs, double t0, int *bestS_io, St *best_io, BS *Nb_io, const char *outp) {
    static long tabu_until[MAXR];
    static St cs, cand, bestc;
    static BS cN[MAXM], candN[MAXM], bestN[MAXM];
    cs = *cur0; memcpy(cN, N0, sizeof(BS) * m);
    int curS = cost(cN);
    bestc = cs; memcpy(bestN, cN, sizeof(BS) * m);
    int bestS = curS;
    char fn[512];
    long step = 0;
    for (int r = 0; r < MAXR; r++) tabu_until[r] = 0;
    while (now() - t0 < secs && bestS > 0) {
        step++;
        int bi = -1; St bestMove; int bestMoveS = INT_MAX; BS bestMoveN[MAXM];
        for (int s = 0; s < K; s++) {
            cand = cs;
            int idx;
            double r = rndu();
            if (r < 0.5 || cs.n < 2) {   /* 2-switch on two reps */
                int i = rndi(cs.n), j = rndi(cs.n);
                if (i == j) continue;
                if (tabu_until[i] > step || tabu_until[j] > step) continue;
                int a = cand.r[i].p, b = cand.r[i].q, c = cand.r[j].p, d = cand.r[j].q;
                if (rnd() & 1) { int tt = c; c = d; d = tt; }
                cand.r[i].p = a; cand.r[i].q = G[rndi(nG)][c]; cand.r[j].p = b; cand.r[j].q = G[rndi(nG)][d];
                idx = i;
                if (!valid(&cand, candN)) continue;
            } else {                      /* voltage move on one rep */
                int i = rndi(cs.n);
                if (tabu_until[i] > step) continue;
                int g = rndi(nG);
                if (rnd() & 1) cand.r[i].q = G[g][cs.r[i].q]; else cand.r[i].p = G[g][cs.r[i].p];
                idx = i;
                if (!valid(&cand, candN)) continue;
            }
            int Sc = cost(candN);
            if (Sc < bestMoveS) {
                bestMoveS = Sc; bi = idx; bestMove = cand; memcpy(bestMoveN, candN, sizeof(BS) * m);
            }
        }
        if (bi < 0) continue;
        cs = bestMove; memcpy(cN, bestMoveN, sizeof(BS) * m); curS = bestMoveS;
        tabu_until[bi] = step + tten;
        if (curS < bestS) {
            bestS = curS; bestc = cs; memcpy(bestN, cN, sizeof(BS) * m);
            printf("tabu improve far=%d (step %ld, %.1fs)\n", bestS, step, now() - t0); fflush(stdout);
            snprintf(fn, sizeof fn, "%s_best.reps", outp); write_reps(&bestc, fn);
            snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(bestN, fn);
        }
    }
    *bestS_io = bestS; *best_io = bestc; memcpy(Nb_io, bestN, sizeof(BS) * m);
    printf("tabu steps %ld\n", step);
    return bestS;
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: gsym GENFILE m seed seconds T0 T1 sweeps outprefix [init.reps|-] [pert]\n"); return 1; }
    m = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], 0, 10);
    double secs = atof(argv[4]), T0 = atof(argv[5]), T1 = atof(argv[6]);
    long sweeps = atol(argv[7]);
    const char *outp = argv[8];
    /* read generators */
    FILE *gf = fopen(argv[1], "r");
    if (!gf) { perror(argv[1]); return 1; }
    int ng; if (fscanf(gf, "%d", &ng) != 1) return 1;
    static int gen[16][MAXM];
    for (int i = 0; i < ng; i++) for (int v = 0; v < m; v++) if (fscanf(gf, "%d", &gen[i][v]) != 1) return 1;
    fclose(gf);
    /* group closure by BFS on permutations */
    nG = 0;
    for (int v = 0; v < m; v++) G[0][v] = v; nG = 1;
    for (int qi = 0; qi < nG; qi++) {
        for (int i = 0; i < ng; i++) {
            int tmp[MAXM];
            for (int v = 0; v < m; v++) tmp[v] = gen[i][G[qi][v]];
            int found = 0;
            for (int h = 0; h < nG && !found; h++) if (memcmp(G[h], tmp, sizeof(int) * m) == 0) found = 1;
            if (!found) {
                if (nG >= MAXG) { fprintf(stderr, "group too big\n"); return 1; }
                memcpy(G[nG], tmp, sizeof(int) * m); nG++;
            }
        }
    }
    if (getenv("PVOLT")) pvolt = atof(getenv("PVOLT"));
    if (getenv("NOX")) useX = 0;
    if (getenv("PLOOP")) ploop = atof(getenv("PLOOP"));
    printf("group order %d\n", nG);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    static St cur, best, nxt;
    static BS N[MAXM], Nn[MAXM], Nb[MAXM];
    int bestS = INT_MAX;
    int pert = (argc > 10) ? atoi(argv[10]) : 0;
    if (argc > 9 && strcmp(argv[9], "-") != 0) {
        FILE *rf = fopen(argv[9], "r");
        if (!rf) { perror(argv[9]); return 1; }
        cur.n = 0; int a, b;
        while (fscanf(rf, "%d %d", &a, &b) == 2) { cur.r[cur.n].p = a; cur.r[cur.n].q = b; cur.n++; }
        fclose(rf);
        if (!valid(&cur, N)) { fprintf(stderr, "init reps not valid\n"); return 1; }
    } else {
        if (!init_random(&cur, N)) { fprintf(stderr, "init failed\n"); return 1; }
    }
    if (getenv("TABU")) {
        int K = atoi(getenv("TABU")), tten = getenv("TTEN") ? atoi(getenv("TTEN")) : 8;
        static St bst; static BS Nbb[MAXM]; int bS = INT_MAX;
        int s0 = cost(N);
        printf("start far=%d\n", s0);
        run_tabu(&cur, N, K, tten, secs, now(), &bS, &bst, Nbb, outp);
        printf("done tabu best far=%d\n", bS);
        return 0;
    }
    double t0 = now();
    int restarts = 0, firstRound = 1;
    long totalIt = 0, accepted = 0, tried = 0;
    char fn[512];
    int S = cost(N);
    while (now() - t0 < secs) {
        if (!firstRound) {
            if (pert > 0 && bestS < INT_MAX) {
                cur = best;
                for (int p = 0; p < pert; p++) {
                    St tmp = cur;
                    int i = rndi(tmp.n), j = rndi(tmp.n);
                    if (i == j) continue;
                    int a = tmp.r[i].p, b = tmp.r[i].q, c = tmp.r[j].p, d = tmp.r[j].q;
                    if (rnd() & 1) { int tt = c; c = d; d = tt; }
                    tmp.r[i].p = a; tmp.r[i].q = c; tmp.r[j].p = b; tmp.r[j].q = d;
                    BS NN[MAXM]; if (valid(&tmp, NN)) cur = tmp;
                }
            } else {
                if (!init_random(&cur, N)) break;
            }
            valid(&cur, N);
            S = cost(N);
        }
        firstRound = 0;
        for (long it = 0; it < sweeps; it++) {
            double T = T0 * pow(T1 / T0, (double)it / (double)(sweeps > 1 ? sweeps - 1 : 1));
            totalIt++;
            if (cur.n < 2) break;
            int i = rndi(cur.n), j = rndi(cur.n);
            if (rndu() < pvolt) {   /* voltage move: re-choose one endpoint of a rep inside its base-orbit pair */
                nxt = cur;
                int g = rndi(nG);
                if (rnd() & 1) nxt.r[i].q = G[g][cur.r[i].q]; else nxt.r[i].p = G[g][cur.r[i].p];
                tried++;
                if (!valid(&nxt, Nn)) continue;
                int S2 = cost(Nn);
                int dd = S2 - S;
                if (dd <= 0 || rndu() < exp(-dd / T)) {
                    cur = nxt; S = S2; memcpy(N, Nn, sizeof(BS) * m); accepted++;
                    if (S < bestS) {
                        bestS = S; best = cur; memcpy(Nb, N, sizeof(BS) * m);
                        snprintf(fn, sizeof fn, "%s_best.reps", outp); write_reps(&best, fn);
                        snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(Nb, fn);
                        printf("improve far=%d (restart %d, it %ld, %.1fs)\n", bestS, restarts, it, now() - t0);
                        fflush(stdout);
                        if (bestS == 0) goto done;
                    }
                }
                continue;
            }
            if (i == j) continue;
            if (rndu() < ploop) {   /* loop moves: (p,p)+(q,q) <-> edge (p,q) (loops carry one stub each) */
                nxt = cur;
                if (cur.r[i].p == cur.r[i].q && cur.r[j].p == cur.r[j].q) {
                    int p = cur.r[i].p, q = G[rndi(nG)][cur.r[j].p];
                    nxt.r[i].p = p; nxt.r[i].q = q;
                    nxt.r[j] = nxt.r[nxt.n - 1]; nxt.n--;
                } else if (cur.r[i].p != cur.r[i].q && cur.n < MAXR - 1) {
                    int p = cur.r[i].p, q = cur.r[i].q;
                    nxt.r[i].p = p; nxt.r[i].q = p;
                    nxt.r[nxt.n].p = q; nxt.r[nxt.n].q = q; nxt.n++;
                } else continue;
                tried++;
                if (!valid(&nxt, Nn)) { nsinv++; continue; }
                nsval++;
                int S2 = cost(Nn);
                int dd = S2 - S;
                if (dd <= 0 || rndu() < exp(-dd / T)) {
                    cur = nxt; S = S2; memcpy(N, Nn, sizeof(BS) * m); accepted++;
                    if (S < bestS) {
                        bestS = S; best = cur; memcpy(Nb, N, sizeof(BS) * m);
                        snprintf(fn, sizeof fn, "%s_best.reps", outp); write_reps(&best, fn);
                        snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(Nb, fn);
                        printf("improve far=%d (restart %d, it %ld, %.1fs)\n", bestS, restarts, it, now() - t0);
                        fflush(stdout);
                        if (bestS == 0) goto done;
                    }
                }
                continue;
            }
            nxt = cur;
            int a = nxt.r[i].p, b = nxt.r[i].q, c = nxt.r[j].p, d = nxt.r[j].q;
            if (rnd() & 1) { int tt = c; c = d; d = tt; }
            /* orbit-level 2-switch with random group elements on the new endpoints (keeps stub balance) */
            int g1 = rndi(nG), g2 = rndi(nG);
            nxt.r[i].p = a; nxt.r[i].q = G[g1][c]; nxt.r[j].p = b; nxt.r[j].q = G[g2][d];
            tried++;
            if (!valid(&nxt, Nn)) continue;
            int S2 = cost(Nn);
            int dd = S2 - S;
            if (dd <= 0 || rndu() < exp(-dd / T)) {
                cur = nxt; S = S2; memcpy(N, Nn, sizeof(BS) * m); accepted++;
                if (S < bestS) {
                    bestS = S; best = cur; memcpy(Nb, N, sizeof(BS) * m);
                    snprintf(fn, sizeof fn, "%s_best.reps", outp); write_reps(&best, fn);
                    snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(Nb, fn);
                    printf("improve far=%d (restart %d, it %ld, %.1fs)\n", bestS, restarts, it, now() - t0);
                    fflush(stdout);
                    if (bestS == 0) goto done;
                }
            }
            if ((it & 0x3FFF) == 0 && now() - t0 > secs) break;
        }
        restarts++;
    }
done:
    printf("done: group %d restarts=%d iters=%ld tried=%ld accepted=%ld best far=%d time=%.1fs\n",
           nG, restarts, totalIt, tried, accepted, bestS, now() - t0);
    return 0;
}
