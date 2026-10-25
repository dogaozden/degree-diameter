/* lns.c: large-neighbourhood search for large independent sets (partial ovoids) of E11 (q = 11).
 * Graph: vertices = the 15,984 points of E (rows of E11.map); u ~ v iff B(u,v) = 0 mod 11 and u != v.
 * A solution is a set S of pairwise non-adjacent vertices; output lines "hexpoint spreadline" (cols 1-2 of E11.map).
 *
 * Usage: lns MAP INIT SECONDS SEED OUT [BUDGET] [STRATMASK]
 *   STRATMASK bits: 1 = star (S meets N[x], x random), 2 = random 10-25 % of S,
 *                   4 = double star (S meets N[x] u N[y]), 8 = small-count vertex x (remove S meeting N(x), cnt 1..3).
 * Iteration: remove R from S; F = {v not in S : v has no neighbour in S\R} (F contains R); find a maximum independent
 * set T of G[F] by branch and bound (clique-cover bound, node budget BUDGET; anytime, never worse than R).
 * Accept (S := S\R + T) when |T| >= |R|. |S| never decreases; every increase is written to OUT.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define Q 11
#define NV 15984
#define DEG 1342
#define FMAX 512
#define W 8

static int X[NV][7];
static int hexid[NV], sline[NV];
static int *pt2v;
static int maxpt;
static uint16_t *adj;
static int deg[NV];
static int inS[NV], cnt[NV];
static int posF[NV];
static int mark[NV];
static int stamp = 1;
static double FLO = 0.10, FHI = 0.25; static int CLO = 4, CHI = 8;

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static inline int orth(int a, int b) {
    int v = X[a][0]*X[b][4] + X[a][4]*X[b][0] + X[a][1]*X[b][5] + X[a][5]*X[b][1]
          + X[a][2]*X[b][6] + X[a][6]*X[b][2] - 2*X[a][3]*X[b][3];
    v %= Q; if (v < 0) v += Q;
    return v == 0;
}

static void addv(int v) { inS[v] = 1; const uint16_t *a = adj + (size_t)v*DEG; for (int k = 0; k < deg[v]; k++) cnt[a[k]]++; }
static void remv(int v) { inS[v] = 0; const uint16_t *a = adj + (size_t)v*DEG; for (int k = 0; k < deg[v]; k++) cnt[a[k]]--; }

/* ---- exact MIS on G[F] by branch and bound with bitsets ---- */
static int F[FMAX], nf;
static uint64_t fadj[FMAX][W];
static int cur[FMAX], ncur;
static int bestF[FMAX], nbest;
static int best;
static long long nodes, budget;
static int aborted;

static inline void bset(uint64_t *P, int i) { P[i>>6] |= 1ULL << (i & 63); }
static inline void bclr(uint64_t *P, int i) { P[i>>6] &= ~(1ULL << (i & 63)); }
static int popc(const uint64_t *P) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(P[i]); return c; }

/* greedy clique cover of G[P] (cliques = pairwise orthogonal sets): an upper bound on the independence number */
static int cover_bound(const uint64_t *P) {
    uint64_t R[W]; memcpy(R, P, sizeof R);
    int k = 0;
    for (;;) {
        int v = -1;
        for (int i = 0; i < W; i++) if (R[i]) { v = i*64 + __builtin_ctzll(R[i]); break; }
        if (v < 0) break;
        uint64_t C[W], cand[W];
        memset(C, 0, sizeof C);
        bset(C, v);
        for (int i = 0; i < W; i++) cand[i] = R[i] & fadj[v][i];
        for (;;) {
            int u = -1;
            for (int i = 0; i < W; i++) if (cand[i]) { u = i*64 + __builtin_ctzll(cand[i]); break; }
            if (u < 0) break;
            bset(C, u);
            for (int i = 0; i < W; i++) cand[i] &= fadj[u][i];
        }
        for (int i = 0; i < W; i++) R[i] &= ~C[i];
        k++;
    }
    return k;
}

static void mis_rec(const uint64_t *P, int size) {
    if (aborted) return;
    if (++nodes > budget) { aborted = 1; return; }
    int np = popc(P);
    if (np == 0) {
        if (size > best) { best = size; nbest = ncur; memcpy(bestF, cur, sizeof(int)*ncur); }
        return;
    }
    if (size + cover_bound(P) <= best) return;
    int bv = -1, bd = -1;
    for (int i = 0; i < W; i++) {
        uint64_t m = P[i];
        while (m) {
            int v = i*64 + __builtin_ctzll(m); m &= m - 1;
            int d = 0;
            for (int j = 0; j < W; j++) d += __builtin_popcountll(fadj[v][j] & P[j]);
            if (d > bd) { bd = d; bv = v; }
        }
    }
    if (bd == 0) { /* P is independent: take all of it */
        int save = ncur, tot = size;
        for (int i = 0; i < W; i++) { uint64_t m = P[i]; while (m) { int v = i*64 + __builtin_ctzll(m); m &= m - 1; cur[ncur++] = v; tot++; } }
        if (tot > best) { best = tot; nbest = ncur; memcpy(bestF, cur, sizeof(int)*ncur); }
        ncur = save;
        return;
    }
    uint64_t P2[W];
    for (int j = 0; j < W; j++) P2[j] = P[j] & ~fadj[bv][j];
    bclr(P2, bv);
    cur[ncur++] = bv;
    mis_rec(P2, size + 1);
    ncur--;
    uint64_t P3[W];
    memcpy(P3, P, sizeof P3);
    bclr(P3, bv);
    mis_rec(P3, size);
}

static void writeS(const char *fn) {
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *g = fopen(tmp, "w"); if (!g) { perror("write"); return; }
    for (int v = 0; v < NV; v++) if (inS[v]) fprintf(g, "%d %d\n", hexid[v], sline[v]);
    fclose(g); rename(tmp, fn);
}
static int countS(void) { int c = 0; for (int v = 0; v < NV; v++) c += inS[v]; return c; }
static int checkS(void) {
    for (int v = 0; v < NV; v++) if (inS[v]) for (int k = 0; k < deg[v]; k++) if (inS[adj[(size_t)v*DEG + k]]) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lns MAP INIT SECONDS SEED OUT [BUDGET] [STRATMASK]\n"); return 1; }
    const char *mapf = argv[1], *initf = argv[2], *outf = argv[5];
    double secs = atof(argv[3]);
    uint64_t seed = strtoull(argv[4], 0, 10);
    budget = argc > 6 ? atoll(argv[6]) : 20000;
    int smask = argc > 7 ? atoi(argv[7]) : 15;
    if (argc > 9) { FLO = atof(argv[8]); FHI = atof(argv[9]); }
    if (argc > 11) { CLO = atoi(argv[10]); CHI = atoi(argv[11]); }
    rs ^= (seed + 1) * 0x2545F4914F6CDD1DULL;
    for (int i = 0; i < 20; i++) rnd();

    FILE *f = fopen(mapf, "r"); if (!f) { perror(mapf); return 1; }
    for (int i = 0; i < NV; i++) {
        if (fscanf(f, "%d %d", &hexid[i], &sline[i]) != 2) { fprintf(stderr, "map error at %d\n", i); return 1; }
        for (int c = 0; c < 7; c++) {
            int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "map coord error at %d\n", i); return 1; }
            x %= Q; if (x < 0) x += Q; X[i][c] = x;
        }
        if (hexid[i] > maxpt) maxpt = hexid[i];
    }
    fclose(f);
    pt2v = malloc(sizeof(int) * (maxpt + 1));
    for (int i = 0; i <= maxpt; i++) pt2v[i] = -1;
    for (int i = 0; i < NV; i++) pt2v[hexid[i]] = i;

    adj = malloc((size_t)NV * DEG * sizeof(uint16_t));
    if (!adj) return 1;
    for (int a = 0; a < NV; a++) {
        deg[a] = 0;
        for (int b = 0; b < NV; b++) if (b != a && orth(a, b)) {
            if (deg[a] >= DEG) { fprintf(stderr, "degree overflow at %d\n", a); return 1; }
            adj[(size_t)a*DEG + deg[a]++] = (uint16_t)b;
        }
    }
    { int mind = 1 << 30, maxd = 0;
      for (int a = 0; a < NV; a++) { if (deg[a] < mind) mind = deg[a]; if (deg[a] > maxd) maxd = deg[a]; }
      fprintf(stderr, "graph NV=%d degree %d..%d\n", NV, mind, maxd); }

    f = fopen(initf, "r"); if (!f) { perror(initf); return 1; }
    int p, l;
    while (fscanf(f, "%d %d", &p, &l) == 2) {
        if (p < 0 || p > maxpt || pt2v[p] < 0) { fprintf(stderr, "unknown point %d\n", p); return 1; }
        int v = pt2v[p];
        if (sline[v] != l) fprintf(stderr, "note: point %d has spread line %d (file says %d)\n", p, sline[v], l);
        if (inS[v]) continue;
        if (cnt[v] > 0) { fprintf(stderr, "start set not independent at point %d\n", p); return 1; }
        addv(v);
    }
    fclose(f);
    int curS = countS();
    if (!checkS()) { fprintf(stderr, "start set not independent\n"); return 1; }
    fprintf(stderr, "start: %d points, independent\n", curS);
    writeS(outf);
    int bestS = curS;

    static int R[NV], ML[NV], Cand[NV];
    static long long tries[4], impr[4], plat[4], fails[4];
    long long it = 0, aborts = 0, exact = 0, sumF = 0;
    double t0 = now(), tlast = t0;
    for (int v = 0; v < NV; v++) posF[v] = -1;
    int opts[4], nopt = 0;
    if (smask & 1) opts[nopt++] = 0;
    if (smask & 2) opts[nopt++] = 1;
    if (smask & 4) opts[nopt++] = 2;
    if (smask & 8) opts[nopt++] = 3;
    if (nopt == 0) { fprintf(stderr, "no strategy enabled\n"); return 1; }

    while (now() - t0 < secs) {
        it++;
        int s = opts[rndint(nopt)];
        int nR = 0;
        if (s == 0) {
            int x = rndint(NV);
            if (inS[x]) R[nR++] = x;
            const uint16_t *a = adj + (size_t)x*DEG;
            for (int k = 0; k < deg[x]; k++) if (inS[a[k]]) R[nR++] = a[k];
        } else if (s == 1) {
            int m = 0;
            for (int v = 0; v < NV; v++) if (inS[v]) ML[m++] = v;
            double frac = FLO + (FHI - FLO) * (double)(rnd() % 1000000) / 1e6;
            int k = (int)(frac * m + 0.5); if (k < 1) k = 1;
            for (int i = 0; i < k; i++) { int j = i + rndint(m - i); int t = ML[i]; ML[i] = ML[j]; ML[j] = t; R[nR++] = ML[i]; }
        } else if (s == 2) {
            stamp++;
            int cs[2] = { rndint(NV), rndint(NV) };
            for (int c = 0; c < 2; c++) {
                int z = cs[c];
                if (inS[z] && mark[z] != stamp) { mark[z] = stamp; R[nR++] = z; }
                const uint16_t *a = adj + (size_t)z*DEG;
                for (int k = 0; k < deg[z]; k++) { int u = a[k]; if (inS[u] && mark[u] != stamp) { mark[u] = stamp; R[nR++] = u; } }
            }
        } else {
            int nc = 0;
            for (int v = 0; v < NV; v++) if (!inS[v] && cnt[v] >= CLO && cnt[v] <= CHI) Cand[nc++] = v;
            if (nc == 0) continue;
            int x = Cand[rndint(nc)];
            const uint16_t *a = adj + (size_t)x*DEG;
            for (int k = 0; k < deg[x]; k++) if (inS[a[k]]) R[nR++] = a[k];
        }
        if (nR == 0) continue;
        tries[s]++;
        for (int i = 0; i < nR; i++) remv(R[i]);
        nf = 0; int overflow = 0;
        for (int v = 0; v < NV; v++) if (!inS[v] && cnt[v] == 0) { if (nf >= FMAX) { overflow = 1; break; } F[nf++] = v; }
        if (overflow) {
            for (int i = 0; i < nR; i++) addv(R[i]);
            fails[s]++;
            continue;
        }
        for (int i = nf - 1; i > 0; i--) { int j = rndint(i + 1); int t = F[i]; F[i] = F[j]; F[j] = t; }
        for (int i = 0; i < nf; i++) posF[F[i]] = i;
        for (int i = 0; i < nf; i++) {
            memset(fadj[i], 0, sizeof fadj[i]);
            const uint16_t *a = adj + (size_t)F[i]*DEG;
            for (int k = 0; k < deg[F[i]]; k++) { int j = posF[a[k]]; if (j >= 0) bset(fadj[i], j); }
        }
        best = nR - 1; nbest = 0; nodes = 0; aborted = 0; ncur = 0;
        uint64_t P[W]; memset(P, 0, sizeof P);
        for (int i = 0; i < nf; i++) bset(P, i);
        mis_rec(P, 0);
        sumF += nf;
        if (aborted) aborts++; else exact++;
        for (int i = 0; i < nf; i++) posF[F[i]] = -1;
        if (nbest >= nR) {
            for (int i = 0; i < nbest; i++) addv(F[bestF[i]]);
            curS += nbest - nR;
            if (nbest > nR) impr[s]++; else plat[s]++;
        } else {
            for (int i = 0; i < nR; i++) addv(R[i]);
        }
        if (curS > bestS) {
            bestS = curS;
            writeS(outf);
            fprintf(stderr, "t=%.1f it=%lld IMPROVED S=%d (valid=%d)\n", now() - t0, it, curS, checkS());
        }
        if (now() - tlast > 15) {
            tlast = now();
            fprintf(stderr, "t=%.0f it=%lld S=%d best=%d avgF=%.1f exact=%lld aborts=%lld  per-strategy tries/impr/plateau/overflow: %lld/%lld/%lld/%lld %lld/%lld/%lld/%lld %lld/%lld/%lld/%lld %lld/%lld/%lld/%lld\n",
                    now() - t0, it, curS, bestS, (double)sumF / (it > 0 ? it : 1), exact, aborts,
                    tries[0], impr[0], plat[0], fails[0], tries[1], impr[1], plat[1], fails[1],
                    tries[2], impr[2], plat[2], fails[2], tries[3], impr[3], plat[3], fails[3]);
        }
    }
    int ok = checkS();
    writeS(outf);
    fprintf(stderr, "done: it=%lld exact=%lld aborts=%lld final S=%d best=%d independent=%d\n", it, exact, aborts, curS, bestS, ok);
    printf("best %d valid_indep %d out %s\n", bestS, ok, outf);
    return ok ? 0 : 2;
}
