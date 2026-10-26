/* flift: fast annealer for voltage lifts of a small base multigraph over a group table (big-squad-4-8 job).
   Same problem as lift.c, but voltages act by LEFT multiplication: an edge (u, v, g) of the base gives the lift edges
   (u, x) ~ (v, g*x). (Isomorphic to lift.c's convention via x -> x^-1.) G acts by right multiplication, transitively
   on each fibre, so the eccentricities of the b vertices (u, e) give the diameter.
   Speed: elements are stored as left cosets of a cyclic subgroup H = <h> (|H| <= 64): x = rep_r * h^t is bit t of
   row r. Left multiplication by g maps row r to a row r' with a rotation: g*rep_r = rep_r' * h^j. One BFS level is
   (darts x rows) word operations.

   Usage: flift BASE GROUP d D seconds seed [K] [OUT]      (BASE and GROUP as for lift.c; GROUP: table .bin, or meta:m:k:r)
          flift BASE GROUP d D eval < VOLTAGES             (one line per assignment, m indices in BASE edge order;
                                                            env LIMIT=c aborts counting above c; ONLYLOW=1 prints only
                                                            assignments with cost <= LIMIT, and the minimum on stderr)
   Env: T0 (3), T1 (0.05), EPOCH (20000), NOTREE, QUIET, HMAX (64).
   Cost = sum over base vertices u of the number of lift vertices farther than D from (u, e). Bipartiteness is not
   checked (use a bipartite base). OUT gets the best state and OUT.edges the lift edge list ((v, x) = v*N + x, edges
   (u,x)-(v, g*x)); check it with score48. Loops and semi-edges are not supported. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 64
#define MAXE 256
#define MAXR 4096
static int b, m, N, d, D, K = 8;
static uint16_t *MT; static int *INV;
static int eu[MAXE], ev[MAXE], efix[MAXE], volt[MAXE], bestv[MAXE], nfree, freeidx[MAXE];
static int ndart[MAXB], dto[MAXB][32], dedge[MAXB][32], dinv[MAXB][32];
static int nH, R, *REP, *POS;            /* POS[x] = r*64 + t */
static uint64_t HMASK;
static int16_t *RMAP; static int8_t *ROT;   /* per element g: RMAP[g*R + r], ROT[g*R + r] */
static uint64_t *F, *NF, *V;             /* [b][R] */
static long long evals;
static char gspec[256];
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int mul(int x, int y) { return MT[(size_t)x * N + y]; }

static void load_group(const char *s) {
    snprintf(gspec, sizeof gspec, "%s", s);
    if (!strncmp(s, "meta:", 5)) {
        int mm, k, r; if (sscanf(s + 5, "%d:%d:%d", &mm, &k, &r) != 3) exit(2);
        N = mm * k; MT = malloc((size_t)N * N * 2);
        long *rp = malloc(k * sizeof(long)); rp[0] = 1 % mm; for (int j = 1; j < k; j++) rp[j] = rp[j - 1] * r % mm;
        for (int j = 0; j < k; j++) for (int a = 0; a < mm; a++) for (int l = 0; l < k; l++) for (int bb = 0; bb < mm; bb++)
            MT[(size_t)(a + mm * j) * N + bb + mm * l] = (uint16_t)((a + rp[j] * bb) % mm + mm * ((j + l) % k));
    } else {
        FILE *f = fopen(s, "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) { fprintf(stderr, "cannot read %s\n", s); exit(2); }
        N = n32; MT = malloc((size_t)N * N * 2); if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) exit(2); fclose(f);
    }
    INV = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int h = 0; h < N; h++) if (MT[(size_t)g * N + h] == 0) { INV[g] = h; break; } if (INV[g] < 0) exit(2); }
}

static void setup_cosets(void) {
    int hmax = getenv("HMAX") ? atoi(getenv("HMAX")) : 64, best = 1, bh = 0;
    for (int g = 0; g < N; g++) { int x = g, o = 1; while (x != 0 && o <= N) { x = mul(x, g); o++; }
        /* largest divisor of o that is <= hmax: use g^(o/dv) */
        for (int dv = hmax; dv > best; dv--) if (o % dv == 0) { int e = o / dv, hh = 0; for (int u = 0; u < e; u++) hh = mul(hh, g); best = dv; bh = hh; break; } }
    nH = best; R = N / nH; if (R > MAXR) { fprintf(stderr, "too many rows %d\n", R); exit(2); }
    HMASK = nH == 64 ? ~0ULL : ((1ULL << nH) - 1);
    int *HP = malloc(nH * sizeof(int)); HP[0] = 0; for (int t = 1; t < nH; t++) HP[t] = mul(HP[t - 1], bh);
    POS = malloc(N * sizeof(int)); for (int g = 0; g < N; g++) POS[g] = -1; REP = malloc(R * sizeof(int));
    int r = 0; for (int g = 0; g < N; g++) if (POS[g] < 0) { REP[r] = g; for (int t = 0; t < nH; t++) POS[mul(g, HP[t])] = r * 64 + t; r++; }
    if (r != R) { fprintf(stderr, "coset error\n"); exit(2); }
    RMAP = malloc((size_t)N * R * 2); ROT = malloc((size_t)N * R);
    for (int g = 0; g < N; g++) for (int q = 0; q < R; q++) { int p = POS[mul(g, REP[q])]; RMAP[(size_t)g * R + q] = p >> 6; ROT[(size_t)g * R + q] = p & 63; }
    free(HP);
}

static void load_base(const char *p) {
    FILE *f = fopen(p, "r"); if (!f || fscanf(f, "%d %d", &b, &m) != 2 || b > MAXB || m > MAXE) { fprintf(stderr, "bad base\n"); exit(2); }
    char line[256]; if (!fgets(line, sizeof line, f)) {}
    for (int i = 0; i < m; i++) {
        if (!fgets(line, sizeof line, f)) exit(2);
        char t3[64] = ""; int n3 = sscanf(line, "%d %d %63s", &eu[i], &ev[i], t3);
        if (n3 < 2) { i--; continue; }
        if (eu[i] == ev[i]) { fprintf(stderr, "loops not supported\n"); exit(2); }
        efix[i] = n3 == 3 ? atoi(t3) : -1;
    }
    for (int i = 0; i < m; i++) { int u = eu[i], v = ev[i];
        dto[u][ndart[u]] = v; dedge[u][ndart[u]] = i; dinv[u][ndart[u]] = 0; ndart[u]++;
        dto[v][ndart[v]] = u; dedge[v][ndart[v]] = i; dinv[v][ndart[v]] = 1; ndart[v]++; }
    int intree[MAXE] = {0};
    if (!getenv("NOTREE") || !atoi(getenv("NOTREE"))) {
        int seen[MAXB] = {0}, qq[MAXB], h = 0, t = 0; seen[0] = 1; qq[t++] = 0;
        while (h < t) { int u = qq[h++]; for (int j = 0; j < ndart[u]; j++) { int v = dto[u][j], e = dedge[u][j];
            if (!seen[v] && efix[e] < 0) { seen[v] = 1; intree[e] = 1; qq[t++] = v; } } }
    }
    nfree = 0; for (int i = 0; i < m; i++) { if (intree[i]) efix[i] = 0; if (efix[i] < 0) freeidx[nfree++] = i; }
}
/* dart u->v along edge e: (u,x) ~ (v, g x) with g = volt (forward) or volt^-1 (backward) */
static inline int dvolt(int u, int j) { int g = volt[dedge[u][j]]; return dinv[u][j] ? INV[g] : g; }
static int ok_at(int u) {
    for (int j = 0; j < ndart[u]; j++) { int g = dvolt(u, j);
        for (int i = 0; i < j; i++) if (dto[u][i] == dto[u][j] && dvolt(u, i) == g) return 0; }
    return 1;
}
static inline uint64_t rotl(uint64_t x, int s) { if (!s) return x; return ((x << s) | (x >> (nH - s))) & HMASK; }

static long cost(long lim) {
    evals++; long c = 0; size_t BR = (size_t)b * R;
    for (int root = 0; root < b; root++) {
        memset(F, 0, BR * 8); memset(V, 0, BR * 8);
        F[(size_t)root * R + (POS[0] >> 6)] = 1ULL << (POS[0] & 63); V[(size_t)root * R + (POS[0] >> 6)] = F[(size_t)root * R + (POS[0] >> 6)];
        for (int lev = 1; lev <= D; lev++) {
            memset(NF, 0, BR * 8);
            for (int u = 0; u < b; u++) { const uint64_t *Fu = F + (size_t)u * R;
                for (int j = 0; j < ndart[u]; j++) { int v = dto[u][j], g = dvolt(u, j); uint64_t *NFv = NF + (size_t)v * R;
                    const int16_t *rm = RMAP + (size_t)g * R; const int8_t *ro = ROT + (size_t)g * R;
                    for (int r = 0; r < R; r++) if (Fu[r]) NFv[rm[r]] |= rotl(Fu[r], ro[r]); } }
            for (size_t i = 0; i < BR; i++) { NF[i] &= ~V[i]; V[i] |= NF[i]; }
            uint64_t *t = F; F = NF; NF = t;
        }
        long reached = 0; for (size_t i = 0; i < BR; i++) reached += __builtin_popcountll(V[i]);
        c += (long)b * N - reached;
        if (c > lim) return c;
    }
    return c;
}

static void write_sol(const char *out, long c) {
    FILE *f = fopen(out, "w");
    fprintf(f, "# flift solution d=%d D=%d n=%d cost=%ld (left multiplication: (u,x)~(v,g*x))\nbase %d %d\ngroup %s %d\n", d, D, b * N, c, b, m, gspec, N);
    for (int i = 0; i < m; i++) fprintf(f, "e %d %d %d\n", eu[i], ev[i], volt[i]);
    fclose(f);
    char p[1024]; snprintf(p, sizeof p, "%s.edges", out); f = fopen(p, "w"); fprintf(f, "%d\n", b * N);
    for (int i = 0; i < m; i++) for (int x = 0; x < N; x++) fprintf(f, "%d %d\n", eu[i] * N + x, ev[i] * N + mul(volt[i], x));
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: flift BASE GROUP d D seconds seed [K] [OUT] | flift BASE GROUP d D eval\n"); return 2; }
    load_group(argv[2]); load_base(argv[1]); setup_cosets();
    d = atoi(argv[3]); D = atoi(argv[4]);
    F = malloc((size_t)b * R * 8); NF = malloc((size_t)b * R * 8); V = malloc((size_t)b * R * 8);
    for (int u = 0; u < b; u++) if (ndart[u] > d) { fprintf(stderr, "base degree > d\n"); return 2; }
    if (!strcmp(argv[5], "eval")) {
        char *line = NULL; size_t cap = 0; long lim = getenv("LIMIT") ? atol(getenv("LIMIT")) : (1L << 60);
        int quietok = getenv("ONLYLOW") ? 1 : 0; long nl = 0, minc = 1L << 60;
        while (getline(&line, &cap, stdin) > 0) {
            nl++;
            char *p = line, *q; int i = 0;
            for (; i < m; i++) { long x = strtol(p, &q, 10); if (q == p) break; volt[i] = (int)(((x % N) + N) % N); p = q; }
            if (i < m) continue;
            int ok = 1; for (int u = 0; u < b; u++) if (!ok_at(u)) ok = 0;
            if (!ok) { printf("invalid\n"); continue; }
            long c = cost(lim); if (c < minc) minc = c;
            if (!quietok) printf("%ld\n", c);
            else if (c <= lim) { printf("%ld :", c); for (int i2 = 0; i2 < m; i2++) printf(" %d", volt[i2]); printf("\n"); fflush(stdout); }
        }
        if (quietok) fprintf(stderr, "lines %ld min %ld\n", nl, minc);
        return 0;
    }
    double secs = atof(argv[5]); rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    if (argc > 7) K = atoi(argv[7]);
    const char *out = argc > 8 ? argv[8] : NULL;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 3.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    long EPOCH = getenv("EPOCH") ? atol(getenv("EPOCH")) : 20000; int quiet = getenv("QUIET") ? atoi(getenv("QUIET")) : 0;
    for (int i = 0; i < m; i++) volt[i] = efix[i] >= 0 ? efix[i] : 0;
    for (int f = 0; f < nfree; f++) { int e = freeidx[f], tries = 0; do { volt[e] = (int)(rnd() % N); } while ((!ok_at(eu[e]) || !ok_at(ev[e])) && ++tries < 100000); }
    long cur = cost(1L << 60), best = cur; memcpy(bestv, volt, sizeof volt);
    if (!quiet) printf("group %s N=%d H=%d rows=%d base b=%d m=%d free=%d n=%d start cost=%ld\n", gspec, N, nH, R, b, m, nfree, b * N, cur);
    double t0 = now(), tl = t0; long step = 0;
    while (best > 0 && nfree > 0) {
        if ((step & 255) == 0) { double tn = now(); if (tn - t0 > secs) break;
            if (!quiet && tn - tl > 10) { printf("t=%.0f evals=%lld cur=%ld best=%ld\n", tn - t0, evals, cur, best); fflush(stdout); tl = tn; } }
        long ph = step % EPOCH; if (ph == 0 && step > 0) { memcpy(volt, bestv, sizeof volt); cur = best; }
        double T = T0 * pow(T1 / T0, (double)ph / EPOCH);
        int e = freeidx[rnd() % nfree], old = volt[e], bg = -1; long bc = 1L << 60, lim = cur + (long)(T * 10) + 2;
        for (int k = 0; k < K; k++) { int g = (int)(rnd() % N); if (g == old) continue; volt[e] = g;
            if (!ok_at(eu[e]) || !ok_at(ev[e])) continue; long c = cost(bc < lim ? bc : lim); if (c < bc) { bc = c; bg = g; } }
        volt[e] = old;
        if (bg >= 0 && (bc <= cur || rnd01() < exp(-(bc - cur) / T))) { volt[e] = bg; cur = bc;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof volt); if (!quiet) { printf("t=%.1f evals=%lld best=%ld\n", now() - t0, evals, best); fflush(stdout); } } }
        step++;
    }
    memcpy(volt, bestv, sizeof volt); if (nfree == 0) best = cost(1L << 60);
    printf("RESULT d=%d D=%d group=%s base=%s n=%d best=%ld evals=%lld time=%.1f\n", d, D, gspec, argv[1], b * N, best, evals, now() - t0);
    if (out) { write_sol(out, best); printf("wrote %s and %s.edges (cost %ld)\n", out, out, best); }
    return best == 0 ? 0 : 1;
}
