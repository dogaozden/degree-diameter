/* orbset.c: large non-collinear point sets (kind 0) / non-concurrent line sets (kind 1) of H(q) that are unions of
   orbits of a collineation group given by one generator (permutation files from collin.py). cell-16-7 session.
   Orbit graph: vertices = orbits with no two members collinear (concurrent); edge = some member of one orbit is
   collinear (concurrent) with some member of the other. A maximum independent set of the orbit graph is searched by an
   iterated local search in the style of Andrade-Resende-Werneck: (1,2)-swaps to a local optimum, then perturbation by
   forcing in one or more non-solution vertices, keeping the best.
   Usage: orbset HEXBIN PERMPTS.bin PERMLINES.bin KIND SEED SECONDS OUT.txt [INIT.txt]
   OUT: element ids (one per line, '#' header lines with the orbit count); INIT: optional element list to start from
   (only whole orbits are kept). Env: EXPORT=file writes the orbit graph ("M E", then per vertex "idx rep deg nbrs...",
   rep = smallest element of the orbit) and exits (EXPORT_CONTINUE=1 to go on); SEEDOUT=file writes the best solution as
   orbit-graph indices. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1;
static int32_t *LP, *PL;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int M;                       /* orbit-graph vertices */
static int **adj, *deg;             /* adjacency lists */
static uint64_t *AM; static int W;  /* adjacency bit matrix */
static inline int isadj(int a, int b) { return (AM[(size_t)a * W + (b >> 6)] >> (b & 63)) & 1; }
static char *inS; static int *tau, nS;
static int *sol, *where;            /* solution list with positions */
static void add_v(int v) { inS[v] = 1; where[v] = nS; sol[nS++] = v; for (int i = 0; i < deg[v]; i++) tau[adj[v][i]]++; }
static void rem_v(int v) { inS[v] = 0; int p = where[v]; sol[p] = sol[--nS]; where[sol[p]] = p; for (int i = 0; i < deg[v]; i++) tau[adj[v][i]]--; }

/* free list: vertices not in S with tau 0 */
static void make_maximal(void) {
    int *c = malloc(sizeof(int) * M), n = 0;
    for (int v = 0; v < M; v++) if (!inS[v] && tau[v] == 0) c[n++] = v;
    for (int i = n - 1; i > 0; i--) { int j = rndi(i + 1); int t = c[i]; c[i] = c[j]; c[j] = t; }
    for (int i = 0; i < n; i++) if (!inS[c[i]] && tau[c[i]] == 0) add_v(c[i]);
    free(c);
}
/* (1,2)-swaps until none: remove x in S, add two non-adjacent 1-tight neighbours of x */
static int two_improve(void) {
    int improved = 0, again = 1, *U = malloc(sizeof(int) * M);
    while (again) {
        again = 0;
        for (int s = 0; s < nS; s++) {
            int x = sol[s], nu = 0;
            for (int i = 0; i < deg[x]; i++) { int u = adj[x][i]; if (!inS[u] && tau[u] == 1) U[nu++] = u; }
            if (nu < 2) continue;
            int a = -1, b = -1;
            for (int i = 0; i < nu && a < 0; i++) for (int j = i + 1; j < nu; j++) if (!isadj(U[i], U[j])) { a = U[i]; b = U[j]; break; }
            if (a < 0) continue;
            rem_v(x); add_v(a); add_v(b);
            for (int i = 0; i < nu; i++) if (!inS[U[i]] && tau[U[i]] == 0) add_v(U[i]);
            improved = 1; again = 1; break;
        }
    }
    free(U); return improved;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: orbset HEXBIN PERMPTS.bin PERMLINES.bin KIND SEED SECONDS OUT.txt [INIT.txt]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[(size_t)l * Q1 + k]; PL[(size_t)p * Q1 + c[p]++] = l; }
    int kind = atoi(argv[4]);
    int32_t *perm = malloc(sizeof(int32_t) * N);
    f = fopen(argv[kind == 0 ? 2 : 3], "rb"); if (!f || fread(perm, 4, N, f) != (size_t)N) { fprintf(stderr, "perm read\n"); return 1; } fclose(f);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double tmax = atof(argv[6]);
    const int32_t *A = kind == 0 ? PL : LP, *B = kind == 0 ? LP : PL;
    /* orbits */
    int *orb = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) orb[i] = -1;
    int no = 0, *rep = malloc(sizeof(int) * N);
    for (int s = 0; s < N; s++) if (orb[s] < 0) { int x = s; while (orb[x] < 0) { orb[x] = no; x = perm[x]; } rep[no++] = s; }
    /* members */
    int *ostart = calloc(no + 1, sizeof(int)), *omem = malloc(sizeof(int) * N), *fill = calloc(no, sizeof(int));
    for (int i = 0; i < N; i++) ostart[orb[i] + 1]++;
    for (int o = 0; o < no; o++) ostart[o + 1] += ostart[o];
    for (int i = 0; i < N; i++) omem[ostart[orb[i]] + fill[orb[i]]++] = i;
    /* good orbits */
    int *gid = malloc(sizeof(int) * no); M = 0;
    for (int o = 0; o < no; o++) {
        int good = 1;
        for (int t = ostart[o]; t < ostart[o + 1] && good; t++) { int x = omem[t];
            for (int a = 0; a < Q1 && good; a++) { int y = A[(size_t)x * Q1 + a]; for (int b = 0; b < Q1; b++) { int z = B[(size_t)y * Q1 + b]; if (z != x && orb[z] == o) { good = 0; break; } } } }
        gid[o] = good ? M++ : -1;
    }
    int *g2o = malloc(sizeof(int) * M); for (int o = 0; o < no; o++) if (gid[o] >= 0) g2o[gid[o]] = o;
    W = (M + 63) / 64; AM = calloc((size_t)M * W, 8);
    adj = malloc(sizeof(int *) * M); deg = calloc(M, sizeof(int));
    int *mark = malloc(sizeof(int) * M); for (int i = 0; i < M; i++) mark[i] = -1;
    int *tmp = malloc(sizeof(int) * M); long etot = 0;
    for (int g = 0; g < M; g++) {
        int o = g2o[g], n = 0;
        for (int t = ostart[o]; t < ostart[o + 1]; t++) { int x = omem[t];
            for (int a = 0; a < Q1; a++) { int y = A[(size_t)x * Q1 + a]; for (int b = 0; b < Q1; b++) { int z = B[(size_t)y * Q1 + b]; int g2 = gid[orb[z]];
                if (z == x || g2 < 0 || g2 == g || mark[g2] == g) continue; mark[g2] = g; tmp[n++] = g2; } } }
        adj[g] = malloc(sizeof(int) * (n + 1)); memcpy(adj[g], tmp, sizeof(int) * n); deg[g] = n; etot += n;
        for (int i = 0; i < n; i++) AM[(size_t)g * W + (tmp[i] >> 6)] |= 1ULL << (tmp[i] & 63);
    }
    int osz = ostart[1] - ostart[0];
    fprintf(stderr, "kind %d: %d orbits (size %d), %d good, orbit-graph avg degree %.1f\n", kind, no, osz, M, (double)etot / M);
    if (getenv("EXPORT")) {   /* write the orbit graph: "M E", then per vertex "idx rep deg nbrs..." */
        FILE *fe = fopen(getenv("EXPORT"), "w");
        fprintf(fe, "%d %ld\n", M, etot / 2);
        for (int g = 0; g < M; g++) { fprintf(fe, "%d %d %d", g, rep[g2o[g]], deg[g]); for (int i = 0; i < deg[g]; i++) fprintf(fe, " %d", adj[g][i]); fprintf(fe, "\n"); }
        fclose(fe); fprintf(stderr, "exported orbit graph to %s\n", getenv("EXPORT")); if (!getenv("EXPORT_CONTINUE")) return 0;
    }
    inS = calloc(M, 1); tau = calloc(M, sizeof(int)); sol = malloc(sizeof(int) * M); where = malloc(sizeof(int) * M); nS = 0;
    if (argc > 8) {   /* init */
        FILE *fi = fopen(argv[8], "r"); char buf[256]; int x; int *cnt = calloc(no, sizeof(int));
        while (fi && fgets(buf, sizeof buf, fi)) if (buf[0] != '#' && sscanf(buf, "%d", &x) == 1 && x >= 0 && x < N) cnt[orb[x]]++;
        if (fi) fclose(fi);
        for (int o = 0; o < no; o++) if (cnt[o] == ostart[o + 1] - ostart[o] && gid[o] >= 0 && tau[gid[o]] == 0) add_v(gid[o]);
        fprintf(stderr, "init: %d orbits\n", nS);
    }
    make_maximal(); two_improve();
    int bestn = nS; char *best = malloc(M); memcpy(best, inS, M);
    fprintf(stderr, "start %d orbits = %d elements\n", nS, nS * osz);
    double t0 = now(), last = t0; long it = 0;
    int *cand = malloc(sizeof(int) * M);
    while (now() - t0 < tmax) {
        it++;
        /* perturb: force in k vertices (k = 1 mostly), chosen among non-solution vertices with small tau */
        int k = (rndi(8) == 0) ? 2 + rndi(3) : 1;
        for (int r = 0; r < k; r++) {
            int v = -1, tries = 0;
            while (tries++ < 50) { int u = rndi(M); if (inS[u]) continue; if (v < 0 || tau[u] < tau[v]) v = u; if (tau[v] <= 1 && rndi(2)) break; }
            if (v < 0) continue;
            for (int i = 0; i < deg[v]; i++) if (inS[adj[v][i]]) rem_v(adj[v][i]);
            add_v(v);
        }
        make_maximal(); two_improve();
        if (nS > bestn) { bestn = nS; memcpy(best, inS, M); fprintf(stderr, "  %.1fs it %ld: %d orbits = %d elements\n", now() - t0, it, nS, nS * osz); }
        else if (nS < bestn - 1 - rndi(2)) {   /* fall back to the best */
            for (int v = 0; v < M; v++) if (inS[v] && !best[v]) rem_v(v);
            for (int v = 0; v < M; v++) if (!inS[v] && best[v]) add_v(v);
        }
        if (now() - last > 60) { last = now(); fprintf(stderr, "  %.0fs it %ld: cur %d best %d\n", now() - t0, it, nS, bestn); }
    }
    /* write best, verify independence on elements */
    char *inE = calloc(N, 1); int ne = 0;
    for (int g = 0; g < M; g++) if (best[g]) { int o = g2o[g]; for (int t = ostart[o]; t < ostart[o + 1]; t++) { inE[omem[t]] = 1; ne++; } }
    for (int x = 0; x < N; x++) if (inE[x]) for (int a = 0; a < Q1; a++) { int y = A[(size_t)x * Q1 + a]; for (int b = 0; b < Q1; b++) { int z = B[(size_t)y * Q1 + b]; if (z != x && inE[z]) { fprintf(stderr, "BUG: not independent\n"); return 1; } } }
    if (getenv("SEEDOUT")) { FILE *fz = fopen(getenv("SEEDOUT"), "w"); for (int g = 0; g < M; g++) if (best[g]) fprintf(fz, "%d\n", g); fclose(fz); }
    FILE *fo = fopen(argv[7], "w");
    fprintf(fo, "# orbset kind %d: %d orbits of size %d = %d elements (q=%d, Hoffman bound %d)\n", kind, bestn, osz, ne, q, N / Q1);
    for (int x = 0; x < N; x++) if (inE[x]) fprintf(fo, "%d\n", x);
    fclose(fo);
    fprintf(stderr, "RESULT kind %d: %d orbits = %d elements (%.1f%% of Hoffman %d), it %ld\n", kind, bestn, ne, 100.0 * ne / (N / Q1), N / Q1, it);
    (void)rep; (void)cand;
    return 0;
}
