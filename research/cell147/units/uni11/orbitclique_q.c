/* orbitclique_q.c (env Q = prime q, default 11): partial ovoids of the elliptic section E as unions of orbits of an isometry of E, by an
   iterated local search for a maximum-weight set of pairwise compatible independent orbits. Session cell-14-7 (second).
   Input: E11.map (vertex i of E: hexagon point id, spread line id, coordinates x0..x6) and a permutation of the
   vertices of E (one integer per line, the image of vertex i), e.g. induced by an isometry of V = {x4 = -x0}
   (card r3c3's elements). Orbits = cycles. An orbit is usable if its points are pairwise non-orthogonal; two usable orbits
   are compatible if every point of one is non-orthogonal to every point of the other. Weight = orbit size.
   Usage: orbitclique MAPFILE PERMFILE SECONDS SEED OUTFLAGS [INITFLAGS]
   Output: flags "point spread_line" of the best union (input for pack CHECKONLY / t2design FLAGS=).
   Compile: gcc -O3 -march=native -o orbitclique orbitclique.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q = 11;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static int n, (*X)[7], *pidv, *slv;
static inline int orth(int a, int b) { const int *x = X[a], *y = X[b];
    long s = (long)x[0]*y[4] + (long)x[4]*y[0] + (long)x[1]*y[5] + (long)x[5]*y[1] + (long)x[2]*y[6] + (long)x[6]*y[2] - 2L*x[3]*y[3];
    return (s % q + q) % q == 0; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: orbitclique MAPFILE PERMFILE SECONDS SEED OUTFLAGS [INITFLAGS]\n"); return 2; }
    if (getenv("Q")) q = atoi(getenv("Q"));
    FILE *f = fopen(argv[1], "r"); int cap = 200000; X = malloc(sizeof(int) * 7 * cap); pidv = malloc(sizeof(int) * cap); slv = malloc(sizeof(int) * cap); n = 0;
    while (n < cap && fscanf(f, "%d %d %d %d %d %d %d %d %d", &pidv[n], &slv[n], &X[n][0], &X[n][1], &X[n][2], &X[n][3], &X[n][4], &X[n][5], &X[n][6]) == 9) n++;
    fclose(f);
    int *perm = malloc(sizeof(int) * n); f = fopen(argv[2], "r"); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &perm[i]) != 1) { fprintf(stderr, "bad perm\n"); return 2; } fclose(f);
    double secs = atof(argv[3]); rs ^= strtoull(argv[4], 0, 10) * 0x2545F4914F6CDD1DULL;
    /* orbits */
    int *orb = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) orb[i] = -1;
    int no = 0, *ostart = malloc(sizeof(int) * (n + 1)), *opts = malloc(sizeof(int) * n), np2 = 0;
    for (int i = 0; i < n; i++) if (orb[i] < 0) { ostart[no] = np2; int j = i; while (orb[j] < 0) { orb[j] = no; opts[np2++] = j; j = perm[j]; } no++; }
    ostart[no] = np2;
    if (np2 != n) { fprintf(stderr, "not a permutation\n"); return 2; }
    char *usable = calloc(no, 1); int nu = 0; long hist[64] = {0};
    for (int o = 0; o < no; o++) { int ok = 1, sz = ostart[o + 1] - ostart[o]; if (sz < 64) hist[sz]++;
        for (int a = ostart[o]; a < ostart[o + 1] && ok; a++) for (int b = a + 1; b < ostart[o + 1]; b++) if (orth(opts[a], opts[b])) { ok = 0; break; }
        if (ok) { usable[o] = 1; nu++; } }
    fprintf(stderr, "%d orbits (%d usable); sizes:", no, nu); for (int s = 1; s < 64; s++) if (hist[s]) fprintf(stderr, " %ldx%d", hist[s], s); fprintf(stderr, "\n");
    int *U = malloc(sizeof(int) * nu), *uid = malloc(sizeof(int) * no); { int c = 0; for (int o = 0; o < no; o++) { uid[o] = -1; if (usable[o]) { uid[o] = c; U[c++] = o; } } }
    int *w = malloc(sizeof(int) * nu); for (int i = 0; i < nu; i++) w[i] = ostart[U[i] + 1] - ostart[U[i]];
    /* conflict lists among usable orbits: conflict iff some cross pair is orthogonal */
    int **adj = malloc(sizeof(int *) * nu), *deg = calloc(nu, sizeof(int)); int *tmp = malloc(sizeof(int) * nu);
    char *conf = calloc(nu, 1);
    for (int i = 0; i < nu; i++) {
        memset(conf, 0, nu);
        int o = U[i];
        for (int a = ostart[o]; a < ostart[o + 1]; a++) { int x = opts[a];
            for (int y = 0; y < n; y++) { int oy = orb[y]; if (oy == o || uid[oy] < 0 || conf[uid[oy]]) continue; if (orth(x, y)) conf[uid[oy]] = 1; } }
        int c = 0; for (int j = 0; j < nu; j++) if (conf[j]) tmp[c++] = j;
        adj[i] = malloc(sizeof(int) * (c + 1)); memcpy(adj[i], tmp, sizeof(int) * c); deg[i] = c;
    }
    long sd = 0; for (int i = 0; i < nu; i++) sd += deg[i];
    fprintf(stderr, "conflict graph: %d vertices, average degree %.1f (compatibility density %.3f)\n", nu, (double)sd / nu, 1.0 - (double)sd / nu / (nu - 1));
    /* weighted ILS */
    int *inS = calloc(nu, sizeof(int)), *tau = calloc(nu, sizeof(int)), *S = malloc(sizeof(int) * nu), *pos = malloc(sizeof(int) * nu); int ns = 0; long W = 0;
    #define ADD(v) do { int v_ = (v); inS[v_] = 1; pos[v_] = ns; S[ns++] = v_; W += w[v_]; for (int e_ = 0; e_ < deg[v_]; e_++) tau[adj[v_][e_]]++; } while (0)
    #define REM(v) do { int v_ = (v); inS[v_] = 0; int p_ = pos[v_]; S[p_] = S[--ns]; pos[S[p_]] = p_; W -= w[v_]; for (int e_ = 0; e_ < deg[v_]; e_++) tau[adj[v_][e_]]--; } while (0)
    if (argc > 6) { FILE *fi = fopen(argv[6], "r"); int a, b, *vofp = malloc(sizeof(int) * 200000); for (int i = 0; i < 200000; i++) vofp[i] = -1; for (int i = 0; i < n; i++) vofp[pidv[i]] = i;
        char *want = calloc(nu, 1); while (fi && fscanf(fi, "%d %d", &a, &b) == 2) if (a >= 0 && a < 200000 && vofp[a] >= 0) { int u = uid[orb[vofp[a]]]; if (u >= 0) want[u] = 1; }
        if (fi) fclose(fi); for (int i = 0; i < nu; i++) if (want[i] && tau[i] == 0) ADD(i); fprintf(stderr, "init: %d orbits, weight %ld\n", ns, W); free(want); free(vofp); }
    int *order = malloc(sizeof(int) * nu); for (int i = 0; i < nu; i++) order[i] = i;
    for (int i = nu - 1; i > 0; i--) { int r = rndi(i + 1); int t = order[i]; order[i] = order[r]; order[r] = t; }
    for (int i = 0; i < nu; i++) { int v = order[i]; if (!inS[v] && tau[v] == 0) ADD(v); }
    int *best = malloc(sizeof(int) * nu), nbest = ns; long Wbest = W; memcpy(best, S, sizeof(int) * ns);
    fprintf(stderr, "greedy: %d orbits, weight %ld\n", ns, W);
    clock_t c0 = clock(); long it = 0;
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < secs) {
        it++; int v = rndi(nu); if (inS[v]) continue;
        if (tau[v] == 0) ADD(v);
        else if (tau[v] == 1) { int u = -1; for (int e = 0; e < deg[v]; e++) if (inS[adj[v][e]]) { u = adj[v][e]; break; }
            if (w[v] < w[u] && rndi(8)) continue;
            REM(u); ADD(v); for (int e = 0; e < deg[u]; e++) { int x = adj[u][e]; if (!inS[x] && tau[x] == 0) ADD(x); } }
        else if (tau[v] == 2 && rndi(40) == 0) { for (int e = 0; e < deg[v]; e++) { int u = adj[v][e]; if (inS[u]) REM(u); } ADD(v); }
        if (W > Wbest) { Wbest = W; nbest = ns; memcpy(best, S, sizeof(int) * ns); fprintf(stderr, "it %ld: %d orbits, weight %ld\n", it, ns, W); }
        if (W < Wbest - 24) { while (ns) REM(S[ns - 1]); for (int i = 0; i < nbest; i++) ADD(best[i]); }
    }
    /* output and self-check */
    int *outv = malloc(sizeof(int) * n), nout = 0;
    for (int i = 0; i < nbest; i++) { int o = U[best[i]]; for (int a = ostart[o]; a < ostart[o + 1]; a++) outv[nout++] = opts[a]; }
    long bad = 0; for (int i = 0; i < nout; i++) for (int j = i + 1; j < nout; j++) if (orth(outv[i], outv[j])) bad++;
    f = fopen(argv[5], "w"); for (int i = 0; i < nout; i++) fprintf(f, "%d %d\n", pidv[outv[i]], slv[outv[i]]); fclose(f);
    fprintf(stderr, "best: %d orbits, %d points, orthogonal pairs %ld (%ld iterations)\n", nbest, nout, bad, it);
    return bad ? 1 : 0;
}
