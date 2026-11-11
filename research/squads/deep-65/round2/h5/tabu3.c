/* tabu3.c: full-neighbourhood tabu search for bipartite graphs of type "1,1,3|1,1,3" (degree 6, n = 14m/3).
 * Generalises shared/t18.c ("1,k|1,k") to 9 blocks (N = "a,5-a,1,5-a,a,1,1,1,0", A1B1 empty).
 * Orbits (G = group of order m, q = m/3):
 *   A0' (regular, vertex x -> x), A0'' (regular, x -> m+x), A1 = G/H (coset xH -> 2m+c),
 *   B0' (regular, y -> 2m+q+y), B0'' (regular, y -> 3m+q+y), B1 = G/K (coset yK -> 4m+q+c); |H| = |K| = 3 cyclic.
 * Blocks (double cosets, all full size):
 *   0 A0'-B0' : S1 (a elements s): x ~ xs            1 A0'-B0'' : S2 (5-a elements): x ~ xs
 *   3 A0''-B0': S3 (5-a elements)                     4 A0''-B0'': S4 (a elements)
 *   2 A0'-B1  : one left coset gK: x ~ (xg)K           5 A0''-B1 : one left coset gK
 *   6 A1-B0'  : one right coset Hg: xH ~ x h g (h in H)  7 A1-B0'' : one right coset Hg
 * Degrees are 6 for every such choice. cost = sum over the six orbit representatives of the vertices not reached
 * within 5 steps (A reps: all vertices; B reps: B vertices), the same as mcos. cost 0 <=> diameter <= 5.
 * Moves: change one element of S1..S4, one coset parameter (blocks 2,5,6,7), or H or K to another subgroup of order 3.
 * Each step applies the best non-tabu move of the full neighbourhood (aspiration if it beats the best).
 * usage: tabu3 TABLE A SEED STEPS TENURE TLIM OUT [STALL]
 *   TABLE: group table as for mcos (m, then m x m table, element 0 = identity). A in 1..4.
 *   Prints "best C step S t=T" on each improvement, "RESULT best C steps S time T", "SOL" for cost 0.
 *   Writes OUT (edge list of the best graph) on each improvement and OUT.par (parameters) at the end.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXV 4096
#define MAXSUB 1024
#define BIG (1 << 28)
static int m, q, *T, ord_[MAXM];
#define MUL(x, y) T[(size_t)(x) * m + (y)]
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int nsub, subel[MAXSUB][3];
static int *cosl[MAXSUB];      /* cosl[s][z] = index of the left coset zK_s */
static int *cosr[MAXSUB];      /* cosr[s][c] = representative z of coset c */
static int nS[8];             /* slots per block: 0:a 1:5-a 2:1 3:5-a 4:a 5:1 6:1 7:1 */
static int par[8][8];
static int hs, ks;            /* current subgroups H (A1) and K (B1) */
static int unw = 0;           /* env UNW=1: mcos-style unweighted cost instead of 2*bad */
static int adj[MAXV][6], deg[MAXV], nv, ovf;

static long tabu_until[8][8], tabu_sub[2];
static const int ELEM_BLK[4] = {0, 1, 3, 4}, COS_BLK[4] = {2, 5, 6, 7};

static int is_elem(int b) { return b == 0 || b == 1 || b == 3 || b == 4; }
static void add_edge(int u, int v) {
    if (deg[u] >= 6 || deg[v] >= 6) { ovf = 1; return; }
    adj[u][deg[u]++] = v; adj[v][deg[v]++] = u;
}
static void build_cosets(int s) {
    int *c = malloc(sizeof(int) * m), *rep = malloc(sizeof(int) * q), nx = 0;
    for (int z = 0; z < m; z++) c[z] = -1;
    for (int z = 0; z < m; z++) if (c[z] < 0) {
        int id = nx++; rep[id] = z;
        for (int i = 0; i < 3; i++) c[MUL(z, subel[s][i])] = id;
    }
    cosl[s] = c; cosr[s] = rep;
}
static void enum_sub(void) {
    nsub = 0;
    for (int g = 0; g < m; g++) if (ord_[g] == 3) {
        int dup = 0;
        for (int s = 0; s < nsub && !dup; s++) if (subel[s][1] == g || subel[s][2] == g) dup = 1;
        if (dup || nsub >= MAXSUB) continue;
        subel[nsub][0] = 0; subel[nsub][1] = g; subel[nsub][2] = MUL(g, g); nsub++;
    }
}
static void build(void) {
    const int bA1 = 2 * m, bB0 = 2 * m + q, bB0pp = 3 * m + q, bB1 = 4 * m + q;
    const int *cK = cosl[ks];
    nv = 4 * m + 2 * q;
    for (int v = 0; v < nv; v++) deg[v] = 0;
    ovf = 0;
    for (int i = 0; i < nS[0]; i++) { int s = par[0][i]; for (int x = 0; x < m; x++) add_edge(x, bB0 + MUL(x, s)); }
    for (int i = 0; i < nS[1]; i++) { int s = par[1][i]; for (int x = 0; x < m; x++) add_edge(x, bB0pp + MUL(x, s)); }
    { int g = par[2][0]; for (int x = 0; x < m; x++) add_edge(x, bB1 + cK[MUL(x, g)]); }
    for (int i = 0; i < nS[3]; i++) { int s = par[3][i]; for (int x = 0; x < m; x++) add_edge(m + x, bB0 + MUL(x, s)); }
    for (int i = 0; i < nS[4]; i++) { int s = par[4][i]; for (int x = 0; x < m; x++) add_edge(m + x, bB0pp + MUL(x, s)); }
    { int g = par[5][0]; for (int x = 0; x < m; x++) add_edge(m + x, bB1 + cK[MUL(x, g)]); }
    { int g = par[6][0];
      for (int c = 0; c < q; c++) { int xc = cosr[hs][c];
          for (int j = 0; j < 3; j++) add_edge(bA1 + c, bB0 + MUL(MUL(xc, subel[hs][j]), g)); } }
    { int g = par[7][0];
      for (int c = 0; c < q; c++) { int xc = cosr[hs][c];
          for (int j = 0; j < 3; j++) add_edge(bA1 + c, bB0pp + MUL(MUL(xc, subel[hs][j]), g)); } }
}
/* bit-parallel: bit o of reach[v] = 1 iff the representative of orbit o is within distance d of v */
static uint8_t reach[MAXV], nxtr[MAXV];
static int cost_now(void) {
    build();
    if (ovf) return BIG;
    for (int v = 0; v < nv; v++) if (deg[v] != 6) return BIG;
    const int src[6] = {0, m, 2 * m, 2 * m + q, 3 * m + q, 4 * m + q};
    const int bstart = 2 * m + q;
    for (int v = 0; v < nv; v++) reach[v] = 0;
    for (int o = 0; o < 6; o++) reach[src[o]] |= (uint8_t)(1u << o);
    for (int d = 0; d < 5; d++) {
        for (int v = 0; v < nv; v++) {
            uint8_t r = reach[v];
            for (int j = 0; j < 6; j++) r |= reach[adj[v][j]];
            nxtr[v] = r;
        }
        memcpy(reach, nxtr, sizeof(uint8_t) * nv);
    }
    /* exact objective: sum over orbits o of |O_o| * (vertices not within 5 of the representative of o).
       This is the number of ordered bad pairs, so cost = 2 * bad (unordered pairs at distance > 5). */
    int cnt[6] = {0, 0, 0, 0, 0, 0};
    for (int v = 0; v < nv; v++) { uint8_t miss = (uint8_t)(~reach[v]) & 0x3F;
        for (int o = 0; o < 6; o++) cnt[o] += (miss >> o) & 1; }
    if (unw) {   /* mcos-style cost (A reps: all vertices, B reps: B vertices only) */
        int total = 0;
        for (int v = 0; v < bstart; v++) total += __builtin_popcount((~reach[v]) & 0x07);
        for (int v = bstart; v < nv; v++) total += __builtin_popcount((~reach[v]) & 0x3F);
        return total;
    }
    int tot = 0;
    for (int o = 0; o < 6; o++) tot += cnt[o] * (o == 2 || o == 5 ? q : m);
    return tot;
}
static void write_edges(const char *fn) {   /* adj must be the current graph (call cost_now first) */
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", nv);
    for (int v = 0; v < nv; v++) for (int j = 0; j < 6; j++) if (adj[v][j] > v) fprintf(f, "%d %d\n", v, adj[v][j]);
    fclose(f);
}
static int dup_in_block(int b, int i, int v) {
    for (int j = 0; j < nS[b]; j++) if (j != i && par[b][j] == v) return 1;
    return 0;
}
/* coset parameter equivalence: for left cosets (blocks 2,5) v ~ old iff cK[v] == cK[old];
   for right cosets (blocks 6,7) v ~ old iff v = h*old for some h in H */
static int same_coset(int b, int old, int v) {
    if (b == 2 || b == 5) return cosl[ks][v] == cosl[ks][old];
    for (int j = 0; j < 3; j++) if (MUL(subel[hs][j], old) == v) return 1;
    return 0;
}
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: tabu3 TABLE A SEED STEPS TENURE TLIM OUT [STALL]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d", &m) != 1 || m > MAXM) return 1;
    T = malloc(sizeof(int) * m * m);
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 1;
    fclose(f);
    if (m % 3) return 1;
    q = m / 3;
    unw = getenv("UNW") != NULL;
    int a = atoi(argv[2]);
    if (a < 0 || a > 5) return 1;
    nS[0] = a; nS[1] = 5 - a; nS[2] = 1; nS[3] = 5 - a; nS[4] = a; nS[5] = 1; nS[6] = 1; nS[7] = 1;
    rs ^= (uint64_t)strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    long steps = atol(argv[4]); int tenure = atoi(argv[5]); double tlim = atof(argv[6]); const char *out = argv[7];
    long stallmax = argc > 8 ? atol(argv[8]) : 150;
    for (int x = 0; x < m; x++) { int y = x, o = 1; while (y != 0) { y = MUL(y, x); o++; } ord_[x] = o; }
    enum_sub();
    if (nsub == 0) { printf("no subgroups of order 3\n"); return 0; }
    for (int s = 0; s < nsub; s++) build_cosets(s);
    hs = rnd() % nsub; ks = rnd() % nsub;
    for (int b = 0; b < 8; b++) for (int i = 0; i < nS[b]; i++) {
        int ok;
        do { par[b][i] = rnd() % m; ok = !(is_elem(b) && dup_in_block(b, i, par[b][i])); } while (!ok);
    }
    if (getenv("INIT")) {   /* start from a saved .par file (8 block lines, then "H g K g ...") */
        FILE *fi = fopen(getenv("INIT"), "r");
        if (!fi) return 1;
        for (int b = 0; b < 8; b++) for (int i = 0; i < nS[b]; i++) if (fscanf(fi, "%d", &par[b][i]) != 1) return 1;
        int hg = 0, kg = 0;
        if (fscanf(fi, " H %d K %d", &hg, &kg) != 2) return 1;
        fclose(fi);
        for (int s = 0; s < nsub; s++) { if (subel[s][1] == hg || subel[s][2] == hg) hs = s; if (subel[s][1] == kg || subel[s][2] == kg) ks = s; }
    }
    int cur = cost_now(), best = cur;
    int bestpar[8][8], bh = hs, bk = ks; memcpy(bestpar, par, sizeof par);
    double t0 = now();
    printf("m %d a %d q %d nsub %d start %d\n", m, a, q, nsub, cur); fflush(stdout);
    if (cur < best + 0) { write_edges(out); }
    long stall = 0, it;
    for (it = 0; it < steps && best > 0 && now() - t0 < tlim; it++) {
        int bc = BIG + 1, mk = -1, mb = -1, mi = -1, mv = -1, nt = 0;   /* mk: 0 slot, 1 H, 2 K */
        /* element moves */
        for (int e = 0; e < 4; e++) { int b = ELEM_BLK[e];
            for (int i = 0; i < nS[b]; i++) { int old = par[b][i];
                for (int v = 0; v < m; v++) {
                    if (v == old || dup_in_block(b, i, v)) continue;
                    par[b][i] = v; int c = cost_now(); par[b][i] = old;
                    if (tabu_until[b][i] > it && c >= best) continue;
                    if (c < bc) { bc = c; mk = 0; mb = b; mi = i; mv = v; nt = 1; }
                    else if (c == bc) { nt++; if (rnd() % nt == 0) { mk = 0; mb = b; mi = i; mv = v; } }
                } } }
        /* coset moves */
        for (int e = 0; e < 4; e++) { int b = COS_BLK[e]; int old = par[b][0];
            for (int v = 0; v < m; v++) {
                if (v == old || same_coset(b, old, v)) continue;
                par[b][0] = v; int c = cost_now(); par[b][0] = old;
                if (tabu_until[b][0] > it && c >= best) continue;
                if (c < bc) { bc = c; mk = 0; mb = b; mi = 0; mv = v; nt = 1; }
                else if (c == bc) { nt++; if (rnd() % nt == 0) { mk = 0; mb = b; mi = 0; mv = v; } }
            } }
        /* subgroup moves (H then K) */
        for (int w = 0; w < 2; w++) {
            int saved = w ? ks : hs;
            for (int s = 0; s < nsub; s++) {
                if (s == saved) continue;
                if (w == 0) hs = s; else ks = s;
                int c = cost_now();
                if (w == 0) hs = saved; else ks = saved;
                if (tabu_sub[w] > it && c >= best) continue;
                if (c < bc) { bc = c; mk = 1 + w; mv = s; nt = 1; }
                else if (c == bc) { nt++; if (rnd() % nt == 0) { mk = 1 + w; mv = s; } }
            } }
        if (mk < 0) continue;
        if (mk == 0) { par[mb][mi] = mv; tabu_until[mb][mi] = it + tenure + (long)(rnd() % 3); }
        else if (mk == 1) { hs = mv; tabu_sub[0] = it + tenure; }
        else { ks = mv; tabu_sub[1] = it + tenure; }
        cur = cost_now();
        if (cur < best) {
            best = cur; memcpy(bestpar, par, sizeof par); bh = hs; bk = ks; stall = 0;
            printf("best %d step %ld t=%.1f\n", best, it, now() - t0); fflush(stdout);
            write_edges(out);
        } else stall++;
        if (getenv("VERB") && it % 100 == 0) { printf("step %ld cur %d best %d\n", it, cur, best); fflush(stdout); }
        if (stall > stallmax) {   /* perturbation: re-randomise two slots */
            stall = 0;
            int kick = getenv("KICK") ? atoi(getenv("KICK")) : 2; for (int p = 0; p < kick; p++) {
                int b = rnd() % 8; if (!nS[b]) continue; int i = rnd() % nS[b];
                int ok; do { par[b][i] = rnd() % m; ok = !(is_elem(b) && dup_in_block(b, i, par[b][i])); } while (!ok);
            }
            cur = cost_now();
        }
    }
    memcpy(par, bestpar, sizeof par); hs = bh; ks = bk;
    cost_now();
    printf("RESULT best %d steps %ld time %.1f\n", best, it, now() - t0);
    if (best == 0) printf("SOL\n");
    write_edges(out);
    { char fn[600]; snprintf(fn, sizeof fn, "%s.par", out); FILE *pf = fopen(fn, "w");
      if (pf) { for (int b = 0; b < 8; b++) { for (int i = 0; i < nS[b]; i++) fprintf(pf, "%d ", par[b][i]); fprintf(pf, "\n"); }
                fprintf(pf, "H %d K %d cost %d\n", subel[hs][1], subel[ks][1], best); fclose(pf); } }
    return 0;
}
