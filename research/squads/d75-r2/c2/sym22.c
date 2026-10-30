/* sym22.c (squad card c2): SELF-DUAL 4-vertex-base lifts, non-Haar.
 * Base: A0,A1,B0,B1 with voltage sets E00 (a), E01 (b), E10 (b), E11 (a), a + b = DELTA (7 for the (7,5) cell,
 * 5 for the (5,5) calibration).  Lift by a group K (left regular action, (A_i,h) ~ (B_j, h v), v in E_ij),
 * exactly as lift22.c.  Symmetry (beta in Aut(K), beta^2 = 1):
 *   E11 = psi(E00),  E01 = psi(E01),  E10 = psi(E10),   psi(v) = beta(v)^-1,
 * which gives the colour-swapping automorphism (A0,h)<->(B1,beta h), (A1,h)<->(B0,beta h).  The B-side conditions
 * then follow from the A-side ones, so cost = uncovered counts of the 3 A-side conditions (0,0),(0,1),(1,1) only.
 * Gauge: a symmetric-preserving gauge (E_ij -> a_i^-1 E_ij b_j with b_1 = beta(a_0), b_0 = beta(a_1)) lets us put
 * the identity into E00 w.l.o.g.; E00 = {1} + (a-1) free elements, E01/E10 = unions of psi-orbits of total size b
 * (orbits: fixed points beta(v) = v^-1 and pairs {v, psi(v)}), E11 = psi(E00) (contains 1 too).
 * Search: simulated annealing over these sets (moves: replace one element of E00; swap one psi-orbit of E01/E10 for
 * another of the same size; trade a pair for two fixed points or back).  All beta with p = 1 (identity) or p = 2
 * from the ALPHA lines of GROUP.ht are tried (BETAS env selects indices).  On cost 0 the odd (A to B within 5)
 * condition is checked and, if it holds, the edge list is written (verify with apsp EDGES d 5).
 * usage: sym22 GROUP.ht a [OUT.edges]      env: DELTA (7), SECS (per beta, 20), SEED (1), T0 (1.0), BETAS (all),
 *        ALL=1 (keep going after a hit; default stop at the first hit).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int m; static uint16_t *mul; static int *inv;
#define M(x, y) mul[(size_t)(x) * m + (y)]
static int A, B;                     /* a = |E00| = |E11|, b = |E01| = |E10| */
static int nbeta; static int beta_p[128]; static int *beta_perm[128];
static int *psi, norb, *orbSz, (*orbEl)[2], *orbOf, *singles, nsing, *pairs, npair;
static long long evals = 0;
static uint32_t *stp; static uint32_t st = 0;

typedef struct { int S00[8]; int sel[2][8]; int nsel[2]; } St;
static St bst;
static int E[4][8], nE[4];           /* class 0:(0,0) 1:(0,1) 2:(1,0) 3:(1,1) */
#define MAXP 128
static int Pset[2][2][2][MAXP], nP[2][2][2];

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }
static void load(const char *p) {
    FILE *f = fopen(p, "r"); if (!f) { perror(p); exit(1); }
    m = rdint(f); rdint(f);
    mul = malloc(2 * (size_t)m * m); inv = malloc(sizeof(int) * m);
    for (long i = 0; i < (long)m * m; i++) mul[i] = rdint(f);
    for (int i = 0; i < m; i++) inv[i] = rdint(f);
    char w[32];
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "ALPHA")) {
            int p = rdint(f); int *perm = malloc(sizeof(int) * m);
            for (int i = 0; i < m; i++) perm[i] = rdint(f);
            if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
            int k = rdint(f); for (int j = 0; j < k; j++) for (int i = 0; i < m; i++) rdint(f);
            if ((p == 1 || p == 2) && nbeta < 128) { beta_p[nbeta] = p; beta_perm[nbeta] = perm; nbeta++; }
            else free(perm);
        }
    }
    fclose(f);
    stp = calloc(m, 4);
}
static inline int cls(int i, int j) { return i * 2 + j; }

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* psi-orbits for beta */
static void orbits(const int *beta) {
    free(psi); free(orbSz); free(orbEl); free(orbOf); free(singles); free(pairs);
    psi = malloc(sizeof(int) * m); orbOf = malloc(sizeof(int) * m);
    orbSz = malloc(sizeof(int) * m); orbEl = malloc(sizeof(*orbEl) * m);
    singles = malloc(sizeof(int) * m); pairs = malloc(sizeof(int) * m); nsing = npair = 0; norb = 0;
    for (int v = 0; v < m; v++) psi[v] = inv[beta[v]];
    for (int v = 0; v < m; v++) orbOf[v] = -1;
    for (int v = 0; v < m; v++) if (orbOf[v] < 0) {
        int o = norb++; orbOf[v] = o; orbEl[o][0] = v;
        if (psi[v] == v) { orbSz[o] = 1; singles[nsing++] = o; }
        else { orbSz[o] = 2; orbEl[o][1] = psi[v]; orbOf[psi[v]] = o; pairs[npair++] = o; }
    }
}
static int in_arr(const int *a, int n, int v) { for (int i = 0; i < n; i++) if (a[i] == v) return 1; return 0; }

static void expand(const St *s) {
    nE[0] = A; for (int k = 0; k < A; k++) E[0][k] = s->S00[k];
    nE[3] = A; for (int k = 0; k < A; k++) E[3][k] = psi[s->S00[k]];
    for (int c = 0; c < 2; c++) { int n = 0;
        for (int t = 0; t < s->nsel[c]; t++) { int o = s->sel[c][t]; for (int q = 0; q < orbSz[o]; q++) E[c + 1][n++] = orbEl[o][q]; }
        nE[c + 1] = n; }
}
static void build(int left) {
    for (int x = 0; x < 2; x++) for (int y = 0; y < 2; y++) {
        st++; int n = 0;
        for (int t = 0; t < 2; t++) {
            int c1 = left ? cls(x, t) : cls(t, x), c2 = left ? cls(y, t) : cls(t, y);
            for (int p = 0; p < nE[c1]; p++) for (int q = 0; q < nE[c2]; q++) {
                int z = left ? M(E[c1][p], inv[E[c2][q]]) : M(inv[E[c1][p]], E[c2][q]);
                if (stp[z] != st) { stp[z] = st; if (n < MAXP) Pset[left][x][y][n++] = z; } }
        }
        nP[left][x][y] = n;
    }
}
static int cover(int left, int x, int y) {   /* uncovered count of U_l P(x,l) P(l,y) */
    st++; int cov = 0;
    for (int l = 0; l < 2; l++) { int *a = Pset[left][x][l], na = nP[left][x][l], *b = Pset[left][l][y], nb = nP[left][l][y];
        for (int i = 0; i < na; i++) { const uint16_t *row = mul + (size_t)a[i] * m;
            for (int j = 0; j < nb; j++) { int z = row[b[j]]; if (stp[z] != st) { stp[z] = st; cov++; } } } }
    return m - cov;
}
/* A-side cost (the search cost) */
static int cost_A(const St *s) {
    evals++; expand(s); build(1);
    return cover(1, 0, 0) + cover(1, 0, 1) + cover(1, 1, 1);
}
/* full 6-condition cost, for the final check */
static int cost_full(const St *s) {
    expand(s); build(1); build(0);
    int c = 0;
    for (int left = 0; left < 2; left++) { c += cover(left, 0, 0); c += cover(left, 0, 1); c += cover(left, 1, 1); }
    return c;
}
static int odd_ok(void) {   /* (A_i,1) reaches every B_j fibre within 5 (after expand/build(1) of the state) */
    build(1);
    char *mk = calloc(m, 1), *mk2 = calloc(m, 1); int ok = 1;
    for (int i = 0; i < 2 && ok; i++) for (int j = 0; j < 2 && ok; j++) {
        memset(mk, 0, m); memset(mk2, 0, m);
        for (int l = 0; l < 2; l++) for (int k = 0; k < 2; k++)
            for (int x = 0; x < nP[1][i][l]; x++) for (int y = 0; y < nP[1][l][k]; y++) mk[M(Pset[1][i][l][x], Pset[1][l][k][y])] |= 1 << k;
        for (int z = 0; z < m; z++) for (int k = 0; k < 2; k++) if (mk[z] >> k & 1) for (int q = 0; q < nE[cls(k, j)]; q++) mk2[M(z, E[cls(k, j)][q])] = 1;
        for (int z = 0; z < m; z++) if (!mk2[z]) ok = 0;
    }
    free(mk); free(mk2);
    return ok;
}
static void write_edges(const char *path) {
    FILE *f = fopen(path, "w"); fprintf(f, "%d\n", 4 * m);
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { int c = cls(i, j); expand(&bst);
        for (int p = 0; p < nE[c]; p++) for (int h = 0; h < m; h++) fprintf(f, "%d %d\n", i * m + h, (2 + j) * m + M(h, E[c][p])); }
    fclose(f);
}
static void print_state(const St *s) {
    expand(s);
    for (int c = 0; c < 4; c++) { printf(" |"); for (int p = 0; p < nE[c]; p++) printf(" %d", E[c][p]); }
    printf("\n");
}
static int pick_free(const St *s, int *list, int nl, int c);
/* random legal selection of total size b for class c (uses singles/pairs) */
static int rand_sel(int c, int b, St *s) {
    for (int tries = 0; tries < 1000; tries++) {
        int ns = rnd() % (nsing + 1); if (ns > b) continue; if ((b - ns) % 2) continue;
        int np = (b - ns) / 2; if (np > npair) continue;
        s->nsel[c] = 0; int ok = 1;
        for (int t = 0; t < ns && ok; t++) { int o = pick_free(s, singles, nsing, c); if (o < 0) ok = 0; else s->sel[c][s->nsel[c]++] = o; }
        for (int t = 0; t < np && ok; t++) { int o = pick_free(s, pairs, npair, c); if (o < 0) ok = 0; else s->sel[c][s->nsel[c]++] = o; }
        if (ok) return 1;
    }
    return 0;
}
static int rand_S00(St *s) {
    s->S00[0] = 0;
    for (int k = 1; k < A; k++) { int v; do v = 1 + rnd() % (m - 1); while (in_arr(s->S00, k, v)); s->S00[k] = v; }
    return 1;
}
static int free_single(const St *s, int c) { int cnt = 0; for (int t = 0; t < nsing; t++) if (!in_arr(s->sel[c], s->nsel[c], singles[t])) cnt++; return cnt; }
static int free_pair(const St *s, int c) { int cnt = 0; for (int t = 0; t < npair; t++) if (!in_arr(s->sel[c], s->nsel[c], pairs[t])) cnt++; return cnt; }
static int pick_free(const St *s, int *list, int nl, int c) {   /* random orbit of list not selected in class c */
    for (int tt = 0; tt < 30; tt++) { int o = list[rnd() % nl]; if (!in_arr(s->sel[c], s->nsel[c], o)) return o; }
    int cand[512], nc = 0;
    for (int t = 0; t < nl; t++) if (!in_arr(s->sel[c], s->nsel[c], list[t])) cand[nc++] = list[t];
    return nc ? cand[rnd() % nc] : -1;
}
/* propose a neighbour of s into t; returns 0 if no move */
static int propose(const St *s, St *t) {
    *t = *s; int r = rnd() % 100;
    if (r < 25 && A >= 2) {                     /* replace one element of E00 */
        int k = 1 + rnd() % (A - 1), v; do v = 1 + rnd() % (m - 1); while (in_arr(t->S00, A, v));
        t->S00[k] = v; return 1;
    }
    int c = rnd() % 2;
    if (r < 75) {                               /* swap an orbit of E01/E10 for a free orbit of equal size */
        if (t->nsel[c] == 0) return 0;
        int k = rnd() % t->nsel[c], o = t->sel[c][k];
        int o2 = (orbSz[o] == 1) ? pick_free(t, singles, nsing, c) : pick_free(t, pairs, npair, c);
        if (o2 < 0) return 0;
        t->sel[c][k] = o2; return 1;
    }
    /* trade: pair -> two singles, or two singles -> pair */
    int np = 0, ns = 0; for (int k = 0; k < t->nsel[c]; k++) { if (orbSz[t->sel[c][k]] == 2) np++; else ns++; }
    int opt = rnd() % 2;
    if (opt == 0 && np >= 1 && free_single(t, c) >= 2) {
        int k = 0; while (orbSz[t->sel[c][k]] != 2) k++;
        t->sel[c][k] = t->sel[c][--t->nsel[c]];
        int a1 = pick_free(t, singles, nsing, c); t->sel[c][t->nsel[c]++] = a1;
        int a2 = pick_free(t, singles, nsing, c); t->sel[c][t->nsel[c]++] = a2;
        return 1;
    }
    if (opt == 1 && ns >= 2 && free_pair(t, c) >= 1) {
        int cnt = 0;
        for (int k = 0; k < t->nsel[c] && cnt < 2; ) { if (orbSz[t->sel[c][k]] == 1) { t->sel[c][k] = t->sel[c][--t->nsel[c]]; cnt++; } else k++; }
        int p = pick_free(t, pairs, npair, c); t->sel[c][t->nsel[c]++] = p; return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IOLBF, 0);
    if (argc < 3) { fprintf(stderr, "usage: sym22 GROUP.ht a [OUT.edges]\n"); return 2; }
    load(argv[1]); A = atoi(argv[2]); B = (getenv("DELTA") ? atoi(getenv("DELTA")) : 7) - A;
    if (A < 1 || B < 1 || A > 7 || B > 7) { fprintf(stderr, "bad a\n"); return 2; }
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 20, T0 = getenv("T0") ? atof(getenv("T0")) : 1.0;
    int seed = getenv("SEED") ? atoi(getenv("SEED")) : 1; int all = getenv("ALL") != NULL;
    const char *bsel = getenv("BETAS");
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int nhits = 0; long long tot = 0;
    for (int bi = 0; bi < nbeta; bi++) {
        if (bsel) { char buf[1024]; strncpy(buf, bsel, 1023); buf[1023] = 0; int want = 0; char *tk = strtok(buf, ","); int found = 0;
            while (tk) { if (atoi(tk) == bi) found = 1; tk = strtok(NULL, ","); } want = found; if (!want) continue; }
        int *beta = beta_perm[bi]; int inv2 = 1;
        for (int v = 0; v < m; v++) if (beta[beta[v]] != v) { inv2 = 0; break; }
        if (!inv2) { printf("beta %d skipped (beta^2 != 1)\n", bi); continue; }
        orbits(beta);
        int fixed = nsing;
        printf("beta %d p %d fixed %d orbits %d (pairs %d)\n", bi, beta_p[bi], nsing, norb, npair);
        if (nsing == 0 && (B % 2)) { printf("  no fixed points and odd b: skip\n"); continue; }
        int bestc = 1 << 30; int found = 0; long long it = 0; double t0 = now(), T = T0;
        St s, t; int ok = 1;
        ok &= rand_S00(&s); ok &= rand_sel(0, B, &s); ok &= rand_sel(1, B, &s);
        if (!ok) { printf("  cannot build initial sets\n"); continue; }
        int c = cost_A(&s), cs = c; bst = s; bestc = c;
        while (1) {
            if ((it & 1023) == 0) { double el = now() - t0; if (el > secs) break; T = T0 * (1 - el / secs) + 0.01; }
            it++;
            if (!propose(&s, &t)) continue;
            int c2 = cost_A(&t);
            if (c2 <= cs || (rnd() >> 11) * (1.0 / 9007199254740992.0) < exp((cs - c2) / T)) {
                s = t; cs = c2;
                if (cs < bestc) { bestc = cs; bst = s; }
                if (cs == 0) {
                    /* full check: all 6 conditions and the odd condition */
                    int cf = cost_full(&s);
                    if (cf == 0) {
                        expand(&s);
                        if (odd_ok()) { found = 1; break; }
                    }
                }
            }
        }
        tot += it;
        printf("RESULT beta %d p %d fixed %d best %d found %d iters %lld secs %.1f\n", bi, beta_p[bi], fixed, bestc, found, it, now() - t0);
        if (found) {
            nhits++; printf("HIT beta %d  volt", bi); print_state(&s);
            if (argc > 3) { bst = s; char path[1024]; snprintf(path, sizeof path, "%s", argv[3]); write_edges(path); }
            if (!all) break;
        }
    }
    printf("DONE hits %d evals %lld n %d a %d b %d\n", nhits, evals, m, A, B);
    return 0;
}
