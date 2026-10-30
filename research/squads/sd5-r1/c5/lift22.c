/* lift22.c: regular lifts of the 4-vertex bipartite base [[a,b],[b,a]] (A0-B0 and A1-B1: a parallel edges,
 * A0-B1 and A1-B0: b = DELTA - a) by a group K given by its multiplication table (export.g format, identity 0).
 * Lift: vertices (v,h); a base edge A_i -> B_j of voltage g joins (A_i,h) and (B_j,h g).  K acts on the left, so
 * diameter <= 5 iff from (A_0,1), (A_1,1), (B_0,1), (B_1,1) everything is reached.  With E_ij the voltage set of
 * A_i - B_j, L(i,k) = U_j E_ij E_kj^-1 and R(j,l) = U_i E_ij^-1 E_il, the A-fibre k is reached from (A_i,1) within 4
 * steps iff U_l L(i,l) L(l,k) = K, the B-fibre l from (B_j,1) iff U_t R(j,t) R(t,l) = K.  Cost = sum of the uncovered
 * counts of the 6 conditions (i,k), (j,l) in {(0,0),(0,1),(1,1)}; the odd (A-B) condition is checked at cost 0.
 * Tree voltages E00[0] = E01[0] = E10[0] = 1.  Annealing over the other 11 voltages (SECS, SEED, T0 env).
 * usage: lift22 GROUP.ht a [OUT.edges]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int m; static uint16_t *mul; static int *inv;
#define M(x,y) mul[(size_t)(x) * m + (y)]
static int A, B;               /* a, b */
static int V[4][8], nv[4];     /* edge classes 0:(0,0) 1:(0,1) 2:(1,0) 3:(1,1) */
static uint32_t *stp; static uint32_t st = 0;
static long long evals = 0;

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }
static void load(const char *p) {
    FILE *f = fopen(p, "r"); if (!f) { perror(p); exit(1); }
    m = rdint(f); rdint(f);
    mul = malloc(2 * (size_t)m * m); inv = malloc(sizeof(int) * m);
    for (long i = 0; i < (long)m * m; i++) mul[i] = rdint(f);
    for (int i = 0; i < m; i++) inv[i] = rdint(f);
    fclose(f); stp = calloc(m, 4);
}
static int cls(int i, int j) { return i * 2 + j; }
/* build list of P(x,y) = U_j E_xj E_yj^-1 (left=1: A-side) or U_i E_ix^-1 E_iy (left=0) */
static int build(int left, int x, int y, int *out) {
    int n = 0; st++;
    for (int t = 0; t < 2; t++) {
        int c1 = left ? cls(x, t) : cls(t, x), c2 = left ? cls(y, t) : cls(t, y);
        for (int p = 0; p < nv[c1]; p++) for (int q = 0; q < nv[c2]; q++) {
            int z = left ? M(V[c1][p], inv[V[c2][q]]) : M(inv[V[c1][p]], V[c2][q]);
            if (stp[z] != st) { stp[z] = st; out[n++] = z; } }
    }
    return n;
}
static int P[2][2][2][64], nP[2][2][2];
static int cover(int left, int x, int y) {   /* uncovered count of U_l P(x,l) P(l,y) */
    st++; int cov = 0;
    for (int l = 0; l < 2; l++) { int *a = P[left][x][l], na = nP[left][x][l], *b = P[left][l][y], nb = nP[left][l][y];
        for (int i = 0; i < na; i++) { const uint16_t *row = mul + (size_t)a[i] * m;
            for (int j = 0; j < nb; j++) { int z = row[b[j]]; if (stp[z] != st) { stp[z] = st; cov++; } } } }
    return m - cov;
}
static int cost(void) {
    evals++;
    for (int left = 0; left < 2; left++) for (int x = 0; x < 2; x++) for (int y = 0; y < 2; y++) nP[left][x][y] = build(left, x, y, P[left][x][y]);
    int c = 0;
    for (int left = 0; left < 2; left++) { c += cover(left, 0, 0); c += cover(left, 0, 1); c += cover(left, 1, 1); }
    return c;
}
static void write_edges(const char *path) {
    FILE *f = fopen(path, "w"); fprintf(f, "%d\n", 4 * m);
    /* vertex index: A0 = 0..m-1, A1 = m.., B0 = 2m.., B1 = 3m.. */
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { int c = cls(i, j);
        for (int p = 0; p < nv[c]; p++) for (int h = 0; h < m; h++) fprintf(f, "%d %d\n", i * m + h, (2 + j) * m + M(h, V[c][p])); }
    fclose(f);
}
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: lift22 GROUP.ht a [OUT.edges]\n"); return 2; }
    load(argv[1]); A = atoi(argv[2]); B = (getenv("DELTA") ? atoi(getenv("DELTA")) : 7) - A;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 2.0;
    int seed = getenv("SEED") ? atoi(getenv("SEED")) : 1;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    nv[0] = A; nv[1] = B; nv[2] = B; nv[3] = A;
    int slots[32][2], ns = 0;
    for (int c = 0; c < 4; c++) for (int p = 0; p < nv[c]; p++) { V[c][p] = rnd() % m; if (p == 0 && c < 3) V[c][p] = 0; else { slots[ns][0] = c; slots[ns][1] = p; ns++; } }
    int cur = cost(), best = cur, BV[4][8]; memcpy(BV, V, sizeof V);
    double t0 = now(), T = T0; long it = 0;
    if (getenv("TABU")) {   /* tabu: each step tries NS random values for every slot, takes the best non-tabu move */
        int NS = getenv("NS") ? atoi(getenv("NS")) : 48, TEN = getenv("TEN") ? atoi(getenv("TEN")) : 15;
        long *tabu_until = calloc((size_t)ns * m, sizeof(long)); long step = 0; int stall = 0;
        while (now() - t0 < secs && best > 0) {
            step++; int bc = 1 << 30, bs = -1, bvv = -1;
            for (int s = 0; s < ns; s++) { int c = slots[s][0], p = slots[s][1], old = V[c][p];
                for (int r = 0; r < NS; r++) { int v = rnd() % m; if (v == old) continue;
                    int dup = 0; for (int q = 0; q < nv[c]; q++) if (V[c][q] == v) dup = 1; if (dup) continue;
                    V[c][p] = v; int c2 = cost(); V[c][p] = old;
                    if ((tabu_until[(size_t)s * m + v] > step && c2 >= best) ) continue;
                    if (c2 < bc || (c2 == bc && (rnd() & 1))) { bc = c2; bs = s; bvv = v; } } }
            if (bs < 0) continue;
            int c = slots[bs][0], p = slots[bs][1];
            tabu_until[(size_t)bs * m + V[c][p]] = step + TEN + rnd() % 5;
            V[c][p] = bvv; cur = bc;
            if (cur < best) { best = cur; memcpy(BV, V, sizeof V); stall = 0; } else stall++;
            if (stall > 400) { memcpy(V, BV, sizeof V); for (int k = 0; k < 3; k++) { int s = rnd() % ns; V[slots[s][0]][slots[s][1]] = rnd() % m; } cur = cost(); stall = 0; }
        }
        secs = -1;
    }
    while (secs > 0) {
        if ((it & 255) == 0) { double el = now() - t0; if (el > secs) break; T = T0 * (1 - el / secs) + 0.02; }
        it++;
        int s = rnd() % ns, c = slots[s][0], p = slots[s][1], old = V[c][p];
        int v = rnd() % m; if (v == old) continue;
        int dup = 0; for (int q = 0; q < nv[c]; q++) if (V[c][q] == v) dup = 1; if (dup) continue;
        V[c][p] = v; int c2 = cost();
        if (c2 <= cur || (rnd() >> 11) * (1.0 / 9007199254740992.0) < exp((cur - c2) / T)) { cur = c2;
            if (cur < best) { best = cur; memcpy(BV, V, sizeof V); if (best == 0) break; } }
        else V[c][p] = old;
    }
    memcpy(V, BV, sizeof V);
    int ok = 0;
    if (best == 0) { /* odd condition: (A_i,1) reaches B_j fibre within 5: U_l P(i,l) Q(l,j) with Q(l,j) = U_k P(l,k)E_kj */
        cost(); ok = 1;
        for (int i = 0; i < 2 && ok; i++) for (int j = 0; j < 2 && ok; j++) {
            char *mk = calloc(m, 1), *mk2 = calloc(m, 1);
            for (int l = 0; l < 2; l++) for (int k = 0; k < 2; k++) for (int x = 0; x < nP[1][i][l]; x++) for (int y = 0; y < nP[1][l][k]; y++) mk[M(P[1][i][l][x], P[1][l][k][y])] |= 1 << k;
            for (int z = 0; z < m; z++) for (int k = 0; k < 2; k++) if (mk[z] >> k & 1) for (int q = 0; q < nv[cls(k, j)]; q++) mk2[M(z, V[cls(k, j)][q])] = 1;
            for (int z = 0; z < m; z++) if (!mk2[z]) ok = 0;
            free(mk); free(mk2);
        }
        if (ok && argc > 3) write_edges(argv[3]);
    }
    printf("RESULT best %d odd_ok %d m %d a %d evals %lld secs %.0f volt", best, ok, m, A, evals, now() - t0);
    for (int c = 0; c < 4; c++) { printf(" |"); for (int p = 0; p < nv[c]; p++) printf(" %d", BV[c][p]); }
    printf("\n");
    return 0;
}
