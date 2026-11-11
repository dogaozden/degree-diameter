/* ctrl6.c: exact search for Delta = 10 route-chart lifts (5 letters x GF(2), fibre GF(2)^4; job cell-10-5).

   Base: 5-regular bipartite multigraph on k + k vertices.  Every base edge e = (a_i, b_j) carries
     a voltage v_e in a group G (table file), an offset c_e in GF(2)^4, and a chart entry (A_e, b_e),
     A_e in GL(4,2), b_e != 0.
   Lift: ((a_i, g), x) ~ ((b_j, v_e g), A_e x + c_e + lam b_e), lam in {0,1}.  10-regular, bipartite, 2*k*|G|*16
   vertices.  G acts by right multiplication, so the sources ((a_i, 1), x) and ((b_j, 1), y) suffice.
   EXACT cost: a same-side lift pair is within distance 4 iff some controller walk of length 0, 2 or 4 (backtracking
   allowed: the lift path may use the same controller edge twice with different lam) reaches it.  Every walk's
   reached set from x is computed by brute force over lam and stored as a 16-bit mask per x.
   cost = number of (source lift vertex, same-side target lift vertex) pairs at distance > 4.  0 <=> diameter <= 5.

   Modes: CHART=file (per-letter chart; colour = letter after PERM, Konig colouring); only voltages and offsets move.
          CHART unset: per-edge charts, annealed too (A_e by column bit flips, b_e by random change).
          Offsets start at 0 (RANDOFF=1: random) and move by bit flips or random changes unless NOOFF=1.
   usage: ctrl6 search BASE TABLE SECONDS SEED [OUT]
   env:   CHART, PERM (01234 or rand), CSEED, T0 (default 200, in lift-pair units), NOOFF=1 (offsets fixed at 0), INIT=solution file
          (start from it), WRITEBEST=1, PV (probability of a voltage move, default 0.5), TARGP (fraction of voltage
          moves that are targeted: random uncovered pair, random nonsingular walk to it, one voltage solved; default 0.3)
   OUT:   "ctrl6 k K n N cost C" then per base edge "i j v A0 A1 A2 A3 b c" (build_rc.py reads it).           */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (double)(xr() >> 11) / 9007199254740992.0; }

#define MAXK 16
#define MAXE (5 * MAXK)
#define MAXW 651
static int k, ne, EA[MAXE], EB[MAXE], col[MAXE], let[MAXE], n, *T, *Inv, e_id, istree[MAXE];
static int volt[MAXE], off[MAXE], Am[MAXE][4], Ainv[MAXE][4], bv[MAXE];
/* walks: per source s (0..k-1 = a_s, k..2k-1 = b_{s-k}) */
static int nw[2 * MAXK], wlen[2 * MAXK][MAXW], we[2 * MAXK][MAXW][4], wend[2 * MAXK][MAXW];
static uint64_t wmask[2 * MAXK][MAXW][4];       /* 16 masks of 16 bits: x = 4*q + r -> word q, bits 16r..16r+15 */
static uint64_t *U; static double TARGP = 0.3;
static inline int mul(int a, int b) { return T[a * n + b]; }
static inline int mv(const int *c, int x) { int y = 0; for (int r = 0; r < 4; r++) if (x >> r & 1) y ^= c[r]; return y; }
static int rank4(const int *v, int nv) { int basis[4] = {0}, r = 0;
    for (int i = 0; i < nv; i++) { int x = v[i]; for (int b = 3; b >= 0; b--) if (x >> b & 1) { if (basis[b]) x ^= basis[b]; else { basis[b] = x; r++; break; } } }
    return r; }
static int inverse(const int *c, int *ic) { int pre[16]; for (int x = 0; x < 16; x++) pre[x] = -1;
    for (int x = 0; x < 16; x++) { int y = mv(c, x); if (pre[y] >= 0) return 0; pre[y] = x; }
    for (int r = 0; r < 4; r++) ic[r] = pre[1 << r]; return 1; }

/* one lift step along base edge e from side s (0: A -> B, 1: B -> A) */
static inline int step(int x, int s, int e, int lam) {
    if (s == 0) return mv(Am[e], x) ^ off[e] ^ (lam ? bv[e] : 0);
    return mv(Ainv[e], x ^ off[e] ^ (lam ? bv[e] : 0));
}
/* reached set of a walk from x: A_W x + c_W + D_W (affine composition; D_W as a 16-bit subspace mask) */
static uint16_t coset_slow(uint16_t D, int t) { uint16_t m = 0; for (int y = 0; y < 16; y++) if (D >> y & 1) m |= 1 << (y ^ t); return m; }
static signed char SID[65536]; static uint16_t XTAB[67][16]; static int nsub = 0;
static void init_cosets(void) {   /* the 67 subspaces of GF(2)^4 and their 16 translates */
    memset(SID, -1, sizeof SID);
    for (int a = 0; a < 16; a++) for (int b = 0; b < 16; b++) for (int c = 0; c < 16; c++) for (int d = 0; d < 16; d++) {
        uint16_t D = 1; int g[4] = {a, b, c, d};
        for (int i = 0; i < 4; i++) { uint16_t D2 = D; for (int y = 0; y < 16; y++) if (D >> y & 1) D2 |= 1 << (y ^ g[i]); D = D2; }
        if (SID[D] < 0) { SID[D] = nsub; for (int t = 0; t < 16; t++) XTAB[nsub][t] = coset_slow(D, t); nsub++; } }
}
static inline uint16_t coset_mask(uint16_t D, int t) { return XTAB[(int)SID[D]][t]; }
static void walk_mask(int s, int w) {
    int side = s < k ? 0 : 1, L = wlen[s][w];
    int M[4] = {1, 2, 4, 8}, c = 0, dirs[4], nd = 0;          /* current map x -> M x + c, directions so far */
    for (int i = 0; i < L; i++) { int e = we[s][w][i];
        if (side == 0) {   /* x -> A x + off + lam b */
            int M2[4]; for (int r = 0; r < 4; r++) M2[r] = mv(Am[e], M[r]); memcpy(M, M2, sizeof M2);
            c = mv(Am[e], c) ^ off[e]; for (int d = 0; d < nd; d++) dirs[d] = mv(Am[e], dirs[d]); dirs[nd++] = bv[e];
        } else {           /* y -> Ainv (y + off + lam b) */
            int M2[4]; for (int r = 0; r < 4; r++) M2[r] = mv(Ainv[e], M[r]); memcpy(M, M2, sizeof M2);
            c = mv(Ainv[e], c ^ off[e]); for (int d = 0; d < nd; d++) dirs[d] = mv(Ainv[e], dirs[d]); dirs[nd++] = mv(Ainv[e], bv[e]);
        }
        side ^= 1; }
    uint16_t D = 1; for (int d = 0; d < nd; d++) { uint16_t D2 = D; for (int y = 0; y < 16; y++) if (D >> y & 1) D2 |= 1 << (y ^ dirs[d]); D = D2; }
    uint64_t m[4] = {0, 0, 0, 0};
    for (int x0 = 0; x0 < 16; x0++) m[x0 >> 2] |= (uint64_t)coset_mask(D, mv(M, x0) ^ c) << (16 * (x0 & 3));
    memcpy(wmask[s][w], m, sizeof m);
}
static void all_masks(void) { for (int s = 0; s < 2 * k; s++) for (int w = 0; w < nw[s]; w++) walk_mask(s, w); }
static int *ewS[MAXE], *ewW[MAXE], new_[MAXE];
static void build_edge_index(void) {
    for (int e = 0; e < ne; e++) { int c = 0;
        for (int s = 0; s < 2 * k; s++) for (int w = 0; w < nw[s]; w++) { int hit = 0; for (int i = 0; i < wlen[s][w]; i++) if (we[s][w][i] == e) hit = 1; c += hit; }
        ewS[e] = malloc(sizeof(int) * (c + 1)); ewW[e] = malloc(sizeof(int) * (c + 1)); new_[e] = 0;
        for (int s = 0; s < 2 * k; s++) for (int w = 0; w < nw[s]; w++) { int hit = 0; for (int i = 0; i < wlen[s][w]; i++) if (we[s][w][i] == e) hit = 1;
            if (hit) { ewS[e][new_[e]] = s; ewW[e][new_[e]] = w; new_[e]++; } } }
}
static void masks_for_edge(int e) { for (int i = 0; i < new_[e]; i++) walk_mask(ewS[e][i], ewW[e][i]); }
static inline int target(int s, int w) {
    int *E = we[s][w], L = wlen[s][w];
    if (L == 0) return e_id;
    if (s < k) { if (L == 2) return mul(Inv[volt[E[1]]], volt[E[0]]);
                 return mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]]))); }
    if (L == 2) return mul(volt[E[1]], Inv[volt[E[0]]]);
    return mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]])));
}
static long cost(void) {
    long c = 0; size_t sz = (size_t)k * n * 4;
    for (int s = 0; s < 2 * k; s++) {
        memset(U, 0, sz * sizeof(uint64_t));
        for (int w = 0; w < nw[s]; w++) { uint64_t *u = U + ((size_t)wend[s][w] * n + target(s, w)) * 4, *m = wmask[s][w];
            u[0] |= m[0]; u[1] |= m[1]; u[2] |= m[2]; u[3] |= m[3]; }
        long cov = 0; for (size_t i = 0; i < sz; i++) cov += __builtin_popcountll(U[i]);
        c += (long)k * n * 256 - cov;
    }
    return c;
}
/* pick a random uncovered (target index, x) for source s; returns 0 if s is fully covered */
static int pick_uncovered(int s, int *tix, int *xx) {
    size_t sz = (size_t)k * n * 4; memset(U, 0, sz * sizeof(uint64_t));
    for (int w = 0; w < nw[s]; w++) { uint64_t *u = U + ((size_t)wend[s][w] * n + target(s, w)) * 4, *m = wmask[s][w];
        u[0] |= m[0]; u[1] |= m[1]; u[2] |= m[2]; u[3] |= m[3]; }
    long cnt = 0;
    for (int t = 0; t < k * n; t++) for (int x = 0; x < 16; x++) {
        uint16_t m = (uint16_t)(U[(size_t)t * 4 + (x >> 2)] >> (16 * (x & 3)));
        if (m != 0xFFFF) { cnt++; if (xr() % cnt == 0) { *tix = t; *xx = x; } } }
    return cnt > 0;
}
/* set the voltage of one free edge of a random length-4 walk from s to base vertex tb so that it ends at group element g */
static int targeted(int s, int tb, int g, int *edge, int *newv) {
    int cand[MAXW], nc = 0;
    for (int w = 0; w < nw[s]; w++) if (wlen[s][w] == 4 && wend[s][w] == tb) {
        uint64_t *m = wmask[s][w]; if (m[0] == ~0ULL && m[1] == ~0ULL && m[2] == ~0ULL && m[3] == ~0ULL) cand[nc++] = w; }
    if (!nc) return 0;
    int w = cand[xr() % nc], *E = we[s][w], pos[4], np = 0;
    for (int i = 0; i < 4; i++) { if (istree[E[i]]) continue; int dup = 0; for (int j = 0; j < 4; j++) if (j != i && E[j] == E[i]) dup = 1; if (!dup) pos[np++] = i; }
    if (!np) return 0;
    int i = pos[xr() % np], v1 = volt[E[0]], v2 = volt[E[1]], v3 = volt[E[2]], v4 = volt[E[3]], x;
    if (s < k) {   /* value = v4^-1 v3 v2^-1 v1 */
        if (i == 0) x = mul(v2, mul(Inv[v3], mul(v4, g)));
        else if (i == 1) x = mul(v1, mul(Inv[g], mul(Inv[v4], v3)));
        else if (i == 2) x = mul(v4, mul(g, mul(Inv[v1], v2)));
        else x = mul(v3, mul(Inv[v2], mul(v1, Inv[g])));
    } else {       /* value = v4 v3^-1 v2 v1^-1 */
        if (i == 0) x = mul(Inv[g], mul(v4, mul(Inv[v3], v2)));
        else if (i == 1) x = mul(v3, mul(Inv[v4], mul(g, v1)));
        else if (i == 2) x = mul(v2, mul(Inv[v1], mul(Inv[g], v4)));
        else x = mul(g, mul(v1, mul(Inv[v2], v3)));
    }
    *edge = E[i]; *newv = x; return 1;
}
static int parallel_ok(void) {   /* parallel base edges need distinct voltages (simple controller) */
    for (int a = 0; a < ne; a++) for (int b = a + 1; b < ne; b++) if (EA[a] == EA[b] && EB[a] == EB[b] && volt[a] == volt[b]) return 0;
    return 1;
}
static int used[MAXE], matchB[MAXK], visB[MAXK];
static int aug(int a) {
    int es[MAXE], m = 0; for (int e = 0; e < ne; e++) if (!used[e] && EA[e] == a) es[m++] = e;
    for (int i = m - 1; i > 0; i--) { int j = xr() % (i + 1), t = es[i]; es[i] = es[j]; es[j] = t; }
    for (int q = 0; q < m; q++) { int e = es[q]; if (visB[EB[e]]) continue; visB[EB[e]] = 1;
        if (matchB[EB[e]] < 0 || aug(EA[matchB[EB[e]]])) { matchB[EB[e]] = e; return 1; } }
    return 0;
}
static void colour(void) {
    memset(used, 0, sizeof used); int ord[MAXK];
    for (int c = 0; c < 5; c++) {
        for (int j = 0; j < k; j++) matchB[j] = -1;
        for (int a = 0; a < k; a++) ord[a] = a;
        for (int i = k - 1; i > 0; i--) { int j = xr() % (i + 1), t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        for (int q = 0; q < k; q++) { memset(visB, 0, sizeof visB); if (!aug(ord[q])) { printf("colouring failed\n"); exit(9); } }
        for (int j = 0; j < k; j++) { col[matchB[j]] = c; used[matchB[j]] = 1; }
    }
}
static void build_walks(void) {
    for (int s = 0; s < 2 * k; s++) { int c = 0;
        wlen[s][c] = 0; wend[s][c] = s % k; c++;
        int side = s < k ? 0 : 1, v = s % k;
        for (int e1 = 0; e1 < ne; e1++) if ((side == 0 ? EA[e1] : EB[e1]) == v) {
            int v1 = side == 0 ? EB[e1] : EA[e1];
            for (int e2 = 0; e2 < ne; e2++) if ((side == 0 ? EB[e2] : EA[e2]) == v1) {
                int v2 = side == 0 ? EA[e2] : EB[e2];
                wlen[s][c] = 2; we[s][c][0] = e1; we[s][c][1] = e2; wend[s][c] = v2; c++;
                for (int e3 = 0; e3 < ne; e3++) if ((side == 0 ? EA[e3] : EB[e3]) == v2) {
                    int v3 = side == 0 ? EB[e3] : EA[e3];
                    for (int e4 = 0; e4 < ne; e4++) if ((side == 0 ? EB[e4] : EA[e4]) == v3) {
                        int v4 = side == 0 ? EA[e4] : EB[e4];
                        wlen[s][c] = 4; we[s][c][0] = e1; we[s][c][1] = e2; we[s][c][2] = e3; we[s][c][3] = e4; wend[s][c] = v4; c++; } } } }
        nw[s] = c; if (c > MAXW) { printf("too many walks\n"); exit(8); }
    }
}
static void random_gl(int *c) { for (;;) { for (int r = 0; r < 4; r++) c[r] = xr() % 16; if (rank4(c, 4) == 4) return; } }

int main(int argc, char **argv) {
    if (argc < 6 || strcmp(argv[1], "search")) { printf("usage: ctrl6 search BASE TABLE SECONDS SEED [OUT]\n"); return 1; }
    FILE *f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &k) != 1 || k > MAXK) { printf("bad base\n"); return 2; }
    ne = 5 * k; for (int i = 0; i < ne; i++) if (fscanf(f, "%d %d", &EA[i], &EB[i]) != 2) { printf("bad base edge\n"); return 3; }
    fclose(f);
    f = fopen(argv[3], "r"); if (!f || fscanf(f, "%d", &n) != 1) { printf("bad table\n"); return 4; }
    T = malloc(sizeof(int) * n * n); Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) { printf("bad table entry\n"); return 5; }
    fclose(f);
    e_id = -1; for (int i = 0; i < n && e_id < 0; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e_id = i; }
    for (int i = 0; i < n; i++) { Inv[i] = -1; for (int j = 0; j < n; j++) if (T[i * n + j] == e_id) Inv[i] = j; }
    double secs = atof(argv[4]); uint64_t seed = (uint64_t)atoll(argv[5]); const char *out = argc > 6 ? argv[6] : NULL;
    rs ^= (getenv("CSEED") ? (uint64_t)atoll(getenv("CSEED")) : seed) * 0x9E3779B97F4A7C15ULL + 12345; if (!rs) rs = 1;
    U = malloc(sizeof(uint64_t) * k * n * 4);
    int letter_mode = getenv("CHART") != NULL, nooff = getenv("NOOFF") != NULL;
    int chA[5][4], chB[5];
    colour();
    int perm[5] = {0, 1, 2, 3, 4}; const char *P = getenv("PERM");
    if (P && !strcmp(P, "rand")) { for (int i = 4; i > 0; i--) { int j = xr() % (i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; } }
    else if (P && strlen(P) == 5) for (int c = 0; c < 5; c++) perm[c] = P[c] - '0';
    for (int e = 0; e < ne; e++) let[e] = perm[col[e]];
    rs ^= seed * 0xD1B54A32D192ED03ULL + 777; if (!rs) rs = 1;
    if (letter_mode) { FILE *g = fopen(getenv("CHART"), "r"); if (!g) { printf("no chart\n"); return 6; }
        for (int t = 0; t < 5; t++) if (fscanf(g, "%d %d %d %d %d", &chA[t][0], &chA[t][1], &chA[t][2], &chA[t][3], &chB[t]) != 5) { printf("bad chart\n"); return 6; }
        fclose(g); }
    int seen[2 * MAXK] = {0}, q[2 * MAXK], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int x = q[h++];
        for (int i = 0; i < ne; i++) { int a = EA[i], b = k + EB[i], y = -1;
            if (x == a && !seen[b]) y = b; else if (x == b && !seen[a]) y = a;
            if (y >= 0) { seen[y] = 1; q[t++] = y; istree[i] = 1; } } }
    if (t != 2 * k) { printf("base disconnected\n"); return 7; }
    init_cosets(); build_walks(); build_edge_index();
    for (int e = 0; e < ne; e++) {
        if (letter_mode) { memcpy(Am[e], chA[let[e]], sizeof(int) * 4); bv[e] = chB[let[e]]; }
        else { random_gl(Am[e]); bv[e] = 1 + xr() % 15; }
        inverse(Am[e], Ainv[e]); off[e] = 0;
    }
    int randoff = getenv("RANDOFF") != NULL;
    do { for (int i = 0; i < ne; i++) { volt[i] = istree[i] ? e_id : (int)(xr() % n); if (!nooff && randoff) off[i] = xr() % 16; } } while (!parallel_ok());
    if (getenv("INIT")) { FILE *g = fopen(getenv("INIT"), "r"); char buf[256]; if (!g || !fgets(buf, sizeof buf, g)) { printf("bad INIT\n"); return 9; }
        for (int e = 0; e < ne; e++) { int i, j, v, a0, a1, a2, a3, b, c; if (fscanf(g, "%d %d %d %d %d %d %d %d %d", &i, &j, &v, &a0, &a1, &a2, &a3, &b, &c) != 9) { printf("bad INIT line\n"); return 9; }
            volt[e] = v; Am[e][0] = a0; Am[e][1] = a1; Am[e][2] = a2; Am[e][3] = a3; bv[e] = b; off[e] = c; inverse(Am[e], Ainv[e]); }
        fclose(g); }
    all_masks();
    double T0 = getenv("T0") ? atof(getenv("T0")) : 200.0, PV = getenv("PV") ? atof(getenv("PV")) : 0.5;
    TARGP = getenv("TARGP") ? atof(getenv("TARGP")) : 0.3;
    long c = cost(), best = c;
    int b_volt[MAXE], b_off[MAXE], b_A[MAXE][4], b_b[MAXE];
    memcpy(b_volt, volt, sizeof volt); memcpy(b_off, off, sizeof off); memcpy(b_A, Am, sizeof Am); memcpy(b_b, bv, sizeof bv);
    int free_e[MAXE], nf = 0; for (int i = 0; i < ne; i++) if (!istree[i]) free_e[nf++] = i;
    clock_t t0 = clock(); long it = 0, last_imp = 0;
    printf("start cost %ld (k=%d n=%d m=%d, walks/source %d)\n", c, k, n, k * n, nw[0]); fflush(stdout);
    while (best > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs, TT = T0 * pow(0.05, fr);
        double r = urand(); int e, kind;
        if (r < PV) { kind = 0; e = free_e[xr() % nf]; }
        else { e = xr() % ne; if (letter_mode) { if (nooff) continue; kind = 1; } else { double r2 = urand(); kind = nooff ? (r2 < 0.6 ? 2 : 3) : (r2 < 0.4 ? 1 : r2 < 0.8 ? 2 : 3); } }
        int sv = volt[e], so = off[e], sA[4], sAi[4], sb = bv[e]; memcpy(sA, Am[e], sizeof sA); memcpy(sAi, Ainv[e], sizeof sAi);
        if (kind == 0) {
            if (urand() < TARGP) { int s = xr() % (2 * k), tix, xx, ed, nv;
                if (!pick_uncovered(s, &tix, &xx) || !targeted(s, tix / n, tix % n, &ed, &nv)) continue;
                e = ed; sv = volt[e]; volt[e] = nv; }
            else volt[e] = xr() % n;
            if (volt[e] == sv || !parallel_ok()) { volt[e] = sv; continue; } }
        else if (kind == 1) { off[e] = urand() < 0.5 ? (off[e] ^ (1 << (xr() % 4))) : (int)(xr() % 16); masks_for_edge(e); }
        else if (kind == 2) { Am[e][xr() % 4] ^= 1 << (xr() % 4); if (rank4(Am[e], 4) < 4) { memcpy(Am[e], sA, sizeof sA); continue; } inverse(Am[e], Ainv[e]); masks_for_edge(e); }
        else { bv[e] = 1 + xr() % 15; if (bv[e] == sb) continue; masks_for_edge(e); }
        long c2 = cost();
        if (c2 <= c || exp((c - c2) / TT) > urand()) { c = c2;
            if (c < best) { best = c; last_imp = it; memcpy(b_volt, volt, sizeof volt); memcpy(b_off, off, sizeof off); memcpy(b_A, Am, sizeof Am); memcpy(b_b, bv, sizeof bv); } }
        else { volt[e] = sv; off[e] = so; memcpy(Am[e], sA, sizeof sA); memcpy(Ainv[e], sAi, sizeof sAi); bv[e] = sb; if (kind) masks_for_edge(e); }
        if (it - last_imp > 200000 && c > best) { memcpy(volt, b_volt, sizeof volt); memcpy(off, b_off, sizeof off); memcpy(Am, b_A, sizeof Am); memcpy(bv, b_b, sizeof bv);
            for (int x = 0; x < ne; x++) inverse(Am[x], Ainv[x]); all_masks(); c = best; last_imp = it; }
        if (getenv("REPORT") && it % 200000 == 0) { printf("  it %ld cost %ld best %ld T %.3f\n", it, c, best, TT); fflush(stdout); }
    }
    printf("k=%d n=%d m=%d mode=%s perm=%d%d%d%d%d best_cost=%ld iters=%ld time=%.1f\n", k, n, k * n, letter_mode ? "letter" : "edge",
           perm[0], perm[1], perm[2], perm[3], perm[4], best, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (out && (best == 0 || getenv("WRITEBEST"))) { FILE *g = fopen(out, "w");
        fprintf(g, "ctrl6 k %d n %d cost %ld\n", k, n, best);
        for (int i = 0; i < ne; i++) fprintf(g, "%d %d %d %d %d %d %d %d %d\n", EA[i], EB[i], b_volt[i], b_A[i][0], b_A[i][1], b_A[i][2], b_A[i][3], b_b[i], b_off[i]);
        fclose(g); }
    return 0;
}
