/* B3: formal identities among non-backtracking B-side walks of length <= MAXL on H(G,S), G = PSL(2,243) x Z_11.
 * Same model as ident_walks.py: letters e and the alpha-orbit(s) of K random generators; a walk's value is the
 * group element for every generator (two generators give a 128-bit key; accidental equality ~ 1e-6 here).
 * usage: ident7 MODE MAXL SEED   MODE = k10 (alpha = conj(h) o Frobenius, z -> 2z) | k5 (Frobenius, z -> 3z, 2 orbits) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint8_t MUL[243][243], ADDT[243][243], NEG[243], INVT[243];
static int dig(int x, int i) { for (int k = 0; k < i; k++) x /= 3; return x % 3; }
static void build_field(void) {
    for (int a = 0; a < 243; a++) for (int b = 0; b < 243; b++) {
        int ca[5], cb[5], r[9] = {0};
        for (int i = 0; i < 5; i++) { ca[i] = dig(a, i); cb[i] = dig(b, i); }
        for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) r[i + j] = (r[i + j] + ca[i] * cb[j]) % 3;
        for (int d = 8; d >= 5; d--) { int c = r[d]; if (c) { r[d] = 0; r[d - 4] = (r[d - 4] + c) % 3; r[d - 5] = (r[d - 5] + 2 * c) % 3; } }
        int s = 0, p = 1; for (int i = 0; i < 5; i++) { s += r[i] * p; p *= 3; }
        MUL[a][b] = (uint8_t)s;
        int t = 0; p = 1; for (int i = 0; i < 5; i++) { t += ((dig(a, i) + dig(b, i)) % 3) * p; p *= 3; }
        ADDT[a][b] = (uint8_t)t;
    }
    for (int a = 0; a < 243; a++) {
        int s = 0, p = 1; for (int i = 0; i < 5; i++) { s += ((3 - dig(a, i)) % 3) * p; p *= 3; } NEG[a] = (uint8_t)s;
    }
    for (int a = 1; a < 243; a++) for (int b = 1; b < 243; b++) if (MUL[a][b] == 1) INVT[a] = (uint8_t)b;
}
typedef uint64_t E;   /* group element: matrix (a,b,c,d) packed in bits 8..39 (a<<32|b<<24|c<<16|d<<8 ...) and z in bits 0..7 */
static uint32_t pk(int a, int b, int c, int d) { return ((uint32_t)a << 24) | ((uint32_t)b << 16) | ((uint32_t)c << 8) | (uint32_t)d; }
static uint32_t canonm(int a, int b, int c, int d) {
    uint32_t m = pk(a, b, c, d), n = pk(NEG[a], NEG[b], NEG[c], NEG[d]); return m < n ? m : n;
}
static E mk(uint32_t m, int z) { return ((E)m << 8) | (uint32_t)z; }
static uint32_t MOF(E g) { return (uint32_t)(g >> 8); }
static int ZOF(E g) { return (int)(g & 255); }
static uint8_t AB(uint32_t m, int s) { return (uint8_t)(m >> s); }
static E gmul(E g, E h) {
    uint32_t m1 = MOF(g), m2 = MOF(h);
    int a1 = AB(m1, 24), b1 = AB(m1, 16), c1 = AB(m1, 8), d1 = AB(m1, 0);
    int a2 = AB(m2, 24), b2 = AB(m2, 16), c2 = AB(m2, 8), d2 = AB(m2, 0);
    int A = ADDT[MUL[a1][a2]][MUL[b1][c2]], B = ADDT[MUL[a1][b2]][MUL[b1][d2]];
    int C = ADDT[MUL[c1][a2]][MUL[d1][c2]], D = ADDT[MUL[c1][b2]][MUL[d1][d2]];
    return mk(canonm(A, B, C, D), (ZOF(g) + ZOF(h)) % 11);
}
static E ginv(E g) {
    uint32_t m = MOF(g); int a = AB(m, 24), b = AB(m, 16), c = AB(m, 8), d = AB(m, 0);
    return mk(canonm(d, NEG[b], NEG[c], a), (11 - ZOF(g)) % 11);
}
static const int HA = 0, HB = 1, HC = 2, HD = 0, IA = 0, IB = 2, IC = 1, ID_ = 0;   /* h = (0,1,2,0), h^-1 = (0,2,1,0) */
static E alpha10(E g) {
    uint32_t m = MOF(g); int a = AB(m,24), b = AB(m,16), c = AB(m,8), d = AB(m,0);
    int fa = MUL[MUL[a][a]][a], fb = MUL[MUL[b][b]][b], fc = MUL[MUL[c][c]][c], fd = MUL[MUL[d][d]][d];
    /* h * F(M) * h^-1 with h = [[0,1],[2,0]], h^-1 = [[0,2],[1,0]] */
    int ta = ADDT[MUL[HA][fa]][MUL[HB][fc]], tb = ADDT[MUL[HA][fb]][MUL[HB][fd]];
    int tc = ADDT[MUL[HC][fa]][MUL[HD][fc]], td = ADDT[MUL[HC][fb]][MUL[HD][fd]];
    int a2 = ADDT[MUL[ta][IA]][MUL[tb][IC]], b2 = ADDT[MUL[ta][IB]][MUL[tb][ID_]];
    int c2 = ADDT[MUL[tc][IA]][MUL[td][IC]], d2 = ADDT[MUL[tc][IB]][MUL[td][ID_]];
    return mk(canonm(a2, b2, c2, d2), (2 * ZOF(g)) % 11);
}
static E alpha5(E g) {
    uint32_t m = MOF(g); int a = AB(m,24), b = AB(m,16), c = AB(m,8), d = AB(m,0);
    int fa = MUL[MUL[a][a]][a], fb = MUL[MUL[b][b]][b], fc = MUL[MUL[c][c]][c], fd = MUL[MUL[d][d]][d];
    return mk(canonm(fa, fb, fc, fd), (3 * ZOF(g)) % 11);
}
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static E rand_g(void) {
    for (;;) {
        int a = rnd64() % 243, b = rnd64() % 243, c = rnd64() % 243;
        if (!a) continue;
        int bc = MUL[b][c];
        int d = MUL[ADDT[1][bc]][INVT[a]];           /* ad - bc = 1 */
        int z = 1 + rnd64() % 10;
        return mk(canonm(a, b, c, d), z);
    }
}
#define MAXK 2
#define MAXLEN 9
typedef struct { uint64_t k1, k2, letters; uint8_t len; } REC;
static REC *recs; static size_t nrec = 0, caprec = 0;
static E L[MAXK][11]; static int NL = 11, MAXL, NORB;
static int cur_letters[MAXLEN];
static void push_rec(E v0, E v1, int depth) {
    if (nrec == caprec) { caprec = caprec ? caprec * 2 : (1 << 20); recs = realloc(recs, caprec * sizeof(REC)); if (!recs) { fprintf(stderr, "oom\n"); exit(2); } }
    uint64_t lw = 0; for (int i = 0; i < depth; i++) lw |= (uint64_t)cur_letters[i] << (4 * i);
    recs[nrec].k1 = v0; recs[nrec].k2 = v1; recs[nrec].letters = lw; recs[nrec].len = (uint8_t)depth; nrec++;
}
static void dfs(E v0, E v1, int side, int last, int depth, E *alphaG) {
    (void)alphaG;
    if (depth > 0 && side == 1 && (depth % 2 == 1)) push_rec(v0, v1, depth);
    if (depth == MAXL) return;
    for (int l = 0; l < NL; l++) {
        if (l == last) continue;
        cur_letters[depth] = l;
        if (side == 0) dfs(gmul(L[0][l], v0), gmul(L[1][l], v1), 1, l, depth + 1, alphaG);
        else dfs(gmul(ginv(L[0][l]), v0), gmul(ginv(L[1][l]), v1), 0, l, depth + 1, alphaG);
    }
}
static int cmp(const void *a, const void *b) {
    const REC *x = a, *y = b;
    if (x->k1 != y->k1) return x->k1 < y->k1 ? -1 : 1;
    if (x->k2 != y->k2) return x->k2 < y->k2 ? -1 : 1;
    if (x->len != y->len) return x->len < y->len ? -1 : 1;
    return 0;
}
static void show(uint64_t lw, int len) {
    static const char *nm[11] = {"e","o0","o1","o2","o3","o4","o5","o6","o7","o8","o9"};
    for (int i = 0; i < len; i++) { int l = (lw >> (4 * i)) & 15; printf("%s ", nm[l]); }
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: ident7 k10|k5 MAXL SEED\n"); return 2; }
    int k5 = strcmp(argv[1], "k5") == 0; MAXL = atoi(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (MAXL > MAXLEN) { fprintf(stderr, "MAXL too large\n"); return 2; }
    build_field();
    E ident = mk(canonm(1, 0, 0, 1), 0);
    /* sanity: alpha is a homomorphism on random elements */
    for (int t = 0; t < 3; t++) {
        E g = rand_g(), h = rand_g();
        E (*al)(E) = k5 ? alpha5 : alpha10;
        if (al(gmul(g, h)) != gmul(al(g), al(h))) { fprintf(stderr, "not a homomorphism\n"); return 3; }
    }
    for (int s = 0; s < MAXK; s++) {
        E x = rand_g();
        L[s][0] = ident;
        if (!k5) {
            E y = x; for (int i = 0; i < 10; i++) { L[s][1 + i] = y; y = alpha10(y); }
            if (y != x) { fprintf(stderr, "alpha^10 != 1\n"); return 3; }
        } else {
            E y = x, w = rand_g(); E u = w;
            for (int i = 0; i < 5; i++) { L[s][1 + i] = y; y = alpha5(y); }
            for (int i = 0; i < 5; i++) { L[s][6 + i] = u; u = alpha5(u); }
            if (y != x) { fprintf(stderr, "alpha5^5 != 1\n"); return 3; }
        }
    }
    dfs(ident, ident, 0, -1, 0, NULL);
    size_t tot = nrec; qsort(recs, tot, sizeof(REC), cmp);
    size_t dup = 0; long long dupL[MAXLEN + 1] = {0}, walksL[MAXLEN + 1] = {0};
    for (size_t i = 0; i < tot; i++) walksL[recs[i].len]++;
    size_t shown = 0;
    for (size_t i = 0; i < tot; ) {
        size_t j = i + 1;
        while (j < tot && recs[j].k1 == recs[i].k1 && recs[j].k2 == recs[i].k2) j++;
        if (j - i > 1) {
            for (size_t t = i + 1; t < j; t++) { dup++; dupL[recs[t].len]++; }
            if (shown < 12) { shown++; printf("  identical value:"); for (size_t t = i; t < j; t++) { printf(" [len %d: ", recs[t].len); show(recs[t].letters, recs[t].len); printf("]"); } printf("\n"); }
        }
        i = j;
    }
    printf("mode %s K=2 maxlen=%d seed=%s walks:", argv[1], MAXL, argv[3]);
    for (int l = 1; l <= MAXL; l += 2) printf(" len%d=%lld", l, walksL[l]);
    printf("\nduplicated walks (formal identities, all generators): %zu", dup);
    for (int l = 1; l <= MAXL; l += 2) printf(" len%d=%lld", l, dupL[l]);
    printf("\n");
    return 0;
}
