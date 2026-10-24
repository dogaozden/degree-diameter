/* pqcheck: independent low-memory diameter check of a Haar graph H(G,S), G = SL(2,q) x Z_n or PSL(2,q) x Z_n,
 * q = p^e any prime power (e = 1 allowed).  Written for the cell-11-10 session from the definitions only (it shares no
 * code with haar_sym, build_haar2.py, haarcheck_sl/psl or the squad's checkers).
 *
 * Input: a haar_sym solution file.  Header "d D sl|psl q [poly <f>] n NCYC N NTOT", then d lines
 * "<idx> mat(a,b,c,d) z=Z"; only the mat/z parts are used.  Field: GF(p)[x]/(f), f the header polynomial (required
 * when e > 1, monic of degree e, irreducibility is checked); an entry "a" is the integer sum a_i p^i <-> sum a_i x^i.
 * Graph: vertices (g,A), (g,B); edges (g,A) ~ (s g, B) for s in S.  Right multiplication by G is transitive on each
 * side, so the diameter is <= D iff BFS from (e,A) and from (e,B) reach every vertex within D.  Prints the eccentricities.
 * Elements: a matrix [[a,b],[c,d]] of determinant 1 gets the SL index (c != 0: ((c-1) q + a) q + d, b implied;
 * c = 0: q^2 (q-1) + (a-1) q + b, d implied); for PSL a matrix and its negative are one element, numbered through a
 * table SL index -> PSL index (the representative is the one with the smaller SL index).  Group index = idx * n + z.
 * Memory: the SL->PSL table (4 |SL| bytes, PSL only) and 4 bitsets of N bits.
 * Build: cc -O3 -o pqcheck pqcheck.c      Usage: pqcheck SOL.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>

static int q, p, e, n, isp;           /* isp: PSL */
static int fpoly[17];                 /* monic f, low -> high */
static uint16_t *ADD, *MUL, *NEG, *INV;
static long long NSL, NG;             /* |SL(2,q)|, |G| */
static int32_t *SL2P;                 /* SL index -> PSL index (or -1 if not the representative) */
static int64_t *P2SL;                 /* PSL index -> SL index of the representative */

static int pw(int b, int k) { int r = 1; while (k--) r *= b; return r; }
static int fmul_slow(int a, int b) {  /* polynomial product mod f over GF(p) */
    int da[17] = {0}, db[17] = {0}, pr[34] = {0};
    for (int i = 0; i < e; i++) { da[i] = a % p; a /= p; db[i] = b % p; b /= p; }
    for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) pr[i + j] = (pr[i + j] + da[i] * db[j]) % p;
    for (int i = 2 * e - 2; i >= e; i--) if (pr[i]) { int t = pr[i]; for (int j = 0; j <= e; j++) pr[i - e + j] = ((pr[i - e + j] - t * fpoly[j]) % p + p) % p; }
    int s = 0; for (int i = e - 1; i >= 0; i--) s = s * p + pr[i];
    return s;
}
static int fadd_slow(int a, int b) { int s = 0, m = 1; for (int i = 0; i < e; i++) { s += ((a % p + b % p) % p) * m; a /= p; b /= p; m *= p; } return s; }
#define FA(x, y) ADD[(x) * q + (y)]
#define FM(x, y) MUL[(x) * q + (y)]
static int parse_poly(const char *s) {   /* "x^5+2x+1" -> fpoly */
    memset(fpoly, 0, sizeof fpoly); int deg = -1;
    const char *c = s;
    while (*c && !isspace((unsigned char)*c)) {
        int coef = 1, ex = 0, have = 0;
        if (isdigit((unsigned char)*c)) { coef = 0; while (isdigit((unsigned char)*c)) coef = coef * 10 + (*c++ - '0'); have = 1; }
        if (*c == 'x') { c++; ex = 1; if (*c == '^') { c++; ex = 0; while (isdigit((unsigned char)*c)) ex = ex * 10 + (*c++ - '0'); } }
        else if (!have) return 0;
        if (ex > 16) return 0;
        fpoly[ex] = (fpoly[ex] + coef) % p; if (ex > deg) deg = ex;
        if (*c == '+') c++; else if (*c && !isspace((unsigned char)*c)) return 0;
    }
    return deg;
}
static long long slidx(int a, int b, int c, int d) {
    if (c) return ((long long)(c - 1) * q + a) * q + d;
    return (long long)q * q * (q - 1) + (long long)(a - 1) * q + b;
}
static void sldec(long long k, int *a, int *b, int *c, int *d) {
    long long base = (long long)q * q * (q - 1);
    if (k < base) { *c = (int)(k / ((long long)q * q)) + 1; *a = (int)(k / q % q); *d = (int)(k % q);
        int ad1 = FA(FM(*a, *d), NEG[1]); *b = FM(ad1, INV[*c]); }
    else { k -= base; *c = 0; *a = (int)(k / q) + 1; *b = (int)(k % q); *d = INV[*a]; }
}
static inline long long gidx(int a, int b, int c, int d, int z) {
    long long k = slidx(a, b, c, d);
    if (isp) { int32_t t = SL2P[k]; if (t < 0) t = SL2P[slidx(NEG[a], NEG[b], NEG[c], NEG[d])]; k = t; }
    return k * n + z;
}
static inline void gdec(long long g, int *a, int *b, int *c, int *d, int *z) {
    *z = (int)(g % n); long long k = g / n;
    sldec(isp ? P2SL[k] : k, a, b, c, d);
}
typedef struct { int a, b, c, d, z; } el;
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: pqcheck SOL.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    int dg, D; char fam[16], tok[64]; int off = 0;
    if (sscanf(line, "%d %d %15s %d %n", &dg, &D, fam, &q, &off) != 4) { printf("INVALID reason=header\n"); return 1; }
    if (strcmp(fam, "sl") && strcmp(fam, "psl")) { printf("INVALID reason=family %s not sl/psl\n", fam); return 1; }
    isp = !strcmp(fam, "psl");
    p = 0; for (int t = 2; t <= q; t++) if (q % t == 0) { p = t; break; }
    e = 0; { int x = q; while (x % p == 0) { x /= p; e++; } if (x != 1) { printf("INVALID reason=q not a prime power\n"); return 1; } }
    if (q > 4096) { printf("INVALID reason=q too large for this checker\n"); return 1; }
    char *rest = line + off; long long NN = 0;
    if (sscanf(rest, "%63s", tok) == 1 && !strcmp(tok, "poly")) {
        char ps[256]; int o2 = 0; sscanf(rest, "poly %255s %n", ps, &o2); rest += o2;
        if (parse_poly(ps) != e || fpoly[e] != 1) { printf("INVALID reason=bad polynomial %s\n", ps); return 1; }
    } else if (e > 1) { printf("INVALID reason=prime power without polynomial\n"); return 1; }
    else { memset(fpoly, 0, sizeof fpoly); fpoly[1] = 1; }
    if (sscanf(rest, "n %d N %lld", &n, &NN) != 2 || n < 1) { printf("INVALID reason=header n/N\n"); return 1; }
    if (isp && p == 2) isp = 0;          /* char 2: PSL = SL */
    /* field tables, checked: f irreducible <=> GF(p)[x]/(f) has no zero divisors */
    ADD = malloc(2 * (size_t)q * q); MUL = malloc(2 * (size_t)q * q); NEG = malloc(2 * q); INV = malloc(2 * q);
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { FA(a, b) = (uint16_t)fadd_slow(a, b); FM(a, b) = (uint16_t)fmul_slow(a, b); }
    for (int a = 0; a < q; a++) { NEG[a] = 0xffff; INV[a] = 0xffff;
        for (int b = 0; b < q; b++) { if (FA(a, b) == 0) NEG[a] = b; if (FM(a, b) == 1) INV[a] = b; } }
    for (int a = 1; a < q; a++) if (INV[a] == 0xffff) { printf("INVALID reason=polynomial not irreducible (no inverse of %d)\n", a); return 1; }
    for (int a = 0; a < q; a += 7) for (int b = 0; b < q; b += 5) for (int c = 0; c < q; c += 3)   /* associativity, distributivity */
        if (FM(FM(a, b), c) != FM(a, FM(b, c)) || FM(a, FA(b, c)) != FA(FM(a, b), FM(a, c))) { printf("INVALID reason=field tables\n"); return 1; }
    NSL = (long long)q * ((long long)q * q - 1);
    NG = (isp ? NSL / 2 : NSL) * n;
    if (NG != NN) { printf("INVALID reason=header N %lld != |Q| n = %lld\n", NN, NG); return 1; }
    if (isp) {
        SL2P = malloc(sizeof(int32_t) * NSL); P2SL = malloc(sizeof(int64_t) * (NSL / 2)); long long cnt = 0;
        for (long long k = 0; k < NSL; k++) SL2P[k] = -1;
        for (long long k = 0; k < NSL; k++) { int a, b, c, d; sldec(k, &a, &b, &c, &d);
            long long k2 = slidx(NEG[a], NEG[b], NEG[c], NEG[d]);
            if (k2 == k) { printf("INVALID reason=-M = M in odd characteristic?\n"); return 1; }
            if (k < k2) { SL2P[k] = (int32_t)cnt; P2SL[cnt] = k; cnt++; } }
        if (cnt * 2 != NSL) { printf("INVALID reason=PSL count\n"); return 1; }
    }
    /* self-test of the indexing on a sample */
    for (long long g = 0; g < NG; g += NG / 5000 + 1) { int a, b, c, d, z; gdec(g, &a, &b, &c, &d, &z);
        if (FA(FM(a, d), NEG[FM(b, c)]) != 1 || gidx(a, b, c, d, z) != g) { printf("INVALID reason=index self-test at %lld\n", g); return 1; } }
    el S[64], SI[64]; int k = 0;
    while (fgets(line, sizeof line, f) && k < 64) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z=");
        if (!m || !zz) continue;
        int a, b, c, d, z;
        if (sscanf(m, "mat(%d,%d,%d,%d)", &a, &b, &c, &d) != 4 || sscanf(zz, "z=%d", &z) != 1) { printf("INVALID reason=parse\n"); return 1; }
        if (a < 0 || a >= q || b < 0 || b >= q || c < 0 || c >= q || d < 0 || d >= q || z < 0 || z >= n) { printf("INVALID reason=entry out of range\n"); return 1; }
        if (FA(FM(a, d), NEG[FM(b, c)]) != 1) { printf("INVALID reason=determinant != 1: %s", line); return 1; }
        S[k] = (el){a, b, c, d, z}; SI[k] = (el){d, NEG[b], NEG[c], a, (n - z) % n}; k++;
    }
    if (k != dg) { printf("INVALID reason=read %d generators, header says %d\n", k, dg); return 1; }
    for (int i = 0; i < k; i++) for (int j = 0; j < i; j++)
        if (gidx(S[i].a, S[i].b, S[i].c, S[i].d, S[i].z) == gidx(S[j].a, S[j].b, S[j].c, S[j].d, S[j].z)) { printf("INVALID reason=repeated generator %d %d\n", j, i); return 1; }
    long long W = (NG + 63) / 64;
    uint64_t *vis[2], *cur[2], *nxt[2];
    for (int s = 0; s < 2; s++) { vis[s] = malloc(W * 8); cur[s] = malloc(W * 8); nxt[s] = malloc(W * 8); }
    int ecc[2] = {0, 0}, ok = 1;
    long long eg = gidx(1, 0, 0, 1, 0);
    for (int st = 0; st < 2; st++) {
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(cur[s], 0, W * 8); }
        vis[st][eg >> 6] |= 1ULL << (eg & 63); cur[st][eg >> 6] |= 1ULL << (eg & 63);
        long long reached[2] = {st == 0, st == 1}; int side = st, lev = 0;
        while (reached[0] + reached[1] < 2 * NG && lev < D + 2) {
            int to = side ^ 1; memset(nxt[to], 0, W * 8); long long add = 0;
            for (long long w = 0; w < W; w++) { uint64_t x = cur[side][w]; while (x) { int bt = __builtin_ctzll(x); x &= x - 1;
                long long g = w * 64 + bt; int a, b, c, d, z; gdec(g, &a, &b, &c, &d, &z);
                for (int i = 0; i < k; i++) { const el *s = side == 0 ? &S[i] : &SI[i];   /* A -> B: s g;  B -> A: s^-1 g */
                    int na = FA(FM(s->a, a), FM(s->b, c)), nb = FA(FM(s->a, b), FM(s->b, d));
                    int nc = FA(FM(s->c, a), FM(s->d, c)), nd = FA(FM(s->c, b), FM(s->d, d));
                    long long h = gidx(na, nb, nc, nd, (s->z + z) % n);
                    uint64_t bit = 1ULL << (h & 63);
                    if (!(vis[to][h >> 6] & bit)) { vis[to][h >> 6] |= bit; nxt[to][h >> 6] |= bit; add++; } } } }
            lev++; reached[to] += add; if (add == 0) break;
            uint64_t *t = cur[to]; cur[to] = nxt[to]; nxt[to] = t; memset(cur[side], 0, W * 8); side = to;
            fprintf(stderr, "  start %c level %d: new %lld, reached A %lld B %lld\n", st ? 'B' : 'A', lev, add, reached[0], reached[1]);
        }
        ecc[st] = lev;
        if (reached[0] != NG || reached[1] != NG || lev > D) ok = 0;
        fprintf(stderr, "from (e,%c): reached A %lld/%lld, B %lld/%lld, eccentricity %d\n", st ? 'B' : 'A', reached[0], NG, reached[1], NG, lev);
    }
    if (ok) printf("VALID d=%d D=%d group=%s %d x Z_%d N=%lld vertices=%lld eccA=%d eccB=%d (pqcheck)\n", dg, D, fam, q, n, NG, 2 * NG, ecc[0], ecc[1]);
    else printf("INVALID d=%d D=%d group=%s %d x Z_%d vertices=%lld eccA=%d eccB=%d (pqcheck)\n", dg, D, fam, q, n, 2 * NG, ecc[0], ecc[1]);
    return ok ? 0 : 1;
}
