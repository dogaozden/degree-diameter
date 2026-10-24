/* haarcheck_pq: low-memory exact diameter check of Haar graphs H(G,S) for G = SL(2,q) x Z_n and PSL(2,q) x Z_n,
 * q = p^e (prime powers; e = 1 works too).  Companion to haar_sym for the prime-power families, which the prime
 * checkers (tools/haarcheck_psl, tools/hcsl) do not cover.
 *
 * Usage: haarcheck_pq SOLUTION.txt
 *   Solution file, as haar_sym writes it: header "d D sl|psl q [poly f] n NCYC N NTOT", then d lines
 *   "<i> mat(a,b,c,d) z=Z".  Field elements are integers sum c_i p^i, GF(p)[x]/(f), f monic of degree e (from "poly").
 *
 * Method: vertices (g,A), (g,B), g in G = (SL or PSL) x Z_n; edges (g,A) ~ (s g,B) for s in S.  Right multiplication by G
 *   is an automorphism, transitive on each side, so diam = max(eccA, eccB) where eccA, eccB are the eccentricities of
 *   (e,A) and (e,B).  Each one is a BFS by levels over bitsets: visited bitsets for both sides, two frontier bitsets,
 *   i.e. 4 |G| bits of memory.  Group elements are ranked and unranked in closed form (no table of size |G|):
 *   a matrix with a != 0 is (a, b, c) with d = (1+bc)/a; with a = 0 it is (b, d) with c = -1/b.  For PSL (q odd) the
 *   representative of +-X is the one whose leading entry (a, or b if a = 0) lies in T = {x : x < -x}.
 *
 * Output: a summary, then the last line "VALID d=.. D=.. vertices=.. eccA=.. eccB=.." or "INVALID ... reason=..".
 * Exit status 0 iff VALID.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

#define MAXQ 4096
#define MAXD 64

static int q, p, e, n, psl_odd, nk;
static int dig[MAXQ][16];
static uint16_t *MUL, *ADD;
static int NEG[MAXQ], INV[MAXQ], ISPOS[MAXQ], KIDX[MAXQ], Kl[MAXQ];
static int ND, DH;
static int GM[2][MAXD][4], GZ[2][MAXD];   /* side 0: s_t (A -> B), side 1: s_t^-1 (B -> A) */
static uint64_t NG, NV, W;                /* NG = |G| (vertices per side), NV = 2|G|, W = words per bitset */
static uint64_t *VIS[2], *CUR, *NXT;

static void fail(const char *why) { printf("INVALID reason=%s\n", why); exit(1); }
static inline int MLT(int a, int b) { return MUL[(size_t)a * q + b]; }
static inline int ADL(int a, int b) { return ADD[(size_t)a * q + b]; }

static void build_field(const char *poly) {
    int f[17] = {0};
    if (e == 1) f[1] = 1;
    else {
        if (!poly) fail("extension field needs poly");
        char buf[512]; strncpy(buf, poly, sizeof buf - 1); buf[sizeof buf - 1] = 0;
        char *term = strtok(buf, "+");
        while (term) {
            int coef = 1, ex = 0; char *s = term;
            if (isdigit((unsigned char)*s)) { coef = 0; while (isdigit((unsigned char)*s)) coef = coef * 10 + (*s++ - '0'); }
            if (*s == 'x') { s++; ex = 1; if (*s == '^') { s++; ex = 0; while (isdigit((unsigned char)*s)) ex = ex * 10 + (*s++ - '0'); } }
            else if (*s) fail("bad poly");
            if (ex > e) fail("poly degree > e");
            f[ex] = (f[ex] + coef) % p;
            term = strtok(NULL, "+");
        }
        if (f[e] != 1) fail("poly not monic of degree e");
    }
    for (int x = 0; x < q; x++) { int y = x; for (int i = 0; i < e; i++) { dig[x][i] = y % p; y /= p; } }
    MUL = malloc(sizeof(uint16_t) * (size_t)q * q); ADD = malloc(sizeof(uint16_t) * (size_t)q * q);
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int s = 0, pw = 1;
        for (int i = 0; i < e; i++) { s += ((dig[a][i] + dig[b][i]) % p) * pw; pw *= p; }
        ADD[(size_t)a * q + b] = (uint16_t)s;
        int pr[40] = {0};
        for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) pr[i + j] = (pr[i + j] + dig[a][i] * dig[b][j]) % p;
        for (int i = 2 * e - 2; i >= e; i--) {
            int t = pr[i]; if (!t) continue;
            for (int j = 0; j <= e; j++) pr[i - e + j] = ((pr[i - e + j] - t * f[j]) % p + p) % p;
        }
        s = 0; pw = 1;
        for (int i = 0; i < e; i++) { s += pr[i] * pw; pw *= p; }
        MUL[(size_t)a * q + b] = (uint16_t)s;
    }
    for (int a = 0; a < q; a++) {
        int found = 0;
        for (int b = 0; b < q; b++) if (ADD[(size_t)a * q + b] == 0) { NEG[a] = b; found = 1; break; }
        if (!found) fail("no additive inverse (table error)");
        INV[a] = 0;
    }
    for (int a = 1; a < q; a++) {       /* commutative ring with every nonzero unit = field */
        int found = 0;
        for (int b = 1; b < q; b++) if (MUL[(size_t)a * q + b] == 1) { INV[a] = b; found = 1; break; }
        if (!found) fail("poly is not irreducible (not a field)");
    }
    for (int x = 1; x < q; x++) ISPOS[x] = (x < NEG[x]);
    nk = 0;
    for (int x = 0; x < q; x++) KIDX[x] = -1;
    for (int x = 1; x < q; x++) if (!psl_odd || ISPOS[x]) { Kl[nk] = x; KIDX[x] = nk; nk++; }
}

/* canonical representative of +-X (PSL, q odd); identity on SL */
static inline void canon(int *a, int *b, int *c, int *d) {
    if (!psl_odd) return;
    int lead = *a ? *a : *b;
    if (!ISPOS[lead]) { *a = NEG[*a]; *b = NEG[*b]; *c = NEG[*c]; *d = NEG[*d]; }
}
static inline uint64_t rank_canon(int a, int b, int c, int d) {
    uint64_t Q2 = (uint64_t)q * q;
    if (a) return (uint64_t)KIDX[a] * Q2 + (uint64_t)b * q + (uint64_t)c;
    return (uint64_t)nk * Q2 + (uint64_t)KIDX[b] * q + (uint64_t)d;
}
static inline void unrank(uint64_t r, int *a, int *b, int *c, int *d) {
    uint64_t Q2 = (uint64_t)q * q;
    if (r < (uint64_t)nk * Q2) {
        uint64_t t = r / Q2, rem = r % Q2;
        *b = (int)(rem / q); *c = (int)(rem % q); *a = Kl[t];
        *d = MLT(ADL(1, MLT(*b, *c)), INV[*a]);
    } else {
        uint64_t r2 = r - (uint64_t)nk * Q2, t = r2 / q;
        *d = (int)(r2 % q); *b = Kl[t]; *a = 0; *c = NEG[INV[*b]];
    }
}

static void read_gens(FILE *fp) {
    char line[8192];
    int got = 0;
    while (got < ND && fgets(line, sizeof line, fp)) {
        char *m = strstr(line, "mat("), *z = strstr(line, "z=");
        if (!m || !z) { if (strspn(line, " \t\r\n") == strlen(line)) continue; fail("bad generator line"); }
        int a, b, c, dd, zz;
        if (sscanf(m, "mat(%d,%d,%d,%d)", &a, &b, &c, &dd) != 4) fail("bad mat(...)");
        if (sscanf(z, "z=%d", &zz) != 1) fail("bad z=");
        if (a < 0 || a >= q || b < 0 || b >= q || c < 0 || c >= q || dd < 0 || dd >= q) fail("matrix entry out of range");
        if (ADL(MLT(a, dd), NEG[MLT(b, c)]) != 1) fail("matrix not in SL (det != 1)");
        if (zz < 0 || zz >= n) fail("z out of range");
        GM[0][got][0] = a; GM[0][got][1] = b; GM[0][got][2] = c; GM[0][got][3] = dd; GZ[0][got] = zz;
        GM[1][got][0] = dd; GM[1][got][1] = NEG[b]; GM[1][got][2] = NEG[c]; GM[1][got][3] = a;   /* inverse */
        GZ[1][got] = (n - zz) % n;
        got++;
    }
    if (got != ND) fail("missing generator lines");
}

/* one BFS by levels from (src, side0); ecc = last level with new vertices, reached = vertices reached (both sides) */
static void bfs(int side0, uint64_t src, int *ecc, uint64_t *reached) {
    memset(VIS[0], 0, W * 8); memset(VIS[1], 0, W * 8); memset(CUR, 0, W * 8);
    VIS[side0][src >> 6] |= 1ULL << (src & 63);
    CUR[src >> 6] |= 1ULL << (src & 63);
    int side = side0, level = 0;
    uint64_t total = 1;
    for (;;) {
        int ns = side ^ 1;
        memset(NXT, 0, W * 8);
        uint64_t newc = 0;
        for (uint64_t w = 0; w < W; w++) {
            uint64_t x = CUR[w];
            while (x) {
                uint64_t idx = (w << 6) + (uint64_t)__builtin_ctzll(x);
                x &= x - 1;
                uint64_t r = idx / (uint64_t)n;
                int zc = (int)(idx - r * (uint64_t)n);
                int a, b, c, dd;
                unrank(r, &a, &b, &c, &dd);
                for (int t = 0; t < ND; t++) {
                    const int *M = GM[side][t];
                    int A = ADL(MLT(M[0], a), MLT(M[1], c));
                    int B = ADL(MLT(M[0], b), MLT(M[1], dd));
                    int C = ADL(MLT(M[2], a), MLT(M[3], c));
                    int Dd = ADL(MLT(M[2], b), MLT(M[3], dd));
                    canon(&A, &B, &C, &Dd);
                    uint64_t rr = rank_canon(A, B, C, Dd);
                    int z2 = zc + GZ[side][t]; if (z2 >= n) z2 -= n;
                    uint64_t v = rr * (uint64_t)n + (uint64_t)z2;
                    uint64_t m = 1ULL << (v & 63);
                    if (!(VIS[ns][v >> 6] & m)) { VIS[ns][v >> 6] |= m; NXT[v >> 6] |= m; newc++; }
                }
            }
        }
        if (!newc) break;
        total += newc; level++;
        uint64_t *tmp = CUR; CUR = NXT; NXT = tmp;
        side = ns;
    }
    *ecc = level; *reached = total;
}

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: %s SOLUTION.txt\n", argv[0]); return 2; }
    FILE *fp = fopen(argv[1], "r");
    if (!fp) { printf("INVALID reason=cannot open %s\n", argv[1]); return 1; }
    char line[8192], polybuf[512] = "";
    if (!fgets(line, sizeof line, fp)) fail("empty file");
    char *tok[64]; int nt = 0;
    for (char *s = strtok(line, " \t\r\n"); s && nt < 64; s = strtok(NULL, " \t\r\n")) tok[nt++] = s;
    if (nt < 7) fail("short header");
    ND = atoi(tok[0]); DH = atoi(tok[1]);
    int i = 2, psl;
    if (!strcmp(tok[i], "sl")) psl = 0;
    else if (!strcmp(tok[i], "psl")) psl = 1;
    else fail("group must be sl or psl");
    i++;
    int qq = atoi(tok[i++]);
    int haspoly = 0;
    if (i < nt && !strcmp(tok[i], "poly")) {
        if (i + 1 >= nt) fail("poly without value");
        strncpy(polybuf, tok[i + 1], sizeof polybuf - 1); haspoly = 1; i += 2;
    }
    if (i + 1 >= nt || strcmp(tok[i], "n")) fail("expected n");
    n = atoi(tok[i + 1]); i += 2;
    unsigned long long Ndecl = 0; int hasN = 0;
    if (i + 1 < nt && !strcmp(tok[i], "N")) { Ndecl = strtoull(tok[i + 1], NULL, 10); hasN = 1; }
    if (ND < 1 || ND > MAXD) fail("bad d");
    if (qq < 2 || qq > MAXQ) fail("q out of range");
    if (n < 1) fail("bad n");
    q = qq;
    p = 0; for (int t = 2; t <= q; t++) if (q % t == 0) { p = t; break; }
    e = 0; { int x = q; while (x % p == 0) { x /= p; e++; } if (x != 1) fail("q is not a prime power"); }
    psl_odd = psl && (q % 2 == 1);
    build_field(haspoly ? polybuf : NULL);
    NG = (uint64_t)nk * ((uint64_t)q * q + q) * (uint64_t)n;     /* |SL| = q^3 - q, |PSL| = |SL|/2 for q odd */
    NV = 2 * NG; W = (NG + 63) / 64;
    if (hasN && Ndecl != NG) fail("declared N does not match |G|");
    read_gens(fp);
    fclose(fp);

    /* d distinct canonical generators (else the graph has repeated edges) */
    uint64_t key[MAXD];
    for (int t = 0; t < ND; t++) {
        int a = GM[0][t][0], b = GM[0][t][1], c = GM[0][t][2], dd = GM[0][t][3];
        canon(&a, &b, &c, &dd);
        key[t] = rank_canon(a, b, c, dd) * (uint64_t)n + (uint64_t)GZ[0][t];
    }
    for (int t = 0; t < ND; t++) for (int u = 0; u < t; u++) if (key[t] == key[u]) {
        printf("INVALID d=%d D=%d vertices=%llu reason=generators not distinct\n", ND, DH, (unsigned long long)NV);
        return 1;
    }

    printf("group=%s q=%d p=%d e=%d n=%d |G|=%llu vertices=%llu d=%d D=%d\n", psl ? "psl" : "sl", q, p, e, n,
           (unsigned long long)NG, (unsigned long long)NV, ND, DH);
    VIS[0] = calloc(W, 8); VIS[1] = calloc(W, 8); CUR = calloc(W, 8); NXT = calloc(W, 8);
    if (!VIS[0] || !VIS[1] || !CUR || !NXT) fail("out of memory");

    int a = 1, b = 0, c = 0, dd = 1;
    canon(&a, &b, &c, &dd);
    uint64_t src = rank_canon(a, b, c, dd) * (uint64_t)n;     /* (e, A) and (e, B) */
    int eccA, eccB; uint64_t reA, reB;
    bfs(0, src, &eccA, &reA);
    printf("from (e,A): ecc=%d unreached=%llu\n", eccA, (unsigned long long)(NV - reA));
    fflush(stdout);
    bfs(1, src, &eccB, &reB);
    printf("from (e,B): ecc=%d unreached=%llu\n", eccB, (unsigned long long)(NV - reB));

    int unreached = (reA != NV) || (reB != NV);
    if (!unreached && eccA <= DH && eccB <= DH) {
        printf("VALID d=%d D=%d vertices=%llu eccA=%d eccB=%d\n", ND, DH, (unsigned long long)NV, eccA, eccB);
        return 0;
    }
    printf("INVALID d=%d D=%d vertices=%llu eccA=%d eccB=%d reason=%s\n", ND, DH, (unsigned long long)NV, eccA, eccB,
           unreached ? "disconnected" : "diameter");
    return 1;
}
