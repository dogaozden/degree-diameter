/* haarcheck_pslq: independent, low-memory diameter check of a Haar graph H(G,S), G = PSL(2,q) x Z_n, q = p^k odd.
 * Written for this job from the definitions (same method as haarcheck_psl.c, which handles prime p only).
 * Reads a haar_sym solution file. Header: "d D psl q [poly f] n NCYC N NTOT", where f = x^k+... is the monic
 * irreducible of GF(q) = GF(p)[x]/(f) (omitted for prime q). Field element c = sum c_i p^i, c_i the coefficient of x^i.
 * Then d lines "<index> mat(a,b,c,d) z=Z" (either sign of the matrix may be given).
 * Vertices (g,A),(g,B); edges (g,A) ~ (s g, B). Right multiplication by G is transitive on each side, so BFS from
 * (e,A) and (e,B) gives the exact diameter.
 * Own element indexing: a matrix and its negative are one element. Normal form: c != 0 with c in H, or c = 0 with
 * a in H, where H = {x != 0 : x < -x} (one of each pair x, -x). c != 0: index ((rank c)*q + a)*q + d, b = (ad-1)/c.
 * c = 0: index H2*q*q + (rank a)*q + b, d = 1/a. Index = matrix index * n + z.
 * Memory: 4 bitsets of N bits. Usage: haarcheck_pslq SOL.txt   Build: cc -O3 -o haarcheck_pslq haarcheck_pslq.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int p, kf, q, H2, n;          /* q = p^kf, H2 = (q-1)/2 */
static long long N;
static int *ADD, *MUL, *NEG, *INV, *HR, *HE;

static int fdig(int x, int *d) { for (int i = 0; i < kf; i++) { d[i] = x % p; x /= p; } return 0; }
static int fenc(const int *d) { int s = 0; for (int i = kf - 1; i >= 0; i--) s = s * p + d[i]; return s; }
static int fadd(int a, int b) { return ADD[a * q + b]; }
static int fmul(int a, int b) { return MUL[a * q + b]; }

static void build_field(const int *poly) {       /* poly[0..kf], monic, poly[kf] = 1 */
    ADD = malloc(sizeof(int) * q * q); MUL = malloc(sizeof(int) * q * q);
    NEG = malloc(sizeof(int) * q); INV = malloc(sizeof(int) * q);
    HR = malloc(sizeof(int) * q); HE = malloc(sizeof(int) * (H2 + 1));
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int da[16], db[16], s[16], pr[32] = {0};
        fdig(a, da); fdig(b, db);
        for (int i = 0; i < kf; i++) s[i] = (da[i] + db[i]) % p;
        ADD[a * q + b] = fenc(s);
        for (int i = 0; i < kf; i++) for (int j = 0; j < kf; j++) pr[i + j] = (pr[i + j] + da[i] * db[j]) % p;
        for (int i = 2 * kf - 2; i >= kf; i--) { int t = pr[i]; if (!t) continue;
            for (int j = 0; j <= kf; j++) pr[i - kf + j] = ((pr[i - kf + j] - t * poly[j]) % p + p) % p; }
        for (int i = 0; i < kf; i++) s[i] = pr[i];
        MUL[a * q + b] = fenc(s);
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        if (ADD[a * q + b] == 0) NEG[a] = b;
        if (MUL[a * q + b] == 1) INV[a] = b;
    }
    for (int a = 1; a < q; a++) if (fmul(a, INV[a]) != 1) { fprintf(stderr, "not a field (poly reducible?)\n"); exit(2); }
    int r = 0;
    for (int x = 1; x < q; x++) if (x < NEG[x]) { HR[x] = r; HE[r] = x; r++; } else HR[x] = -1;
    if (r != H2) { fprintf(stderr, "H size %d != %d\n", r, H2); exit(2); }
}
static int inH(int x) { return x != 0 && x < NEG[x]; }
static long long enc(int a, int b, int c, int d, int z) {
    if (c ? !inH(c) : !inH(a)) { a = NEG[a]; b = NEG[b]; c = NEG[c]; d = NEG[d]; }
    long long k;
    if (c) k = ((long long)HR[c] * q + a) * q + d;
    else k = (long long)H2 * q * q + (long long)HR[a] * q + b;
    return k * n + z;
}
static void dec(long long g, int *a, int *b, int *c, int *d, int *z) {
    *z = (int)(g % n); long long k = g / n;
    if (k < (long long)H2 * q * q) {
        int hr = (int)(k / ((long long)q * q)); *c = HE[hr];
        *a = (int)(k / q % q); *d = (int)(k % q);
        *b = fmul(fadd(fmul(*a, *d), NEG[1]), INV[*c]);
    } else {
        k -= (long long)H2 * q * q; int hr = (int)(k / q); *b = (int)(k % q);
        *a = HE[hr]; *d = INV[*a]; *c = 0;
    }
}
typedef struct { int a, b, c, d, z; } el;
static int parse_poly(const char *s, int *poly) {   /* "x^4+x+2" */
    memset(poly, 0, sizeof(int) * 16);
    char buf[256]; strncpy(buf, s, sizeof buf - 1); buf[sizeof buf - 1] = 0;
    for (char *t = strtok(buf, "+"); t; t = strtok(NULL, "+")) {
        int coef = 1, deg = 0; char *x = strchr(t, 'x');
        if (!x) { coef = atoi(t); deg = 0; }
        else {
            if (x != t) coef = atoi(t);
            if (x[1] == '^') deg = atoi(x + 2); else deg = 1;
        }
        poly[deg] = coef;
    }
    return 0;
}
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_pslq SOL.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    int dg, D; char tok[12][256]; int nt = 0;
    {   /* tokens: d D psl q [poly f] n NCYC N NTOT */
        char *t = strtok(line, " \n");
        while (t && nt < 12) { strcpy(tok[nt++], t); t = strtok(NULL, " \n"); }
    }
    if (nt < 4 || strcmp(tok[2], "psl")) { fprintf(stderr, "only psl headers\n"); return 2; }
    dg = atoi(tok[0]); D = atoi(tok[1]); q = atoi(tok[3]);
    int ti = 4; int poly[16] = {0};
    if (!strcmp(tok[ti], "poly")) { parse_poly(tok[ti + 1], poly); ti += 2; }
    else { poly[1] = 1; }
    /* kf = log_p q */
    p = 0; for (int t = 2; t <= q; t++) if (q % t == 0) { p = t; break; }
    kf = 0; { int x = q; while (x % p == 0) { x /= p; kf++; } if (x != 1) { fprintf(stderr, "q not a prime power\n"); return 2; } }
    if (p < 3 || p % 2 == 0) { fprintf(stderr, "q must be odd\n"); return 2; }
    if (kf == 1) { memset(poly, 0, sizeof poly); poly[1] = 1; }
    if (strcmp(tok[ti], "n") || strcmp(tok[ti + 2], "N")) { fprintf(stderr, "bad header: %s\n", tok[0]); return 2; }
    n = atoi(tok[ti + 1]); long long NN = atoll(tok[ti + 3]);
    q = 1; for (int i = 0; i < kf; i++) q *= p;
    H2 = (q - 1) / 2;
    N = (long long)q * ((long long)q * q - 1) / 2 * n;
    if (N != NN) { fprintf(stderr, "header N %lld != |PSL(2,%d)| n = %lld\n", NN, q, N); return 2; }
    /* the poly for kf > 1 must be monic of degree kf */
    if (kf > 1 && poly[kf] != 1) { fprintf(stderr, "poly not monic of degree %d\n", kf); return 2; }
    build_field(poly);
    el S[64], SI[64]; int k = 0;
    while (fgets(line, sizeof line, f) && k < 64) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z=");
        if (!m || !zz) continue;
        int a, b, c, d, z;
        if (sscanf(m, "mat(%d,%d,%d,%d)", &a, &b, &c, &d) != 4 || sscanf(zz, "z=%d", &z) != 1) return 2;
        if (a < 0 || a >= q || b < 0 || b >= q || c < 0 || c >= q || d < 0 || d >= q || z < 0 || z >= n ||
            fadd(fmul(a, d), NEG[fmul(b, c)]) != 1) { fprintf(stderr, "bad element: %s", line); return 2; }
        S[k] = (el){a, b, c, d, z}; SI[k] = (el){d, NEG[b], NEG[c], a, (n - z) % n}; k++;
    }
    if (k != dg) { fprintf(stderr, "read %d elements, expected %d\n", k, dg); return 2; }
    for (int i = 0; i < k; i++) for (int j = 0; j < i; j++)
        if (enc(S[i].a, S[i].b, S[i].c, S[i].d, S[i].z) == enc(S[j].a, S[j].b, S[j].c, S[j].d, S[j].z)) {
            fprintf(stderr, "repeated generator %d %d\n", i, j); return 2; }
    /* self-test: bijection of the index onto [0,N), det 1, and the normal form is stable under -1 */
    for (long long g = 0; g < N; g += N / 4000 + 1) { int a, b, c, d, z; dec(g, &a, &b, &c, &d, &z);
        if (fadd(fmul(a, d), NEG[fmul(b, c)]) != 1 || enc(a, b, c, d, z) != g ||
            enc(NEG[a], NEG[b], NEG[c], NEG[d], z) != g) { fprintf(stderr, "index self-test failed at %lld\n", g); return 2; } }
    long long W = (N + 63) / 64;
    uint64_t *vis[2], *cur[2], *nxt[2];
    for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); cur[s] = calloc(W, 8); nxt[s] = calloc(W, 8);
        if (!vis[s] || !cur[s] || !nxt[s]) { fprintf(stderr, "out of memory\n"); return 2; } }
    int bad = 0;
    for (int start = 0; start < 2; start++) {
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(cur[s], 0, W * 8); }
        long long e = enc(1, 0, 0, 1, 0); vis[start][e >> 6] |= 1ULL << (e & 63); cur[start][e >> 6] |= 1ULL << (e & 63);
        long long reached[2] = {0, 0}; reached[start] = 1; int side = start, ecc = 0;
        for (int step = 1; step <= D; step++) {
            int ns = side ^ 1; long long add = 0; memset(nxt[ns], 0, W * 8);
            el *T = side == 0 ? S : SI;          /* (g,A) -> (s g, B);  (h,B) -> (s^-1 h, A) */
            for (long long w = 0; w < W; w++) { uint64_t bits = cur[side][w];
                while (bits) { int bt = __builtin_ctzll(bits); bits &= bits - 1; long long g = w * 64 + bt;
                    int a, b, c, d, z; dec(g, &a, &b, &c, &d, &z);
                    for (int i = 0; i < k; i++) { const el *s = &T[i];
                        long long hh = enc(fadd(fmul(s->a, a), fmul(s->b, c)), fadd(fmul(s->a, b), fmul(s->b, d)),
                                           fadd(fmul(s->c, a), fmul(s->d, c)), fadd(fmul(s->c, b), fmul(s->d, d)),
                                           (s->z + z) % n);
                        uint64_t m1 = 1ULL << (hh & 63);
                        if (!(vis[ns][hh >> 6] & m1)) { vis[ns][hh >> 6] |= m1; nxt[ns][hh >> 6] |= m1; add++; } } } }
            memset(cur[side], 0, W * 8); uint64_t *t = cur[ns]; cur[ns] = nxt[ns]; nxt[ns] = t;
            reached[ns] += add; if (add) ecc = step; side = ns;
        }
        printf("from (e,%c): reached A %lld/%lld, B %lld/%lld within %d, ecc %d\n", start ? 'B' : 'A', reached[0], N, reached[1], N, D, ecc);
        if (reached[0] != N || reached[1] != N) bad = 1;
    }
    printf("%s d=%d D=%d group=psl %d x Z_%d N=%lld vertices=%lld (distinct generators, %d-regular simple)\n",
           bad ? "INVALID" : "VALID", dg, D, q, n, N, 2 * N, dg);
    return bad;
}
