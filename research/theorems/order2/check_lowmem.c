/* check_lowmem.c: independent low-memory diameter check of a haar_gen3-format solution file on
 * G = Q x Z_n, Q = SL(2,q) or a direct product of two SL(2,q_i) (q prime powers; PSL = SL in characteristic 2).
 * Written for research/theorems/order2 (ORDER2.md), sharing no code with haar_gen3/haar_sym, build_haar2.py or
 * check_np.py.  Field GF(p^k) = GF(p)[x]/(f) with f read from the "poly ..." part of the spec (as haar_gen3 writes it),
 * field elements written as sum c_i p^i.  An SL(2,q) element (a,b,c,d) is stored as its key
 *   a != 0: ((a-1) q + b) q + c          (d = (1 + b c)/a)
 *   a == 0: (q-1) q^2 + (b-1) q + d      (c = -1/b)
 * which is a bijection SL(2,q) -> [0, q^3 - q).  Products index i1 |Q2| + i2; G indexes qidx * n + z.
 * Haar graph H(G,S): (g,A) ~ (s g, B).  Right multiplication by G is transitive on each side, so the diameter is
 * max(ecc(e,A), ecc(e,B)); both BFS run over all 2N vertices with bitsets (N/8 bytes each), neighbours computed by
 * group multiplication on the fly.  Checks: d distinct generators, every vertex reached, both eccentricities <= D.
 * Build: gcc -O3 -march=native -fopenmp -o check_lowmem check_lowmem.c      Usage: check_lowmem SOL.txt [threads]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef struct { int q, p, k; int poly[16]; int *add, *mul, *neg, *inv; } fld;
typedef struct { fld F; long long order; } slq;

static void parse_poly(const char *s, int p, int *coef, int k) {   /* "x^4+x+1" -> coefficients low..high */
    memset(coef, 0, sizeof(int) * 16);
    const char *t = s;
    while (*t) {
        int c = 1, e = 0, have_c = 0;
        if (isdigit((unsigned char)*t)) { c = 0; while (isdigit((unsigned char)*t)) c = c * 10 + (*t++ - '0'); have_c = 1; }
        if (*t == 'x') { t++; e = 1; if (*t == '^') { t++; e = 0; while (isdigit((unsigned char)*t)) e = e * 10 + (*t++ - '0'); } }
        else if (!have_c) { fprintf(stderr, "bad poly %s\n", s); exit(2); }
        coef[e] = (coef[e] + c) % p;
        if (*t == '+') t++;
    }
    if (coef[k] != 1) { fprintf(stderr, "poly %s is not monic of degree %d\n", s, k); exit(2); }
}
static void make_field(fld *F, int q, const char *poly) {
    int p = 0; for (int t = 2; t <= q; t++) if (q % t == 0) { p = t; break; }
    int k = 0, x = q; while (x % p == 0) { x /= p; k++; }
    if (x != 1) { fprintf(stderr, "%d not a prime power\n", q); exit(2); }
    F->q = q; F->p = p; F->k = k;
    if (k == 1) { memset(F->poly, 0, sizeof F->poly); F->poly[1] = 1; }
    else { if (!poly) { fprintf(stderr, "GF(%d) needs a poly\n", q); exit(2); } parse_poly(poly, p, F->poly, k); }
    F->add = malloc(sizeof(int) * q * q); F->mul = malloc(sizeof(int) * q * q); F->neg = malloc(sizeof(int) * q); F->inv = malloc(sizeof(int) * q);
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int da[16], db[16], aa = a, bb = b;
        for (int i = 0; i < k; i++) { da[i] = aa % p; aa /= p; db[i] = bb % p; bb /= p; }
        int s = 0, pw = 1; for (int i = 0; i < k; i++) { s += ((da[i] + db[i]) % p) * pw; pw *= p; }
        F->add[a * q + b] = s;
        int pr[32] = {0};
        for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) pr[i + j] = (pr[i + j] + da[i] * db[j]) % p;
        for (int i = 2 * k - 2; i >= k; i--) { int t = pr[i]; if (!t) continue; for (int j = 0; j <= k; j++) pr[i - k + j] = ((pr[i - k + j] - t * F->poly[j]) % p + p) % p; }
        s = 0; pw = 1; for (int i = 0; i < k; i++) { s += pr[i] * pw; pw *= p; }
        F->mul[a * q + b] = s;
    }
    for (int a = 0; a < q; a++) { F->neg[a] = -1; F->inv[a] = -1;
        for (int b = 0; b < q; b++) { if (F->add[a * q + b] == 0) F->neg[a] = b; if (F->mul[a * q + b] == 1) F->inv[a] = b; } }
    for (int a = 1; a < q; a++) if (F->inv[a] < 0) { fprintf(stderr, "GF(%d): poly not irreducible\n", q); exit(2); }
}
#define AD(F, a, b) ((F)->add[(a) * (F)->q + (b)])
#define MU(F, a, b) ((F)->mul[(a) * (F)->q + (b)])
static inline long long sl_key(const fld *F, int a, int b, int c, int d) {
    long long q = F->q; (void)d;
    if (a) return ((long long)(a - 1) * q + b) * q + c;
    return (q - 1) * q * q + (long long)(b - 1) * q + d;
}
static inline void sl_dec(const fld *F, long long key, int *m) {
    long long q = F->q;
    if (key < (q - 1) * q * q) { int a = (int)(key / (q * q)) + 1, b = (int)(key / q % q), c = (int)(key % q);
        m[0] = a; m[1] = b; m[2] = c; m[3] = MU(F, F->inv[a], AD(F, 1, MU(F, b, c))); }
    else { long long r = key - (q - 1) * q * q; int b = (int)(r / q) + 1, d = (int)(r % q);
        m[0] = 0; m[1] = b; m[2] = F->neg[F->inv[b]]; m[3] = d; }
}
static inline long long sl_mulkey(const fld *F, const int *s, long long gk) {   /* key of s * g */
    int g[4]; sl_dec(F, gk, g);
    int a = AD(F, MU(F, s[0], g[0]), MU(F, s[1], g[2])), b = AD(F, MU(F, s[0], g[1]), MU(F, s[1], g[3]));
    int c = AD(F, MU(F, s[2], g[0]), MU(F, s[3], g[2])), d = AD(F, MU(F, s[2], g[1]), MU(F, s[3], g[3]));
    return sl_key(F, a, b, c, d);
}

/* ---- G = Q1 [x Q2] x Z_n ---- */
static int nq;                 /* 1 or 2 matrix factors */
static fld FF[2]; static long long QO[2];
static long long NCYC, NN;
typedef struct { int m[2][4]; int z; } gen;
static gen GS[64], GI[64]; static int d, D;

static inline long long gmul(const gen *s, long long x) {   /* index of s * x */
    long long z = x % NCYC, qx = x / NCYC, out;
    if (nq == 1) out = sl_mulkey(&FF[0], s->m[0], qx);
    else { long long x1 = qx / QO[1], x2 = qx % QO[1]; out = sl_mulkey(&FF[0], s->m[0], x1) * QO[1] + sl_mulkey(&FF[1], s->m[1], x2); }
    long long zz = (z + s->z) % NCYC; if (zz < 0) zz += NCYC;
    return out * NCYC + zz;
}
static void inv_gen(const gen *s, gen *t) {
    for (int f = 0; f < nq; f++) { const fld *F = &FF[f]; const int *m = s->m[f];
        t->m[f][0] = m[3]; t->m[f][1] = F->neg[m[1]]; t->m[f][2] = F->neg[m[2]]; t->m[f][3] = m[0]; }
    t->z = (int)((NCYC - s->z % NCYC) % NCYC);
}
static long long ident(void) {
    long long qi = 0;
    for (int f = 0; f < nq; f++) qi = qi * (f ? QO[f] : 1) + sl_key(&FF[f], 1, 0, 0, 1);
    if (nq == 2) qi = sl_key(&FF[0], 1, 0, 0, 1) * QO[1] + sl_key(&FF[1], 1, 0, 0, 1);
    return qi * NCYC;
}
static long long gen_index(const gen *s) {
    long long qi = nq == 1 ? sl_key(&FF[0], s->m[0][0], s->m[0][1], s->m[0][2], s->m[0][3])
                           : sl_key(&FF[0], s->m[0][0], s->m[0][1], s->m[0][2], s->m[0][3]) * QO[1] + sl_key(&FF[1], s->m[1][0], s->m[1][1], s->m[1][2], s->m[1][3]);
    return qi * NCYC + ((s->z % NCYC) + NCYC) % NCYC;
}

/* BFS from (e, side0); returns eccentricity, sets *unreached */
static int bfs(int side0, long long *unreached, int nth) {
    size_t W = (size_t)((NN + 63) / 64);
    uint64_t *vis[2], *fr = calloc(W, 8), *nx = calloc(W, 8);
    vis[0] = calloc(W, 8); vis[1] = calloc(W, 8);
    if (!fr || !nx || !vis[0] || !vis[1]) { fprintf(stderr, "out of memory\n"); exit(2); }
    long long e = ident(); vis[side0][e >> 6] |= 1ULL << (e & 63); fr[e >> 6] |= 1ULL << (e & 63);
    int side = side0, ecc = 0; long long reached = 1;
    for (;;) {
        const gen *T = side == 0 ? GS : GI; int ns = side ^ 1; uint64_t *vn = vis[ns];
        memset(nx, 0, W * 8);
        #pragma omp parallel for schedule(dynamic, 4096) num_threads(nth)
        for (size_t w = 0; w < W; w++) {
            uint64_t f = fr[w];
            while (f) { int b = __builtin_ctzll(f); f &= f - 1; long long x = (long long)w * 64 + b;
                for (int i = 0; i < d; i++) { long long y = gmul(&T[i], x);
                    uint64_t bit = 1ULL << (y & 63);
                    if (!(vn[y >> 6] & bit)) __atomic_fetch_or(&nx[y >> 6], bit, __ATOMIC_RELAXED); } }
        }
        long long add = 0;
        #pragma omp parallel for reduction(+:add) num_threads(nth)
        for (size_t w = 0; w < W; w++) { uint64_t n = nx[w] & ~vn[w]; nx[w] = n; vn[w] |= n; add += __builtin_popcountll(n); }
        if (!add) break;
        reached += add; ecc++; side = ns; uint64_t *t = fr; fr = nx; nx = t;
        fprintf(stderr, "  BFS from %c: step %d, +%lld, reached %lld of %lld\n", side0 ? 'B' : 'A', ecc, add, reached, 2 * NN);
    }
    *unreached = 2 * NN - reached;
    free(fr); free(nx); free(vis[0]); free(vis[1]);
    return ecc;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: check_lowmem SOL.txt [threads]\n"); return 2; }
    int nth = argc > 2 ? atoi(argv[2]) : 1;
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    /* header: d D <spec> n NCYC N NTOT ; spec = sl q [poly P] | prod sl q [poly P] sl q [poly P] */
    char *tok[64]; int nt = 0; for (char *t = strtok(line, " \t\n"); t && nt < 64; t = strtok(NULL, " \t\n")) tok[nt++] = t;
    d = atoi(tok[0]); D = atoi(tok[1]); int i = 2;
    if (!strcmp(tok[i], "prod")) { nq = 2; i++; } else nq = 1;
    for (int fq = 0; fq < nq; fq++) {
        if (strcmp(tok[i], "sl") && strcmp(tok[i], "psl")) { fprintf(stderr, "only sl/psl (char 2) factors supported, got %s\n", tok[i]); return 2; }
        int q = atoi(tok[i + 1]); i += 2; const char *poly = NULL;
        if (i < nt && !strcmp(tok[i], "poly")) { poly = tok[i + 1]; i += 2; }
        make_field(&FF[fq], q, poly);
        if (!strcmp(tok[i - (poly ? 4 : 2)], "psl") && FF[fq].p != 2) { fprintf(stderr, "psl in odd characteristic not supported\n"); return 2; }
        QO[fq] = (long long)q * q * q - q;
    }
    if (strcmp(tok[i], "n")) { fprintf(stderr, "expected n, got %s\n", tok[i]); return 2; }
    NCYC = atoll(tok[i + 1]); long long Nfile = atoll(tok[i + 3]);
    NN = (nq == 1 ? QO[0] : QO[0] * QO[1]) * NCYC;
    if (NN != Nfile) { fprintf(stderr, "order mismatch: computed %lld, file %lld\n", NN, Nfile); return 1; }
    for (int s = 0; s < d; s++) {
        if (!fgets(line, sizeof line, f)) { fprintf(stderr, "missing generator %d\n", s); return 2; }
        char *p = line; int got = 0;
        for (int fq = 0; fq < nq; fq++) { p = strstr(p, "mat("); if (!p) break;
            int a, b, c, dd; if (sscanf(p, "mat(%d,%d,%d,%d)", &a, &b, &c, &dd) != 4) break;
            GS[s].m[fq][0] = a; GS[s].m[fq][1] = b; GS[s].m[fq][2] = c; GS[s].m[fq][3] = dd; got++; p += 4;
            const fld *F = &FF[fq];   /* det = 1 */
            if (AD(F, MU(F, a, dd), F->neg[MU(F, b, c)]) != 1) { fprintf(stderr, "generator %d factor %d: det != 1\n", s, fq); return 1; } }
        char *zp = strstr(line, "z="); if (got != nq || !zp) { fprintf(stderr, "bad generator line %s", line); return 2; }
        GS[s].z = atoi(zp + 2); inv_gen(&GS[s], &GI[s]);
    }
    fclose(f);
    for (int a = 0; a < d; a++) for (int b = 0; b < a; b++) if (gen_index(&GS[a]) == gen_index(&GS[b])) { printf("INVALID: generators %d and %d coincide\n", a, b); return 1; }
    printf("group: %s factor(s), N = %lld, vertices %lld, d = %d, D = %d, generators distinct\n", nq == 1 ? "one" : "two", NN, 2 * NN, d, D);
    long long uA, uB; int eA = bfs(0, &uA, nth); printf("ecc from (e,A) = %d, unreached %lld\n", eA, uA); fflush(stdout);
    int eB = bfs(1, &uB, nth); printf("ecc from (e,B) = %d, unreached %lld\n", eB, uB);
    if (!uA && !uB && eA <= D && eB <= D) printf("VALID d=%d D=%d N=%lld vertices=%lld diameter=%d\n", d, D, NN, 2 * NN, eA > eB ? eA : eB);
    else printf("INVALID\n");
    return 0;
}
