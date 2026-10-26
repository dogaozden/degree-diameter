/* haarcheck_pp: independent, low-memory diameter check of a Haar graph H(G,S), G = SL(2,q) x Z_n, q any prime power.
 * Same definitions and BFS as ../../frontier/haarcheck_sl.c (which handles prime q only): vertices (g,A),(g,B),
 * edges (g,A) ~ (s g, B), right multiplication by G transitive on each side, so BFS from (e,A) and (e,B) gives the
 * exact diameter.  Field GF(q) is built exactly as in haar_sym.c (make_field: first monic irreducible of degree k
 * in lexicographic order, element = sum c_i p^i), so a haar_sym solution file is read with the same meaning.
 * Index: c != 0: (c,a,d) -> b = (ad-1)/c, index (c-1) q^2 + a q + d; c = 0: a != 0, d = a^-1, index (q-1) q^2 + (a-1) q + b.
 * Memory: 4 bitsets of N bits.  Usage: haarcheck_pp SOL.txt   Build: cc -O3 -o haarcheck_pp haarcheck_pp.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { int q, p, k; int poly[16]; uint16_t *add, *mul, *neg, *inv; } field;
static int pdeg(const int *f, int len) { for (int i = len - 1; i >= 0; i--) if (f[i]) return i; return -1; }
static int irreducible(const int *f, int k, int p) {  /* brute force: no monic factor of degree 1..k/2 */
    for (int dg = 1; dg <= k / 2; dg++) {
        long long cnt = 1; for (int i = 0; i < dg; i++) cnt *= p;
        for (long long code = 0; code < cnt; code++) {
            int g[16] = {0}; long long c = code; for (int i = 0; i < dg; i++) { g[i] = (int)(c % p); c /= p; } g[dg] = 1;
            int r[16]; memcpy(r, f, sizeof r);
            for (int i = k; i >= dg; i--) {
                int t = r[i]; if (!t) continue;
                for (int j = 0; j <= dg; j++) r[i - dg + j] = ((r[i - dg + j] - t * g[j]) % p + p) % p;
            }
            if (pdeg(r, 16) < 0) return 0;
        }
    }
    return 1;
}
static field *make_field(int q) {   /* same construction as haar_sym.c */
    field *F = calloc(1, sizeof *F); F->q = q;
    int p = 0; for (int t = 2; t <= q; t++) if (q % t == 0) { p = t; break; }
    int k = 0, x = q; while (x % p == 0) { x /= p; k++; }
    if (x != 1) { fprintf(stderr, "%d is not a prime power\n", q); exit(2); }
    F->p = p; F->k = k;
    if (k == 1) { F->poly[1] = 1; }
    else {
        long long cnt = 1; for (int i = 0; i < k; i++) cnt *= p;
        for (long long code = 0; code < cnt; code++) {
            int f[16] = {0}; long long c = code; for (int i = 0; i < k; i++) { f[i] = (int)(c % p); c /= p; } f[k] = 1;
            if (f[0] && irreducible(f, k, p)) { memcpy(F->poly, f, sizeof f); break; }
        }
    }
    F->add = malloc(2 * (size_t)q * q); F->mul = malloc(2 * (size_t)q * q);
    F->neg = malloc(2 * (size_t)q); F->inv = malloc(2 * (size_t)q);
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int da[16] = {0}, db[16] = {0}, s = 0, pw = 1, aa = a, bb = b;
        for (int i = 0; i < k; i++) { da[i] = aa % p; aa /= p; db[i] = bb % p; bb /= p; }
        for (int i = 0; i < k; i++) { s += ((da[i] + db[i]) % p) * pw; pw *= p; }
        F->add[a * q + b] = (uint16_t)s;
        int pr[32] = {0};
        for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) pr[i + j] = (pr[i + j] + da[i] * db[j]) % p;
        for (int i = 2 * k - 2; i >= k; i--) { int t = pr[i]; if (!t) continue; for (int j = 0; j <= k; j++) pr[i - k + j] = ((pr[i - k + j] - t * F->poly[j]) % p + p) % p; }
        s = 0; pw = 1; for (int i = 0; i < k; i++) { s += pr[i] * pw; pw *= p; }
        F->mul[a * q + b] = (uint16_t)s;
    }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) { if (F->add[a * q + b] == 0) F->neg[a] = (uint16_t)b; if (F->mul[a * q + b] == 1) F->inv[a] = (uint16_t)b; }
    for (int a = 1; a < q; a++) if (F->mul[a * q + F->inv[a]] != 1) { fprintf(stderr, "field error\n"); exit(2); }
    return F;
}
static void poly_str(const field *F, char *buf) {   /* same format as haar_sym.c: "x^3+2x+1" */
    char *s = buf; *s = 0; int first = 1;
    for (int i = F->k; i >= 0; i--) {
        int c = F->poly[i]; if (!c) continue;
        if (!first) *s++ = '+';
        first = 0;
        if (i == 0) s += sprintf(s, "%d", c);
        else { if (c != 1) s += sprintf(s, "%d", c); s += sprintf(s, i == 1 ? "x" : "x^%d", i); }
    }
}
#define FADD(a, b) (F->add[(a) * q + (b)])
#define FMUL(a, b) (F->mul[(a) * q + (b)])
#define FNEG(a) (F->neg[(a)])
#define FINV(a) (F->inv[(a)])

typedef struct { int a, b, c, d; long long z; } el;
static field *F; static int q; static long long n, N;
static long long enc(int a, int b, int c, int d, long long z) {
    long long k;
    if (c) k = ((long long)(c - 1) * q + a) * q + d;
    else k = (long long)(q - 1) * q * q + (long long)(a - 1) * q + b;
    return k * n + z;
}
static void dec(long long g, int *a, int *b, int *c, int *d, long long *z) {
    *z = g % n; long long k = g / n;
    if (k < (long long)(q - 1) * q * q) {
        *c = (int)(k / ((long long)q * q)) + 1; *a = (int)(k / q % q); *d = (int)(k % q);
        *b = FMUL(FADD(FMUL(*a, *d), FNEG(1)), FINV(*c));
    } else {
        k -= (long long)(q - 1) * q * q; *c = 0; *a = (int)(k / q) + 1; *b = (int)(k % q); *d = FINV(*a);
    }
}
static int det1(int a, int b, int c, int d) { return FADD(FMUL(a, d), FNEG(FMUL(b, c))) == 1; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_pp SOL.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    int dg, D; char fam[64], hpoly[128] = ""; int qq; long long NN;
    if (strstr(line, " poly ")) {   /* "d D sl q poly x^3+x+1 n n N N" (prime powers) */
        if (sscanf(line, "%d %d %63s %d poly %127s n %lld N %lld", &dg, &D, fam, &qq, hpoly, &n, &NN) != 7 || strcmp(fam, "sl")) {
            fprintf(stderr, "only 'sl q' headers: %s", line); return 2; }
    } else if (sscanf(line, "%d %d %63s %d n %lld N %lld", &dg, &D, fam, &qq, &n, &NN) != 6 || strcmp(fam, "sl")) {
        fprintf(stderr, "only 'sl q' headers: %s", line); return 2; }
    q = qq; F = make_field(q);
    if (hpoly[0]) { char ps[128]; poly_str(F, ps); if (strcmp(ps, hpoly)) { fprintf(stderr, "field poly %s != header %s\n", ps, hpoly); return 2; } }
    N = (long long)q * ((long long)q * q - 1) * n;
    if (N != NN) { fprintf(stderr, "header N %lld != q(q^2-1)n = %lld\n", NN, N); return 2; }
    el S[64], SI[64]; int k = 0;
    while (fgets(line, sizeof line, f) && k < 64) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z=");
        if (!m || !zz) continue;
        int a, b, c, d; long long z;
        if (sscanf(m, "mat(%d,%d,%d,%d)", &a, &b, &c, &d) != 4 || sscanf(zz, "z=%lld", &z) != 1) return 2;
        if (a < 0 || a >= q || b < 0 || b >= q || c < 0 || c >= q || d < 0 || d >= q || z < 0 || z >= n || !det1(a, b, c, d)) {
            fprintf(stderr, "bad element: %s", line); return 2; }
        S[k] = (el){a, b, c, d, z}; SI[k] = (el){d, FNEG(b), FNEG(c), a, (n - z) % n}; k++;
    }
    if (k != dg) { fprintf(stderr, "read %d elements, expected %d\n", k, dg); return 2; }
    for (int i = 0; i < k; i++) for (int j = 0; j < i; j++)
        if (!memcmp(&S[i], &S[j], sizeof(el))) { fprintf(stderr, "repeated generator %d %d\n", i, j); return 2; }
    /* self-test of enc/dec */
    for (long long g = 0; g < N; g += N / 1000 + 1) { int a, b, c, d; long long z; dec(g, &a, &b, &c, &d, &z);
        if (!det1(a, b, c, d) || enc(a, b, c, d, z) != g) { fprintf(stderr, "index self-test failed\n"); return 2; } }
    long long W = (N + 63) / 64;
    uint64_t *vis[2], *cur[2], *nxt[2];
    for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); cur[s] = calloc(W, 8); nxt[s] = calloc(W, 8); }
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
                    int a, b, c, d; long long z; dec(g, &a, &b, &c, &d, &z);
                    for (int i = 0; i < k; i++) { const el *s = &T[i];
                        long long h = enc(FADD(FMUL(s->a, a), FMUL(s->b, c)), FADD(FMUL(s->a, b), FMUL(s->b, d)),
                                          FADD(FMUL(s->c, a), FMUL(s->d, c)), FADD(FMUL(s->c, b), FMUL(s->d, d)), (s->z + z) % n);
                        uint64_t m1 = 1ULL << (h & 63);
                        if (!(vis[ns][h >> 6] & m1)) { vis[ns][h >> 6] |= m1; nxt[ns][h >> 6] |= m1; add++; } } } }
            memset(cur[side], 0, W * 8); uint64_t *t = cur[ns]; cur[ns] = nxt[ns]; nxt[ns] = t;
            reached[ns] += add; if (add) ecc = step; side = ns;
        }
        printf("from (e,%c): reached A %lld/%lld, B %lld/%lld within %d, ecc %d\n", start ? 'B' : 'A', reached[0], N, reached[1], N, D, ecc);
        if (reached[0] != N || reached[1] != N) bad = 1;
    }
    printf("%s d=%d D=%d group=sl %d x Z_%lld (GF(%d)) N=%lld vertices=%lld (distinct generators, %d-regular simple)\n",
           bad ? "INVALID" : "VALID", dg, D, q, n, q, N, 2 * N, dg);
    return bad;
}
