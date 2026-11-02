/* haarcheck_lean (job raise-d11, 2026-11-02): independent diameter check of a Haar graph H(G,S) with two bitsets,
 *     G = SL(2,p) x Z_n  or  PSL(2,p) x Z_n,   p an odd prime < 2^15.
 * Reads a haar_gen3 / haar_big solution file: header "d D sl|psl p n NCYC N NTOT", then d lines "... mat(a,b,c,d) z=Z"
 * (only the mat/z descriptions are used; either sign may be given for psl).
 * Written from the definitions for this job; it shares no code with haarcheck_gen.c, haarcheck_sl.c, haarcheck_psl.c or
 * the search programs.  Own element index: canonical matrix (psl: the sign with the first nonzero of (c, d) in
 * 1..(p-1)/2), then
 *     c != 0:  core = ((c - 1) p + d) p + a          (b = (a d - 1) / c)
 *     c == 0:  core = CM p^2 + (d - 1) p + b         (a = 1 / d)
 * with CM = p - 1 (sl) or (p - 1)/2 (psl); index = core * n + z.  Products use a p x p multiplication table.
 * Graph: vertices (g,A), (g,B); edges (g,A) ~ (s g, B).  Right multiplication by G is transitive on each side, so BFS
 * from (e,A) and from (e,B), each reaching every vertex within D steps, is exactly diameter <= D.
 * BFS with monotone balls: in a bipartite graph the vertices first reached at step L all lie on one side, so step L
 * updates only that side T from the other side S (which holds the ball of radius L-1 on S):
 *     T = B:  y joins iff s^-1 y is in S for some s      (push: x in S gives s x)
 *     T = A:  y joins iff s y is in S for some s         (push: x in S gives s^-1 x)
 * Push (atomic OR) while the source is sparse, pull (word-owned, no races) afterwards.  Memory: two bitsets of N bits.
 * Self-tests: index round trip (all elements if N <= 2e7, else 10^6 random), associativity and inverses on random
 * triples, generators of determinant 1 and pairwise distinct.
 * Usage: haarcheck_lean SOL [A|B]       Build: cc -O3 -fopenmp -o haarcheck_lean haarcheck_lean.c
 * Exit 0 iff VALID; last line "VALID ..." / "INVALID ..." (with A or B alone: HALF-VALID / HALF-INVALID). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>
typedef long long ll; typedef uint64_t u64; typedef uint16_t u16;
static ll p, n, N, CM, H; static int PSL;
static u16 *MT;            /* MT[x * p + y] = x y mod p */
static ll *INVT;
typedef struct { int a, b, c, d; ll z; } el;
static inline int ad(int x, int y) { int s = x + y; return s >= p ? s - (int)p : s; }
static inline int ng(int x) { return x ? (int)p - x : 0; }
static inline int ml(int x, int y) { return MT[(ll)x * p + y]; }
static inline el canon(el x) {
    if (PSL) { int f = x.c ? x.c : x.d; if (f > H) { x.a = ng(x.a); x.b = ng(x.b); x.c = ng(x.c); x.d = ng(x.d); } }
    return x;
}
static inline el gm(el x, el y) {
    el r; r.a = ad(ml(x.a, y.a), ml(x.b, y.c)); r.b = ad(ml(x.a, y.b), ml(x.b, y.d));
    r.c = ad(ml(x.c, y.a), ml(x.d, y.c)); r.d = ad(ml(x.c, y.b), ml(x.d, y.d));
    r.z = x.z + y.z; if (r.z >= n) r.z -= n; return canon(r);
}
static inline el gi(el x) { el r = {x.d, ng(x.b), ng(x.c), x.a, x.z ? n - x.z : 0}; return canon(r); }
static inline ll enc(el x) {
    ll core = x.c ? (((ll)(x.c - 1) * p + x.d) * p + x.a) : (CM * p * p + (ll)(x.d - 1) * p + x.b);
    return core * n + x.z;
}
static inline el dec(ll g) {
    el x; x.z = g % n; ll core = g / n;
    if (core < CM * p * p) { x.c = (int)(core / (p * p)) + 1; x.d = (int)(core / p % p); x.a = (int)(core % p);
        x.b = ml(ad(ml(x.a, x.d), (int)p - 1), (int)INVT[x.c]); }
    else { core -= CM * p * p; x.d = (int)(core / p) + 1; x.b = (int)(core % p); x.a = (int)INVT[x.d]; x.c = 0; }
    return x;
}
static int eqel(el x, el y) { return x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d && x.z == y.z; }
static u64 rs = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static ll pmod(ll x) { x %= p; return x < 0 ? x + p : x; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_lean SOL [A|B]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096], fam[16]; int d, D; ll NN;
    if (!fgets(line, sizeof line, f) || sscanf(line, "%d %d %15s %lld n %lld N %lld", &d, &D, fam, &p, &n, &NN) != 6) { fprintf(stderr, "bad header\n"); return 2; }
    if (!strcmp(fam, "psl")) PSL = 1; else if (strcmp(fam, "sl")) { fprintf(stderr, "family must be sl or psl\n"); return 2; }
    if (p < 3 || p >= 32768 || n < 1) { fprintf(stderr, "need odd prime p < 32768, n >= 1\n"); return 2; }
    for (ll t = 2; t * t <= p; t++) if (p % t == 0) { fprintf(stderr, "p not prime\n"); return 2; }
    H = (p - 1) / 2; CM = PSL ? H : p - 1;
    N = (PSL ? p * (p * p - 1) / 2 : p * (p * p - 1)) * n;
    if (N != NN) { fprintf(stderr, "header N %lld, |G| = %lld\n", NN, N); return 2; }
    MT = malloc(sizeof(u16) * p * p); INVT = malloc(sizeof(ll) * p);
    for (ll x = 0; x < p; x++) for (ll y = 0; y < p; y++) MT[x * p + y] = (u16)(x * y % p);
    INVT[0] = 0; for (ll x = 1; x < p; x++) { ll r = 1, b = x, e = p - 2; while (e) { if (e & 1) r = r * b % p; b = b * b % p; e >>= 1; } INVT[x] = r; }
    el S[256], SI[256]; int ns = 0;
    while (fgets(line, sizeof line, f) && ns < d) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z="); if (!m || !zz) continue;
        ll a, b, c, dd, z; if (sscanf(m, "mat(%lld,%lld,%lld,%lld)", &a, &b, &c, &dd) != 4 || sscanf(zz, "z=%lld", &z) != 1) { fprintf(stderr, "bad line\n"); return 2; }
        el x = {(int)pmod(a), (int)pmod(b), (int)pmod(c), (int)pmod(dd), ((z % n) + n) % n};
        if (pmod((ll)x.a * x.d - (ll)x.b * x.c) != 1) { fprintf(stderr, "det != 1: %s", line); return 2; }
        S[ns++] = canon(x);
    }
    if (ns != d) { fprintf(stderr, "%d generators, header says %d\n", ns, d); return 2; }
    for (int i = 0; i < d; i++) for (int j = 0; j < i; j++) if (eqel(S[i], S[j])) { fprintf(stderr, "repeated generator\n"); return 2; }
    for (int i = 0; i < d; i++) SI[i] = gi(S[i]);
    el E = canon((el){1, 0, 0, 1, 0});
    /* self-tests */
    ll nt = N <= 20000000 ? N : 1000000;
    for (ll t = 0; t < nt; t++) { ll g = N <= 20000000 ? t : (ll)(rnd() % (u64)N); el x = dec(g);
        if (pmod((ll)x.a * x.d - (ll)x.b * x.c) != 1 || enc(x) != g || !eqel(canon(x), x)) { fprintf(stderr, "index self-test failed at %lld\n", g); return 2; } }
    for (int t = 0; t < 200000; t++) { el x = dec((ll)(rnd() % (u64)N)), y = dec((ll)(rnd() % (u64)N)), w = dec((ll)(rnd() % (u64)N));
        if (!eqel(gm(gm(x, y), w), gm(x, gm(y, w))) || !eqel(gm(x, gi(x)), E) || !eqel(gm(E, x), x)) { fprintf(stderr, "group self-test failed\n"); return 2; } }
    for (int i = 0; i < d; i++) if (!eqel(gm(S[i], SI[i]), E)) { fprintf(stderr, "generator inverse failed\n"); return 2; }
    printf("haarcheck_lean: %s %lld x Z_%lld, N = %lld, vertices %lld, d = %d, D = %d; self-tests ok (%lld index round trips)\n",
           fam, p, n, N, 2 * N, d, D, nt);
    fflush(stdout);
    ll W = (N + 63) / 64; u64 lastmask = (N & 63) ? ((1ULL << (N & 63)) - 1) : ~0ULL;
    u64 *V[2]; for (int s = 0; s < 2; s++) { V[s] = aligned_alloc(64, ((W * 8 + 63) / 64) * 64); if (!V[s]) { fprintf(stderr, "out of memory\n"); return 2; } }
    int which = argc > 2 ? argv[2][0] : 0, ok = 1;
    ll e0 = enc(E);
    for (int root = 0; root < 2; root++) {
        if ((which == 'A' && root == 1) || (which == 'B' && root == 0)) continue;
        double t0 = now();
        memset(V[0], 0, W * 8); memset(V[1], 0, W * 8);
        V[root][e0 >> 6] |= 1ULL << (e0 & 63);
        ll cnt[2] = {0, 0}; cnt[root] = 1; int full_at = -1;
        for (int L = 1; L <= D; L++) {
            int T = root ^ (L & 1), Sd = T ^ 1;   /* target side, source side */
            u64 *src = V[Sd], *tg = V[T];
            el *M = T == 1 ? S : SI;               /* push: x -> M x;  pull: y needs Q y in src, Q = SI (T = B) or S (T = A) */
            el *Q = T == 1 ? SI : S;
            /* push costs |src| d random writes; pull costs (unreached targets) x (tests until a hit, about N/|src|, at most d) */
            double unr = (double)(N - cnt[T]), tests = (double)N / (double)(cnt[Sd] > 0 ? cnt[Sd] : 1);
            if (tests > d) tests = d;
            int push = (double)cnt[Sd] * d < unr * tests;
            if (push) {
                #pragma omp parallel for schedule(dynamic, 1024)
                for (ll w = 0; w < W; w++) {
                    u64 bits = src[w];
                    while (bits) { int b = __builtin_ctzll(bits); bits &= bits - 1; el x = dec(w * 64 + b);
                        for (int i = 0; i < d; i++) { ll y = enc(gm(M[i], x)); __atomic_fetch_or(&tg[y >> 6], 1ULL << (y & 63), __ATOMIC_RELAXED); } }
                }
            } else {
                #pragma omp parallel for schedule(dynamic, 4096)
                for (ll w = 0; w < W; w++) {
                    u64 have = tg[w], full = (w == W - 1) ? lastmask : ~0ULL, miss = ~have & full, add = 0;
                    while (miss) { int b = __builtin_ctzll(miss); miss &= miss - 1; el y = dec(w * 64 + b);
                        for (int i = 0; i < d; i++) { ll x = enc(gm(Q[i], y)); if ((src[x >> 6] >> (x & 63)) & 1) { add |= 1ULL << b; break; } } }
                    tg[w] = have | add;
                }
            }
            ll c = 0;
            #pragma omp parallel for reduction(+:c)
            for (ll w = 0; w < W; w++) c += __builtin_popcountll(tg[w]);
            cnt[T] = c;
            printf("  root (e,%c) step %d (%s): side %c has %lld of %lld   [%.0f s]\n", root ? 'B' : 'A', L, push ? "push" : "pull",
                   T ? 'B' : 'A', c, N, now() - t0);
            fflush(stdout);
            if (full_at < 0 && cnt[0] == N && cnt[1] == N) full_at = L;
        }
        int good = cnt[0] == N && cnt[1] == N;
        printf("root (e,%c): %s, every vertex within %d at step %d (unreached A %lld, B %lld), %.0f s\n", root ? 'B' : 'A',
               good ? "complete" : "INCOMPLETE", D, full_at, N - cnt[0], N - cnt[1], now() - t0);
        if (!good) ok = 0;
    }
    const char *tag = (which == 'A' || which == 'B') ? (ok ? "HALF-VALID" : "HALF-INVALID") : (ok ? "VALID" : "INVALID");
    printf("%s d=%d D=%d group=%s %lld x Z_%lld N=%lld vertices=%lld%s\n", tag, d, D, fam, p, n, N, 2 * N,
           (which == 'A' || which == 'B') ? (which == 'A' ? " (root (e,A) only)" : " (root (e,B) only)") : "");
    return ok ? 0 : 1;
}
