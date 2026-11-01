/* metacheck.c — independent low-memory diameter check of a Haar graph H(G,S) where G is a direct product of
 * metacyclic groups Z_m x|_r Z_k (one or more factors) and a cyclic group Z_n.  Job beyond-d15 (2026-11-01, director).
 *
 * Input: a haar_gen3 / hmeta solution file
 *   "d D meta m k r n NC N .."                       (one factor), or
 *   "d D prod meta m1 k1 r1 meta m2 k2 r2 n NC N .."  (product of two factors; any number of "meta m k r" groups),
 * then d lines, each containing one "meta(a=A,j=J)" per factor (in order) and optionally "z=Z".
 * The generator index column is ignored: only the (a,j,z) coordinates are used.
 *
 * Own group code (nothing from hmeta or haar_gen3): (a,j)(b,l) = (a + r^j b mod m, j + l mod k), z adds mod n.
 * Checks r^k = 1 mod m, associativity, identity and inverses on 20,000 random triples, and that the d generators are
 * distinct.  Graph: vertices (g,A), (g,B); edges (g,A) ~ (s g, B) for s in S (haar_gen3 convention).  Right
 * multiplication by G is an automorphism transitive on each side, so the diameter is <= D iff the BFS from (e,A) and
 * the BFS from (e,B) each reach all 2N vertices within D steps.  BFS: level-synchronous over bitsets (4 bitsets of N
 * bits), the frontier expanded by LEFT multiplication s g (A -> B) and s^-1 h (B -> A) — not the right-multiplication
 * row rotations hmeta uses.  Prints level sizes, eccentricities and VALID / INVALID.
 * Build: gcc -O3 -march=native -fopenmp -o metacheck metacheck.c      Run: OMP_NUM_THREADS=2 ./metacheck SOL */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <omp.h>
typedef int64_t i64; typedef uint64_t u64;
#define MAXF 4
#define MAXD 16
static int NF; static i64 FM[MAXF], FK[MAXF], FR[MAXF], NZ; static i64 *RP[MAXF]; static i64 N;
static int d, D;
typedef struct { i64 a[MAXF], j[MAXF], z; } el;
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static i64 pmod(i64 x, i64 m) { x %= m; return x < 0 ? x + m : x; }
static i64 mulmod(i64 a, i64 b, i64 m) { return (i64)((__int128)a * b % m); }
static el emul(el x, el y) {
    el r; for (int t = 0; t < NF; t++) { r.a[t] = (x.a[t] + mulmod(RP[t][x.j[t]], y.a[t], FM[t])) % FM[t]; r.j[t] = (x.j[t] + y.j[t]) % FK[t]; }
    r.z = (x.z + y.z) % NZ; return r;
}
static el einv(el x) {
    el r; for (int t = 0; t < NF; t++) { i64 jj = pmod(-x.j[t], FK[t]); r.j[t] = jj; r.a[t] = pmod(-mulmod(RP[t][jj], x.a[t], FM[t]), FM[t]); }
    r.z = pmod(-x.z, NZ); return r;
}
static int eeq(el x, el y) { for (int t = 0; t < NF; t++) if (x.a[t] != y.a[t] || x.j[t] != y.j[t]) return 0; return x.z == y.z; }
/* index: mixed radix over factors (a*k + j), then z (same layout as metacheck2.py; only used for the bitsets) */
static i64 enc(const el *x) { i64 g = 0; for (int t = 0; t < NF; t++) g = g * (FM[t] * FK[t]) + x->a[t] * FK[t] + x->j[t]; return g * NZ + x->z; }
static void dec(i64 g, el *x) { x->z = g % NZ; g /= NZ; for (int t = NF - 1; t >= 0; t--) { i64 q = g % (FM[t] * FK[t]); g /= FM[t] * FK[t]; x->a[t] = q / FK[t]; x->j[t] = q % FK[t]; } }
static u64 rs = 88172645463325252ULL; static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static el erand(void) { el x; for (int t = 0; t < NF; t++) { x.a[t] = rnd() % FM[t]; x.j[t] = rnd() % FK[t]; } x.z = rnd() % NZ; return x; }

static el S[MAXD], SI[MAXD];
/* one BFS from (e, side); returns max level reached-all (eccentricity) or -1 if not all reached within D */
static int bfs(int side, i64 *reachedA, i64 *reachedB, i64 *lev) {
    i64 W = (N + 63) / 64;
    u64 *vis[2], *fr = calloc(W, 8), *nx = calloc(W, 8);
    vis[0] = calloc(W, 8); vis[1] = calloc(W, 8);
    if (!fr || !nx || !vis[0] || !vis[1]) { fprintf(stderr, "out of memory\n"); exit(2); }
    vis[side][0] |= 1; fr[0] |= 1; i64 cnt[2] = {0, 0}; cnt[side] = 1; lev[0] = 1;
    int cur = side, ecc = -1;
    for (int L = 1; L <= D; L++) {
        el *gens = cur == 0 ? S : SI; int to = 1 - cur; u64 *vt = vis[to];
        memset(nx, 0, W * 8);
        i64 added = 0;
        #pragma omp parallel for schedule(dynamic, 1024) reduction(+:added)
        for (i64 w = 0; w < W; w++) {
            u64 bits = fr[w];
            while (bits) {
                int b = __builtin_ctzll(bits); bits &= bits - 1;
                i64 g = w * 64 + b; el x; dec(g, &x);
                for (int s = 0; s < d; s++) {
                    el y = emul(gens[s], x); i64 h = enc(&y);
                    u64 m = 1ULL << (h & 63);
                    if (vt[h >> 6] & m) continue;
                    u64 old = __atomic_fetch_or(&vt[h >> 6], m, __ATOMIC_RELAXED);
                    if (!(old & m)) { __atomic_fetch_or(&nx[h >> 6], m, __ATOMIC_RELAXED); added++; }
                }
            }
        }
        cnt[to] += added; lev[L] = added;
        u64 *t = fr; fr = nx; nx = t; cur = to;
        if (cnt[0] == N && cnt[1] == N && ecc < 0) ecc = L;
        if (added == 0) { for (int L2 = L + 1; L2 <= D; L2++) lev[L2] = 0; break; }
    }
    *reachedA = cnt[0]; *reachedB = cnt[1];
    free(fr); free(nx); free(vis[0]); free(vis[1]);
    return ecc;
}
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: metacheck SOL\n"); return 2; }
    double t0 = now();
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    char *tok[64]; int nt = 0; char *p = strtok(line, " \t\n"); while (p && nt < 64) { tok[nt++] = p; p = strtok(NULL, " \t\n"); }
    d = atoi(tok[0]); D = atoi(tok[1]); NF = 0; NZ = 1; i64 Nfile = -1;
    for (int i = 2; i < nt; i++) {
        if (!strcmp(tok[i], "meta") && i + 3 < nt) { FM[NF] = atoll(tok[i + 1]); FK[NF] = atoll(tok[i + 2]); FR[NF] = atoll(tok[i + 3]); NF++; i += 3; }
        else if (!strcmp(tok[i], "n") && i + 1 < nt) { NZ = atoll(tok[i + 1]); i++; }
        else if (!strcmp(tok[i], "N") && i + 1 < nt) { Nfile = atoll(tok[i + 1]); i++; }
    }
    if (NF < 1 || d < 2 || d > MAXD) { fprintf(stderr, "cannot parse header\n"); return 2; }
    N = NZ; for (int t = 0; t < NF; t++) N *= FM[t] * FK[t];
    printf("file %s\nheader: d=%d D=%d factors=%d", argv[1], d, D, NF);
    for (int t = 0; t < NF; t++) printf(" [Z%lld x|_%lld Z%lld]", (long long)FM[t], (long long)FR[t], (long long)FK[t]);
    printf(" x Z%lld  N=%lld (file says %lld)\n", (long long)NZ, (long long)N, (long long)Nfile);
    if (Nfile >= 0 && Nfile != N) { printf("INVALID: N mismatch\n"); return 1; }
    for (int t = 0; t < NF; t++) {
        RP[t] = malloc(sizeof(i64) * FK[t]); RP[t][0] = 1 % FM[t];
        for (i64 j = 1; j < FK[t]; j++) RP[t][j] = mulmod(RP[t][j - 1], FR[t], FM[t]);
        if (mulmod(RP[t][FK[t] - 1], FR[t], FM[t]) != 1 % FM[t]) { printf("INVALID: r^k != 1 mod m in factor %d\n", t); return 1; }
    }
    for (int i = 0; i < d; i++) {
        if (!fgets(line, sizeof line, f)) { printf("INVALID: missing generator lines\n"); return 1; }
        char *q = line; el x; memset(&x, 0, sizeof x);
        for (int t = 0; t < NF; t++) {
            q = strstr(q, "meta(a="); if (!q) { printf("INVALID: bad generator line %d\n", i); return 1; }
            long long A, J; if (sscanf(q, "meta(a=%lld,j=%lld)", &A, &J) != 2) { printf("INVALID: bad generator %d\n", i); return 1; }
            x.a[t] = pmod(A, FM[t]); x.j[t] = pmod(J, FK[t]); q += 7;
        }
        char *zz = strstr(line, "z="); x.z = zz ? pmod(atoll(zz + 2), NZ) : 0;
        S[i] = x; SI[i] = einv(x);
    }
    fclose(f);
    for (int i = 0; i < d; i++) for (int j = 0; j < i; j++) if (eeq(S[i], S[j])) { printf("INVALID: repeated generator\n"); return 1; }
    el E; memset(&E, 0, sizeof E);
    for (int it = 0; it < 20000; it++) {
        el x = erand(), y = erand(), z = erand();
        if (!eeq(emul(emul(x, y), z), emul(x, emul(y, z))) || !eeq(emul(x, einv(x)), E) || !eeq(emul(E, x), x)) { printf("INVALID: group axioms fail\n"); return 1; }
        el w; dec(enc(&x), &w); if (!eeq(w, x)) { printf("INVALID: index round trip\n"); return 1; }
    }
    printf("selftest: r^k = 1, associativity/identity/inverse on 20000 random triples, index round trip ok; %d distinct generators\n", d);
    int ok = 1; int eccs[2];
    for (int side = 0; side < 2; side++) {
        i64 ra, rb, lev[64]; double t1 = now();
        int ecc = bfs(side, &ra, &rb, lev);
        printf("from (e,%c): reached A %lld/%lld, B %lld/%lld within %d; eccentricity %d; levels", side ? 'B' : 'A',
               (long long)ra, (long long)N, (long long)rb, (long long)N, D, ecc);
        for (int L = 0; L <= D; L++) printf(" %lld", (long long)lev[L]);
        printf(" (%.1f s)\n", now() - t1);
        eccs[side] = ecc; if (ra != N || rb != N) ok = 0;
    }
    printf("%s d=%d D=%d N=%lld vertices=%lld diameter=%d (%.1f s, %d threads)\n", ok ? "VALID" : "INVALID", d, D, (long long)N,
           (long long)(2 * N), ok ? (eccs[0] > eccs[1] ? eccs[0] : eccs[1]) : -1, now() - t0, omp_get_max_threads());
    return ok ? 0 : 1;
}
