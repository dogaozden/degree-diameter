/* metacheck (job raise-d11, 2026-11-02): independent diameter check of a Haar graph H(G,S) for metacyclic groups
 *     G = Z_q x|_r Z_k,  (a,j)(b,l) = (a + r^j b mod q, j + l mod k),  r^k = 1 mod q.
 * Reads a haar_gen3 / haar_meta solution file: header "d D meta q k r n 1 N NG", then d lines "... meta(a=A,j=J) z=0".
 * Written from the definitions only (shares no code with haar_meta.c or haar_gen3.c): element (a,j) has index j*q + a
 * (haar_meta uses r^-j a as the bit); neighbours are computed by the group law with 64-bit arithmetic.
 * Graph: vertices (g,A), (g,B), edges (g,A) ~ (s g, B).  Right multiplication by G is transitive on each side, so BFS
 * from (e,A) and from (e,B), each reaching every vertex within D steps, is exactly diameter <= D.
 * Self-tests: r^k = 1 mod q, generators distinct, associativity and inverses on random triples.
 * BFS: level-synchronous on two bitsets per side (visited, frontier), pull over S or S^-1 (4 bitsets of N bits).
 * Usage: metacheck SOL [A|B]   (A or B: only that BFS)   Build: cc -O3 -fopenmp -o metacheck metacheck.c
 * Output: eccentricities, unreached counts, and a last line VALID / INVALID (or HALF-VALID / HALF-INVALID with A|B). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef long long ll; typedef uint64_t u64;
static ll q, k, r, N; static ll *rp;           /* rp[j] = r^j mod q */
static ll mul_a(ll a, ll j, ll b) { return (a + (ll)((__int128)rp[j] * b % q)) % q; }
typedef struct { ll a, j; } el;
static el gmul(el x, el y) { el z = {mul_a(x.a, x.j, y.a), (x.j + y.j) % k}; return z; }
static el ginv(el x) {           /* (a,j)^-1 = (-r^-j a, -j); r^-j = r^(k-j) */
    ll jj = (k - x.j) % k; el z = {(q - (ll)((__int128)rp[jj] * x.a % q)) % q, jj}; return z; }
static ll idx(el x) { return x.j * q + x.a; }
static el dec(ll g) { el x = {g % q, g / q}; return x; }
static inline int getb(const u64 *b, ll i) { return (b[i >> 6] >> (i & 63)) & 1; }
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: metacheck SOL [A|B]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    int d, D; ll NN;
    if (sscanf(line, "%d %d meta %lld %lld %lld n 1 N %lld", &d, &D, &q, &k, &r, &NN) != 6) { fprintf(stderr, "header: %s", line); return 2; }
    N = q * k; if (N != NN) { fprintf(stderr, "N mismatch %lld vs %lld\n", N, NN); return 2; }
    rp = malloc(sizeof(ll) * (k + 1)); rp[0] = 1 % q;
    for (ll j = 1; j <= k; j++) rp[j] = (ll)((__int128)rp[j - 1] * r % q);
    if (rp[k] != 1 % q) { fprintf(stderr, "r^k != 1 mod q\n"); return 2; }
    el S[256], SI[256]; int ns = 0;
    while (fgets(line, sizeof line, f) && ns < d) {
        char *m = strstr(line, "meta("); if (!m) continue;
        ll a, j; if (sscanf(m, "meta(a=%lld,j=%lld)", &a, &j) != 2 || a < 0 || a >= q || j < 0 || j >= k) { fprintf(stderr, "bad line %s", line); return 2; }
        S[ns].a = a; S[ns].j = j; ns++;
    }
    if (ns != d) { fprintf(stderr, "found %d generators, header says %d\n", ns, d); return 2; }
    for (int i = 0; i < d; i++) for (int j = 0; j < i; j++) if (idx(S[i]) == idx(S[j])) { fprintf(stderr, "repeated generator\n"); return 2; }
    u64 st = 12345;
    for (int t = 0; t < 100000; t++) {
        el x, y, z; st = st * 6364136223846793005ULL + 1442695040888963407ULL; x = dec((ll)((st >> 11) % (u64)N));
        st = st * 6364136223846793005ULL + 1442695040888963407ULL; y = dec((ll)((st >> 11) % (u64)N));
        st = st * 6364136223846793005ULL + 1442695040888963407ULL; z = dec((ll)((st >> 11) % (u64)N));
        if (idx(gmul(gmul(x, y), z)) != idx(gmul(x, gmul(y, z))) || idx(gmul(x, ginv(x))) != 0 || idx(dec(idx(x))) != idx(x)) { fprintf(stderr, "group self-test failed\n"); return 2; }
    }
    for (int i = 0; i < d; i++) SI[i] = ginv(S[i]);
    printf("group meta %lld %lld %lld, N=%lld, vertices=%lld, d=%d, D=%d\n", q, k, r, N, 2 * N, d, D);
    ll W = (N + 63) / 64;
    u64 *vis[2], *fr[2]; for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); fr[s] = calloc(W, 8); if (!vis[s] || !fr[s]) { fprintf(stderr, "out of memory\n"); return 2; } }
    int ok = 1, which = argc > 2 ? argv[2][0] : 0;
    for (int start = 0; start < 2; start++) {
        if ((which == 'A' && start == 1) || (which == 'B' && start == 0)) continue;
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(fr[s], 0, W * 8); }
        vis[start][0] |= 1; fr[start][0] |= 1;            /* identity has index 0 */
        ll cnt[2] = {0, 0}; cnt[start] = 1; int ecc = 0, cur = start;
        for (int lev = 1; lev <= D + 1; lev++) {
            int nxt = cur ^ 1;
            /* new vertices on side nxt: from (g,A) the neighbours are (s g, B); from (h,B) they are (s^-1 h, A).
             * pull: y on side nxt is new iff some predecessor x with x in fr[cur] (x = s^-1 y if nxt = B, x = s y if nxt = A) */
            u64 *nf = calloc(W, 8); ll added = 0;
            #pragma omp parallel for schedule(dynamic, 4096) reduction(+:added)
            for (ll w = 0; w < W; w++) {
                u64 vw = vis[nxt][w], outw = 0;
                if (vw == ~0ULL) continue;
                for (int b = 0; b < 64; b++) {
                    ll y = w * 64 + b; if (y >= N || ((vw >> b) & 1)) continue;
                    el ye = dec(y);
                    for (int i = 0; i < d; i++) {
                        el x = gmul(nxt == 1 ? SI[i] : S[i], ye);
                        if (getb(fr[cur], idx(x))) { outw |= 1ULL << b; break; }
                    }
                }
                nf[w] = outw; added += __builtin_popcountll(outw);
            }
            if (added == 0) { free(nf); break; }
            for (ll w = 0; w < W; w++) vis[nxt][w] |= nf[w];
            free(fr[nxt]); fr[nxt] = nf; memset(fr[cur], 0, W * 8);
            cnt[nxt] += added; ecc = lev; cur = nxt;
            printf("  from (e,%c): level %d reached %lld new (side %c total %lld)\n", start ? 'B' : 'A', lev, added, nxt ? 'B' : 'A', cnt[nxt]);
            fflush(stdout);
        }
        ll un = (N - cnt[0]) + (N - cnt[1]);
        printf("BFS from (e,%c): eccentricity %d, unreached %lld\n", start ? 'B' : 'A', ecc, un);
        if (un || ecc > D) ok = 0;
    }
    if (which == 'A' || which == 'B') printf("%s from (e,%c) d=%d D=%d group=meta %lld %lld %lld N=%lld vertices=%lld\n", ok ? "HALF-VALID" : "HALF-INVALID", which, d, D, q, k, r, N, 2 * N);
    else printf("%s d=%d D=%d group=meta %lld %lld %lld N=%lld vertices=%lld\n", ok ? "VALID" : "INVALID", d, D, q, k, r, N, 2 * N);
    return ok ? 0 : 1;
}
