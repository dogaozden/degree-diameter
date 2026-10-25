/* hc_factor: low-memory diameter check of a Haar graph H(G,S), G = Q x Z_n with Q = SL(2,p) or PSL(2,p), p prime.
 * Written for research/theorems/HAAR_D8_10.md from the definitions, without looking at the other checkers' code paths
 * (it shares only the solution-file format). Different design from haarcheck_sl.c / haarcheck_psl.c: it enumerates Q
 * by brute force over all (a,b,c,d) in [0,p)^4 with ad - bc = 1 (for PSL keeping the lexicographically smaller of
 * X and -X), stores the sorted keys, and turns each generator s = (M, t) into two permutation tables of Q (X -> MX and
 * X -> M^-1 X), checked to be bijections. A vertex (X, z) of side A is joined to (MX, z + t) on side B (the convention
 * (g,A) ~ (s g, B)); from side B the step is (X, z) -> (M^-1 X, z - t).
 * By Corollary 2.3 of HAAR_D8_10.md the graph has diameter <= D iff BFS from (e,A) and from (e,B) each reach all 2|G|
 * vertices within D steps. Memory: 2 permutation tables of |Q| ints per generator, 6 bitsets of |G| bits.
 * Usage: hc_factor SOL.txt        Build: cc -O3 -o hc_factor hc_factor.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef long long ll;
static ll p, n, Q, N;
static int psl;
static ll *keys;                       /* sorted keys ((a*p+b)*p+c)*p+d of the canonical representatives */

static ll md(ll x) { x %= p; return x < 0 ? x + p : x; }
static ll rawkey(ll a, ll b, ll c, ll d) { return ((a * p + b) * p + c) * p + d; }
static ll canon(ll a, ll b, ll c, ll d) {
    ll k1 = rawkey(a, b, c, d);
    if (!psl) return k1;
    ll k2 = rawkey(md(-a), md(-b), md(-c), md(-d));
    return k1 < k2 ? k1 : k2;
}
static ll find(ll key) {               /* index of key in keys[], or -1 */
    ll lo = 0, hi = Q - 1;
    while (lo <= hi) { ll m = (lo + hi) / 2; if (keys[m] == key) return m; if (keys[m] < key) lo = m + 1; else hi = m - 1; }
    return -1;
}
static void unkey(ll k, ll *a, ll *b, ll *c, ll *d) { *d = k % p; k /= p; *c = k % p; k /= p; *b = k % p; *a = k / p; }

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: hc_factor SOL.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096], fam[16];
    int dg, D;
    if (!fgets(line, sizeof line, f) || sscanf(line, "%d %d %15s %lld n %lld", &dg, &D, fam, &p, &n) != 5) {
        fprintf(stderr, "bad header\n"); return 2; }
    if (!strcmp(fam, "psl")) psl = 1; else if (strcmp(fam, "sl")) { fprintf(stderr, "only sl/psl headers\n"); return 2; }
    for (ll t = 2; t * t <= p; t++) if (p % t == 0) { fprintf(stderr, "p not prime\n"); return 2; }
    if (psl && p == 2) { fprintf(stderr, "psl needs p odd\n"); return 2; }
    /* enumerate Q in increasing key order */
    ll expect = p * (p * p - 1) / (psl ? 2 : 1);
    keys = malloc(sizeof(ll) * expect); Q = 0;
    for (ll a = 0; a < p; a++) for (ll b = 0; b < p; b++) for (ll c = 0; c < p; c++) for (ll d = 0; d < p; d++) {
        if (md(a * d - b * c) != 1) continue;
        ll k = rawkey(a, b, c, d);
        if (canon(a, b, c, d) != k) continue;
        if (Q >= expect) { fprintf(stderr, "too many elements\n"); return 2; }
        keys[Q++] = k;
    }
    if (Q != expect) { fprintf(stderr, "|Q| = %lld, expected %lld\n", Q, expect); return 2; }
    N = Q * n;
    /* generators */
    ll M[64][4], T[64]; int k = 0;
    while (fgets(line, sizeof line, f) && k < 64) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z=");
        if (!m || !zz) continue;
        if (sscanf(m, "mat(%lld,%lld,%lld,%lld)", &M[k][0], &M[k][1], &M[k][2], &M[k][3]) != 4 || sscanf(zz, "z=%lld", &T[k]) != 1) return 2;
        for (int i = 0; i < 4; i++) if (M[k][i] < 0 || M[k][i] >= p) { fprintf(stderr, "entry out of range\n"); return 2; }
        if (T[k] < 0 || T[k] >= n || md(M[k][0] * M[k][3] - M[k][1] * M[k][2]) != 1) { fprintf(stderr, "bad element\n"); return 2; }
        k++;
    }
    if (k != dg) { fprintf(stderr, "read %d elements, expected %d\n", k, dg); return 2; }
    for (int i = 0; i < k; i++) for (int j = 0; j < i; j++)
        if (canon(M[i][0], M[i][1], M[i][2], M[i][3]) == canon(M[j][0], M[j][1], M[j][2], M[j][3]) && T[i] == T[j]) {
            fprintf(stderr, "repeated generator %d %d\n", j, i); return 2; }
    /* permutation tables */
    int32_t **fw = malloc(sizeof(int32_t *) * k), **bw = malloc(sizeof(int32_t *) * k);
    uint8_t *hit = malloc(Q);
    for (int i = 0; i < k; i++) {
        ll a = M[i][0], b = M[i][1], c = M[i][2], d = M[i][3];
        ll IA = d, IB = md(-b), IC = md(-c), ID = a;           /* inverse of a det-1 matrix */
        fw[i] = malloc(sizeof(int32_t) * Q); bw[i] = malloc(sizeof(int32_t) * Q);
        for (int dir = 0; dir < 2; dir++) {
            ll A_ = dir ? IA : a, B_ = dir ? IB : b, C_ = dir ? IC : c, D_ = dir ? ID : d;
            int32_t *tab = dir ? bw[i] : fw[i];
            memset(hit, 0, Q);
            for (ll x = 0; x < Q; x++) {
                ll xa, xb, xc, xd; unkey(keys[x], &xa, &xb, &xc, &xd);
                ll y = find(canon(md(A_ * xa + B_ * xc), md(A_ * xb + B_ * xd), md(C_ * xa + D_ * xc), md(C_ * xb + D_ * xd)));
                if (y < 0 || hit[y]) { fprintf(stderr, "left multiplication is not a bijection\n"); return 2; }
                hit[y] = 1; tab[x] = (int32_t)y;
            }
        }
    }
    ll e = find(canon(1, 0, 0, 1)) * n;                        /* identity (I, 0) */
    ll W = (N + 63) / 64;
    uint64_t *vis[2], *cur[2], *nxt[2];
    for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); cur[s] = calloc(W, 8); nxt[s] = calloc(W, 8);
        if (!vis[s] || !cur[s] || !nxt[s]) { fprintf(stderr, "out of memory\n"); return 2; } }
    int bad = 0;
    for (int start = 0; start < 2; start++) {
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(cur[s], 0, W * 8); }
        vis[start][e >> 6] |= 1ULL << (e & 63); cur[start][e >> 6] |= 1ULL << (e & 63);
        ll reached[2] = {0, 0}; reached[start] = 1;
        int side = start, ecc = 0;
        for (int step = 1; step <= D; step++) {
            int ns = side ^ 1; ll add = 0;
            memset(nxt[ns], 0, W * 8);
            for (ll w = 0; w < W; w++) {
                uint64_t bits = cur[side][w];
                while (bits) {
                    int bt = __builtin_ctzll(bits); bits &= bits - 1;
                    ll g = w * 64 + bt, x = g / n, z = g % n;
                    for (int i = 0; i < k; i++) {
                        ll h = side == 0 ? (ll)fw[i][x] * n + (z + T[i]) % n : (ll)bw[i][x] * n + (z - T[i] + n) % n;
                        uint64_t m1 = 1ULL << (h & 63);
                        if (!(vis[ns][h >> 6] & m1)) { vis[ns][h >> 6] |= m1; nxt[ns][h >> 6] |= m1; add++; }
                    }
                }
            }
            memset(cur[side], 0, W * 8);
            uint64_t *t = cur[ns]; cur[ns] = nxt[ns]; nxt[ns] = t;
            reached[ns] += add; if (add) ecc = step; side = ns;
        }
        printf("from (e,%c): reached A %lld/%lld, B %lld/%lld within %d steps, eccentricity %d\n",
               start ? 'B' : 'A', reached[0], N, reached[1], N, D, ecc);
        if (reached[0] != N || reached[1] != N) bad = 1;
    }
    printf("%s d=%d D=%d group=%s %lld x Z_%lld |G|=%lld vertices=%lld (hc_factor)\n", bad ? "INVALID" : "VALID", dg, D,
           fam, p, n, N, 2 * N);
    return bad;
}
