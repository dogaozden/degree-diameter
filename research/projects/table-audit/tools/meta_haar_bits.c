/* meta_haar_bits.c (table-audit-2): a second independent, low-memory check of a Haar graph of a metacyclic group, for
   graphs too large for build_haar2.py.  Written separately from meta_haar_check.c (different element indexing, bitset
   level-by-level BFS instead of a queue, inverse neighbours computed as (b - s_a) r^(-s_j)).
   G = Z_m x|_r Z_k: (a, j)(b, l) = (a + r^j b mod m, j + l mod k).  Haar graph: (g, A) ~ (s g, B), s in S.
   Right multiplication by G is transitive on each side, so BFS from (e, A) and from (e, B) gives the exact diameter.
   Element (a, j) has index j*m + a.  Memory: 4 bitsets over G (about N/2 bytes).
   Input: a haar_gen3 solution file ("d D meta m k r n 1 N ..." then d lines with "meta(a=A,j=J)").
   Usage: meta_haar_bits SOL      prints ecc from each side and "RESULT VALID d D n" iff the diameter is <= D. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static long m, k; static long *rpow;   /* rpow[j] = r^j mod m, j = 0..k */
static inline void setb(uint64_t *b, long i) { b[i >> 6] |= 1ULL << (i & 63); }
static inline int getb(const uint64_t *b, long i) { return (b[i >> 6] >> (i & 63)) & 1; }

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    int d, D; long r, ncyc; char w[64];
    if (fscanf(f, "%d %d %63s %ld %ld %ld %*s %ld", &d, &D, w, &m, &k, &r, &ncyc) != 7 || strcmp(w, "meta") || ncyc != 1) { printf("RESULT INVALID header\n"); return 1; }
    long sa[64], sj[64]; int ns = 0; char line[512];
    while (fgets(line, sizeof line, f)) { char *p = strstr(line, "meta(a="); long a, j; if (p && sscanf(p, "meta(a=%ld,j=%ld)", &a, &j) == 2) { sa[ns] = ((a % m) + m) % m; sj[ns] = ((j % k) + k) % k; ns++; } }
    if (ns != d) { printf("RESULT INVALID %d elements read, %d expected\n", ns, d); return 1; }
    rpow = malloc(sizeof(long) * (k + 1)); rpow[0] = 1 % m;
    for (long j = 1; j <= k; j++) rpow[j] = (long)((__int128)rpow[j - 1] * r % m);
    if (rpow[k] != 1 % m) { printf("RESULT INVALID r^k != 1\n"); return 1; }
    for (int x = 0; x < d; x++) for (int y = 0; y < x; y++) if (sa[x] == sa[y] && sj[x] == sj[y]) { printf("RESULT INVALID repeated generator\n"); return 1; }
    long N = m * k, W = (N + 63) / 64;
    uint64_t *vis[2], *cur = calloc(W, 8), *nxt = calloc(W, 8); vis[0] = calloc(W, 8); vis[1] = calloc(W, 8);
    int diam = 0;
    for (int start = 0; start < 2; start++) {
        memset(vis[0], 0, 8 * W); memset(vis[1], 0, 8 * W); memset(cur, 0, 8 * W);
        setb(cur, 0); setb(vis[start], 0); int side = start, lev = 0; long seen = 1;
        for (;;) {
            memset(nxt, 0, 8 * W); long added = 0; int to = 1 - side;
            for (long wi = 0; wi < W; wi++) { uint64_t bits = cur[wi];
                while (bits) { long g = wi * 64 + __builtin_ctzll(bits); bits &= bits - 1;
                    long j = g / m, a = g - j * m;
                    for (int x = 0; x < d; x++) { long na, nj;
                        if (side == 0) { na = (long)((sa[x] + (__int128)rpow[sj[x]] * a) % m); nj = (sj[x] + j) % k; }        /* s g */
                        else { long ij = (k - sj[x]) % k; na = (long)((__int128)rpow[ij] * (((a - sa[x]) % m + m) % m) % m); nj = (j - sj[x] + k) % k; } /* s^-1 h */
                        long h = nj * m + na;
                        if (!getb(vis[to], h) && !getb(nxt, h)) { setb(nxt, h); added++; }
                    } } }
            if (!added) break;
            lev++; for (long wi = 0; wi < W; wi++) vis[to][wi] |= nxt[wi];
            seen += added; uint64_t *t = cur; cur = nxt; nxt = t; side = to;
        }
        if (seen != 2 * N) { printf("RESULT INVALID from side %c: %ld of %ld vertices reached\n", start ? 'B' : 'A', seen, 2 * N); return 1; }
        printf("ecc(e,%c) = %d\n", start ? 'B' : 'A', lev); if (lev > diam) diam = lev;
    }
    printf("n=%ld degree=%d diameter=%d group=Z%ld x|_%ld Z%ld (bitset check)\n", 2 * N, d, diam, m, r, k);
    if (diam <= D) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, 2 * N); else printf("RESULT INVALID\n");
    return 0;
}
