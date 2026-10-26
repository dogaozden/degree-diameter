/* meta_haar_pull.c (table-audit-2): a third check of a Haar graph of a metacyclic group, low memory, for the largest
   cells (up to 4.1e9 vertices), where meta_haar_check.c (9 bytes per vertex) does not fit.  Different method from
   meta_haar_bits.c: "pull" BFS — a vertex not yet reached on the side being filled is added when one of its own
   neighbours lies in the previous frontier.  Element (a, j) of G = Z_m x|_r Z_k has index a*k + j here.
   Neighbours of (g, B) on side A are s^-1 g; of (g, A) on side B are s g ... so pulling into side B tests s^-1 g in
   the A-frontier, and pulling into side A tests s g in the B-frontier.  Arithmetic in unsigned 64-bit (m < 2^31).
   Usage: meta_haar_pull SOL   prints ecc from (e,A) and (e,B) and "RESULT VALID d D n" iff the diameter is <= D. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    int d, D; uint64_t m, k, r; long ncyc; char w[64];
    if (fscanf(f, "%d %d %63s %lu %lu %lu %*s %ld", &d, &D, w, &m, &k, &r, &ncyc) != 7 || strcmp(w, "meta") || ncyc != 1 || m >= (1ULL << 31)) { printf("RESULT INVALID header\n"); return 1; }
    uint64_t sa[64], sj[64]; int ns = 0; char line[512];
    while (fgets(line, sizeof line, f)) { char *p = strstr(line, "meta(a="); long a, j; if (p && sscanf(p, "meta(a=%ld,j=%ld)", &a, &j) == 2) { sa[ns] = ((a % (long)m) + m) % m; sj[ns] = ((j % (long)k) + k) % k; ns++; } }
    if (ns != d) { printf("RESULT INVALID %d elements, expected %d\n", ns, d); return 1; }
    uint64_t *rp = malloc(8 * (k + 1)); rp[0] = 1 % m; for (uint64_t j = 1; j <= k; j++) rp[j] = rp[j - 1] * r % m;
    if (rp[k] != 1 % m) { printf("RESULT INVALID r^k\n"); return 1; }
    for (int x = 0; x < d; x++) for (int y = 0; y < x; y++) if (sa[x] == sa[y] && sj[x] == sj[y]) { printf("RESULT INVALID repeated\n"); return 1; }
    /* s^-1 = (-r^(k-sj) sa, k - sj) */
    uint64_t ia[64], ij[64]; for (int x = 0; x < d; x++) { ij[x] = (k - sj[x]) % k; ia[x] = (m - rp[ij[x]] * sa[x] % m) % m; }
    uint64_t N = m * k, W = (N + 63) / 64;
    uint64_t *vis[2] = {calloc(W, 8), calloc(W, 8)}, *fr = calloc(W, 8), *nf = calloc(W, 8);
    int diam = 0;
    for (int start = 0; start < 2; start++) {
        memset(vis[0], 0, 8 * W); memset(vis[1], 0, 8 * W); memset(fr, 0, 8 * W);
        vis[start][0] |= 1; fr[0] |= 1; int side = start, lev = 0; uint64_t seen = 1;
        for (;;) {
            int to = 1 - side; uint64_t added = 0; memset(nf, 0, 8 * W);
            for (uint64_t g = 0; g < N; g++) {
                if ((vis[to][g >> 6] >> (g & 63)) & 1) continue;
                uint64_t a = g / k, j = g % k;
                for (int x = 0; x < d; x++) {
                    uint64_t na, nj;   /* neighbour of (g, to) on side `side`: to == B -> s^-1 g ; to == A -> s g */
                    if (to == 1) { na = (ia[x] + rp[ij[x]] * a) % m; nj = (ij[x] + j) % k; }
                    else { na = (sa[x] + rp[sj[x]] * a) % m; nj = (sj[x] + j) % k; }
                    uint64_t h = na * k + nj;
                    if ((fr[h >> 6] >> (h & 63)) & 1) { nf[g >> 6] |= 1ULL << (g & 63); added++; break; }
                }
            }
            if (!added) break;
            lev++; seen += added; for (uint64_t i = 0; i < W; i++) vis[to][i] |= nf[i];
            uint64_t *t = fr; fr = nf; nf = t; side = to;
        }
        if (seen != 2 * N) { printf("RESULT INVALID side %c: %lu of %lu reached\n", start ? 'B' : 'A', seen, 2 * N); return 1; }
        printf("ecc(e,%c) = %d\n", start ? 'B' : 'A', lev); if (lev > diam) diam = lev;
    }
    printf("n=%lu degree=%d diameter=%d group=Z%lu x|_%lu Z%lu (pull check)\n", 2 * N, d, diam, m, r, k);
    if (diam <= D) printf("RESULT VALID d=%d D=%d n=%lu\n", d, D, 2 * N); else printf("RESULT INVALID\n");
    return 0;
}
