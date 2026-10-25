/* Exhaustive search for D in Z_n, |D| = s, with D - D covering Z_n \ {0}.
   WLOG 0,1 in D (translate so that some difference 1 = d1 - d2 has d2 = 0).
   Usage: ./cyc_exh n s [maxprint]   prints the number of solutions and the first few. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int n, s, maxprint = 3;
static int D[32];
static long long found = 0, leaves = 0;
static uint64_t FULL;

static void rec(int depth, int last, uint64_t mask) {
    if (depth == s) {
        leaves++;
        if (mask == FULL) {
            found++;
            if (found <= maxprint) {
                printf("sol:");
                for (int i = 0; i < s; i++) printf(" %d", D[i]);
                printf("\n");
            }
        }
        return;
    }
    for (int x = last + 1; x < n; x++) {
        uint64_t m = mask;
        for (int i = 0; i < depth; i++) {
            int t = (x - D[i] + n) % n;
            m |= (1ULL << t) | (1ULL << ((n - t) % n));
        }
        D[depth] = x;
        rec(depth + 1, x, m);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s n s [maxprint]\n", argv[0]); return 2; }
    n = atoi(argv[1]);
    s = atoi(argv[2]);
    if (argc > 3) maxprint = atoi(argv[3]);
    if (n > 63 || s < 2 || s > 16) { fprintf(stderr, "bad n/s\n"); return 2; }
    FULL = 0;
    for (int t = 1; t < n; t++) FULL |= 1ULL << t;
    D[0] = 0; D[1] = 1;
    uint64_t mask = (1ULL << 1) | (1ULL << (n - 1));
    rec(2, 1, mask);
    printf("n=%d s=%d solutions=%lld (leaves %lld)\n", n, s, found, leaves);
    return 0;
}
