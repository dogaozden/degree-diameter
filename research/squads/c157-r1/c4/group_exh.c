/* Exhaustive search over D in a finite group G (order K <= 64, given by a multiplication table) with
   identity e in D, |D| = s, such that D D^-1 and D^-1 D both contain G \ {e}.
   Input file: "K e" then K*K ints mul[g][h] (row-major).  Usage: ./group_exh FILE s [maxprint]
   WLOG e in D: left-translating D by an element of D keeps both conditions. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int K, e, s, maxprint = 3;
static int *mul, *inv;
static int D[16];
static long long found = 0, leaves = 0;
static uint64_t FULL;

#define MUL(a, b) mul[(a) * K + (b)]

static void rec(int depth, int last, uint64_t m1, uint64_t m2) {
    if (depth == s) {
        leaves++;
        if (m1 == FULL && m2 == FULL) {
            found++;
            if (found <= maxprint) {
                printf("sol:");
                for (int i = 0; i < s; i++) printf(" %d", D[i]);
                printf("\n");
            }
        }
        return;
    }
    for (int x = last + 1; x < K; x++) {
        if (x == e) continue;
        uint64_t a1 = m1, a2 = m2;
        for (int i = 0; i < depth; i++) {
            int d = D[i];
            a1 |= 1ULL << MUL(x, inv[d]);
            a1 |= 1ULL << MUL(d, inv[x]);
            a2 |= 1ULL << MUL(inv[d], x);
            a2 |= 1ULL << MUL(inv[x], d);
        }
        D[depth] = x;
        rec(depth + 1, x, a1, a2);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s FILE s [maxprint]\n", argv[0]); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 2; }
    if (fscanf(f, "%d %d", &K, &e) != 2) return 2;
    mul = malloc(sizeof(int) * K * K);
    inv = malloc(sizeof(int) * K);
    for (int i = 0; i < K * K; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 2;
    fclose(f);
    s = atoi(argv[2]);
    if (argc > 3) maxprint = atoi(argv[3]);
    for (int g = 0; g < K; g++) {
        for (int h = 0; h < K; h++) if (MUL(g, h) == e) inv[g] = h;
    }
    FULL = 0;
    for (int g = 0; g < K; g++) if (g != e) FULL |= 1ULL << g;
    D[0] = e;
    /* masks for the single element e: none (quotients of distinct pairs only) */
    rec(1, -1, 0, 0);
    printf("K=%d s=%d solutions=%lld (leaves %lld)\n", K, s, found, leaves);
    return 0;
}
