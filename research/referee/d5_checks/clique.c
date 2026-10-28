/* Maximum clique (simple bitset branch and bound with greedy colouring bound, Tomita-style) on a graph given as
   "n" then an n x n 0/1 matrix rows as strings. Prints the clique number and one maximum clique. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define W 4
typedef struct { uint64_t w[W]; } bs;
int n; bs adj[256]; int best = 0, cur[256], bestc[256]; long nodes = 0;
static int pc(const bs *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a->w[i]); return c; }
static void expand(bs P, int depth) {
  nodes++;
  int order[256], colour[256], m = 0, k = 0;
  bs U = P;
  while (pc(&U)) {      /* greedy colouring of P: colour classes are independent sets */
    k++; bs Q = U;
    while (pc(&Q)) {
      int v = -1; for (int i = 0; i < W && v < 0; i++) if (Q.w[i]) v = i * 64 + __builtin_ctzll(Q.w[i]);
      U.w[v / 64] &= ~(1ULL << (v % 64)); Q.w[v / 64] &= ~(1ULL << (v % 64));
      for (int i = 0; i < W; i++) Q.w[i] &= ~adj[v].w[i];
      order[m] = v; colour[m] = k; m++;
    }
  }
  for (int i = m - 1; i >= 0; i--) {
    if (depth + colour[i] <= best) return;
    int v = order[i]; cur[depth] = v;
    bs NP; for (int t = 0; t < W; t++) NP.w[t] = P.w[t] & adj[v].w[t];
    if (pc(&NP) == 0) { if (depth + 1 > best) { best = depth + 1; memcpy(bestc, cur, sizeof(int) * best); } }
    else expand(NP, depth + 1);
    P.w[v / 64] &= ~(1ULL << (v % 64));
  }
}
int main(void) {
  if (scanf("%d", &n) != 1 || n > 64 * W) return 1;
  char row[300];
  for (int i = 0; i < n; i++) { scanf("%s", row); for (int j = 0; j < n; j++) if (row[j] == '1') adj[i].w[j / 64] |= 1ULL << (j % 64); }
  bs P; memset(&P, 0, sizeof P); for (int i = 0; i < n; i++) P.w[i / 64] |= 1ULL << (i % 64);
  expand(P, 0);
  printf("clique number %d (nodes %ld):", best, nodes); for (int i = 0; i < best; i++) printf(" %d", bestc[i]); printf("\n");
  return 0;
}
