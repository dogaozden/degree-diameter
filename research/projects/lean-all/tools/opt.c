// opt: degree-preserving edge swaps to reach same-side distance <= 6 in a bipartite graph.
// usage: opt IN.edges nB nA OUT.edges seed maxiters
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MAXD 8
static int nB, nA; static int degB[20000], degA[20000], nbB[20000][MAXD], nbA[20000][MAXD];
static uint64_t *cur, *oth, *nx;
static uint64_t rs = 88172645463325252ULL; static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void layer(int nX, int (*nbX)[MAXD], int *degX, uint64_t *prev, uint64_t *out, int W) {
  for (int x = 0; x < nX; x++) { uint64_t *o = out + (size_t)x * W; memset(o, 0, 8 * W);
    for (int t = 0; t < degX[x]; t++) { uint64_t *p = prev + (size_t)nbX[x][t] * W; for (int w = 0; w < W; w++) o[w] |= p[w]; } }
}
// far pairs of one side; if lst, store up to cap ordered far pairs
static long side(int nS, int nO, int (*nbS)[MAXD], int *degS, int (*nbO)[MAXD], int *degO, int *lst, int cap, int *nl) {
  int W = (nS + 63) / 64; memset(cur, 0, (size_t)nS * W * 8);
  for (int i = 0; i < nS; i++) cur[(size_t)i * W + i / 64] |= 1ULL << (i % 64);
  for (int r = 0; r < 3; r++) { layer(nO, nbO, degO, cur, oth, W); layer(nS, nbS, degS, oth, nx, W);
    for (size_t k = 0; k < (size_t)nS * W; k++) cur[k] |= nx[k]; }
  long miss = 0;
  for (int i = 0; i < nS; i++) { long c = 0; for (int w = 0; w < W; w++) c += __builtin_popcountll(cur[(size_t)i * W + w]); miss += nS - c;
    if (lst && nS - c > 0) for (int j = 0; j < nS && *nl < cap; j++) if (!((cur[(size_t)i * W + j / 64] >> (j % 64)) & 1)) { lst[2 * *nl] = i; lst[2 * *nl + 1] = j; (*nl)++; } }
  return miss / 2;
}
static int lstB[200000], lstA[200000], nlB, nlA;
static long evalall(int wantlist, long *fb, long *fa) {
  int d1 = 0, d2 = 0;
  if (wantlist) nlB = nlA = 0;
  *fb = side(nB, nA, nbB, degB, nbA, degA, wantlist ? lstB : NULL, 100000, wantlist ? &nlB : &d1);
  *fa = side(nA, nB, nbA, degA, nbB, degB, wantlist ? lstA : NULL, 100000, wantlist ? &nlA : &d2);
  return *fb + *fa;
}
static int hasB(int b, int a) { for (int t = 0; t < degB[b]; t++) if (nbB[b][t] == a) return 1; return 0; }
static void repl(int *arr, int d, int from, int to) { for (int t = 0; t < d; t++) if (arr[t] == from) { arr[t] = to; return; } fprintf(stderr, "repl fail\n"); exit(1); }
// swap: remove (q,p'),(q',p); add (q,p),(q',p')  [q,q' in B; p,p' in A]
static int doswap(int q, int pp, int qq, int p) {
  if (q == qq || p == pp) return 0;
  if (!hasB(q, pp) || !hasB(qq, p) || hasB(q, p) || hasB(qq, pp)) return 0;
  repl(nbB[q], degB[q], pp, p); repl(nbA[p], degA[p], qq, q); repl(nbB[qq], degB[qq], p, pp); repl(nbA[pp], degA[pp], q, qq);
  return 1;
}
static void undo(int q, int pp, int qq, int p) { // inverse of doswap(q,pp,qq,p): now (q,p),(qq,pp) present
  repl(nbB[q], degB[q], p, pp); repl(nbA[pp], degA[pp], qq, q); repl(nbB[qq], degB[qq], pp, p); repl(nbA[p], degA[p], q, qq);
}
// BFS distances from a vertex (side s: 0 = B, 1 = A); dist arrays
static int dB[20000], dA[20000], qu[40000];
static void bfs(int s, int v) {
  for (int i = 0; i < nB; i++) dB[i] = 99; for (int i = 0; i < nA; i++) dA[i] = 99;
  int h = 0, t = 0; if (s == 0) dB[v] = 0; else dA[v] = 0; qu[t++] = s ? (v + 100000) : v;
  while (h < t) { int x = qu[h++];
    if (x < 100000) { for (int k = 0; k < degB[x]; k++) { int a = nbB[x][k]; if (dA[a] == 99) { dA[a] = dB[x] + 1; qu[t++] = a + 100000; } } }
    else { x -= 100000; for (int k = 0; k < degA[x]; k++) { int b = nbA[x][k]; if (dB[b] == 99) { dB[b] = dA[x] + 1; qu[t++] = b; } } } }
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); nB = atoi(argv[2]); nA = atoi(argv[3]); rs ^= (uint64_t)atol(argv[5]) * 0x9E3779B97F4A7C15ULL; long maxit = atol(argv[6]);
  int b, a; while (fscanf(f, "%d %d", &b, &a) == 2) { nbB[b][degB[b]++] = a; nbA[a][degA[a]++] = b; } fclose(f);
  int nmax = nB > nA ? nB : nA; int W = (nmax + 63) / 64;
  cur = malloc((size_t)nmax * W * 8); oth = malloc((size_t)nmax * W * 8); nx = malloc((size_t)nmax * W * 8);
  long fb, fa, best = evalall(1, &fb, &fa); printf("start farB %ld farA %ld\n", fb, fa); fflush(stdout);
  long it = 0, acc = 0;
  while (best > 0 && it < maxit) {
    it++;
    // pick a far pair
    int side_ = (nlA == 0) ? 0 : (nlB == 0) ? 1 : (int)(rnd() % 2);
    int x, y; if (side_ == 0) { int k = rnd() % nlB; x = lstB[2 * k]; y = lstB[2 * k + 1]; } else { int k = rnd() % nlA; x = lstA[2 * k]; y = lstA[2 * k + 1]; }
    int q, pp, qq, p;
    if (side_ == 0) { // x,y in B: p in N(x) (A), q in B with d(q,y)<=4
      bfs(0, y); p = nbB[x][rnd() % degB[x]];
      int tries = 0; do { q = rnd() % nB; tries++; } while ((dB[q] > 4 || hasB(q, p)) && tries < 100000);
      if (tries >= 100000) continue;
      qq = nbA[p][rnd() % degA[p]]; if (qq == x) continue; pp = nbB[q][rnd() % degB[q]];
    } else { // x,y in A: q in N(x) (B), p in A with d(p,y)<=4
      bfs(1, y); q = nbA[x][rnd() % degA[x]];
      int tries = 0; do { p = rnd() % nA; tries++; } while ((dA[p] > 4 || hasB(q, p)) && tries < 100000);
      if (tries >= 100000) continue;
      pp = nbB[q][rnd() % degB[q]]; if (pp == x) continue; qq = nbA[p][rnd() % degA[p]];
    }
    if (!doswap(q, pp, qq, p)) continue;
    long nb_, na_, v = evalall(0, &nb_, &na_);
    if (v < best || (v == best && rnd() % 4 == 0)) { best = v; acc++; evalall(1, &fb, &fa);
      printf("it %ld acc %ld farB %ld farA %ld\n", it, acc, fb, fa); fflush(stdout);
      FILE *o = fopen(argv[4], "w"); for (int i = 0; i < nB; i++) for (int t = 0; t < degB[i]; t++) fprintf(o, "%d %d\n", i, nbB[i][t]); fclose(o);
    } else undo(q, pp, qq, p);
  }
  if (it % 50 == 0) {}
  printf("done it %ld best %ld\n", it, best);
  return 0;
}
