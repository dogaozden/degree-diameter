/* c04: generic group search. Input: permutation generators of G (file: "d g" then g lines of d ints).
 * Builds the full multiplication table (|G| <= 8192), then
 *  mode h: Haar graph H(G,{e,x,y}) (bipartite cubic, 2|G| vertices); cost = #vertices not within D of
 *          (e,A) plus #not within D of (e,B). Random restarts + plateau walk over (x,y).
 *  mode c: cubic Cayley graph Cay(G,{a,b,c}), a,b,c distinct involutions, bipartite (BFS parity check);
 *          cost = #vertices with dist > D from e. Vertex-transitive, so BFS from e suffices.
 * Usage: cay MODE GROUPFILE SECONDS SEED PREFIX [D]
 * Writes PREFIX.sol (cost 0 only) and PREFIX.edges (edge list "u v" with first line n) for cost 0 graphs.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#define MAXN 8192
#define HS 65536
static int d, ng, N, D = 14;
static uint16_t *el;
static uint32_t htab[HS];
static uint16_t *mul;
static int *inv;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t hp(const uint16_t *p) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < d; i++) { h ^= p[i]; h *= 1099511628211ULL; } return h; }
static int lookup_or_add(const uint16_t *p, int *added) {
  uint64_t h = hp(p) & (HS - 1);
  for (;;) {
    uint32_t e = htab[h];
    if (!e) {
      if (N >= MAXN) { fprintf(stderr, "group too big\n"); exit(2); }
      memcpy(el + (size_t)N * d, p, sizeof(uint16_t) * d);
      htab[h] = N + 1; if (added) *added = 1; return N++;
    }
    if (memcmp(el + (size_t)(e - 1) * d, p, sizeof(uint16_t) * d) == 0) { if (added) *added = 0; return e - 1; }
    h = (h + 1) & (HS - 1);
  }
}
static int lookup(const uint16_t *p) { int a; return lookup_or_add(p, &a); }
static uint16_t *gens;
static void closure(void) {
  uint16_t *q = malloc(sizeof(uint16_t) * d);
  for (int i = 0; i < d; i++) q[i] = i;
  lookup_or_add(q, NULL);
  for (int g = 0; g < N; g++)
    for (int t = 0; t < ng; t++) {
      for (int i = 0; i < d; i++) q[i] = el[(size_t)g * d + gens[t * d + i]];
      lookup_or_add(q, NULL);
    }
  free(q);
}
static void build_mul(void) {
  uint16_t *q = malloc(sizeof(uint16_t) * d);
  for (int g = 0; g < N; g++)
    for (int h = 0; h < N; h++) {
      for (int i = 0; i < d; i++) q[i] = el[(size_t)g * d + el[(size_t)h * d + i]];
      mul[(size_t)g * N + h] = lookup(q);
    }
  free(q);
  for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (mul[(size_t)g * N + h] == 0) inv[g] = h;
}
static int *dist, *qu;
/* Haar: cost = unreached within D from source (A: v<N, B: v>=N) */
static int haar_cost_src(int src, int x, int ix, int y, int iy) {
  int V = 2 * N;
  for (int i = 0; i < V; i++) dist[i] = -1;
  int h = 0, t = 0; qu[t++] = src; dist[src] = 0; int reached = 1;
  while (h < t) {
    int v = qu[h++]; int dv = dist[v];
    if (dv >= D) continue;
    int nb[3];
    if (v < N) { nb[0] = N + v; nb[1] = N + mul[(size_t)v * N + x]; nb[2] = N + mul[(size_t)v * N + y]; }
    else { int k = v - N; nb[0] = k; nb[1] = mul[(size_t)k * N + ix]; nb[2] = mul[(size_t)k * N + iy]; }
    for (int j = 0; j < 3; j++) if (dist[nb[j]] < 0) { dist[nb[j]] = dv + 1; qu[t++] = nb[j]; reached++; }
  }
  return V / 2 - (reached - 0) + 0 ? (N - (reached - 0) + 0) : 0;
}
static int haar_cost(int x, int y) {
  int ix = inv[x], iy = inv[y];
  int V = 2 * N;
  int ca, cb;
  /* count vertices on each side not reached within D; cost = sum over both sources */
  {
    for (int i = 0; i < V; i++) dist[i] = -1;
    int h = 0, t = 0; qu[t++] = 0; dist[0] = 0;
    while (h < t) { int v = qu[h++]; int dv = dist[v]; if (dv >= D) continue;
      int nb[3];
      if (v < N) { nb[0] = N + v; nb[1] = N + mul[(size_t)v * N + x]; nb[2] = N + mul[(size_t)v * N + y]; }
      else { int k = v - N; nb[0] = k; nb[1] = mul[(size_t)k * N + ix]; nb[2] = mul[(size_t)k * N + iy]; }
      for (int j = 0; j < 3; j++) if (dist[nb[j]] < 0) { dist[nb[j]] = dv + 1; qu[t++] = nb[j]; }
    }
    ca = V - t;
  }
  {
    for (int i = 0; i < V; i++) dist[i] = -1;
    int h = 0, t = 0; qu[t++] = N; dist[N] = 0;
    while (h < t) { int v = qu[h++]; int dv = dist[v]; if (dv >= D) continue;
      int nb[3];
      if (v < N) { nb[0] = N + v; nb[1] = N + mul[(size_t)v * N + x]; nb[2] = N + mul[(size_t)v * N + y]; }
      else { int k = v - N; nb[0] = k; nb[1] = mul[(size_t)k * N + ix]; nb[2] = mul[(size_t)k * N + iy]; }
      for (int j = 0; j < 3; j++) if (dist[nb[j]] < 0) { dist[nb[j]] = dv + 1; qu[t++] = nb[j]; }
    }
    cb = V - t;
  }
  return ca + cb;
}
static int cay_cost(int a, int b, int c) {
  /* full BFS from e (index 0) with parity check; returns cost */
  for (int i = 0; i < N; i++) dist[i] = -1;
  int h = 0, t = 0; qu[t++] = 0; dist[0] = 0;
  int s[3] = {a, b, c};
  while (h < t) { int v = qu[h++];
    for (int j = 0; j < 3; j++) { int w = mul[(size_t)v * N + s[j]]; if (dist[w] < 0) { dist[w] = dist[v] + 1; qu[t++] = w; } }
  }
  int far = N - t;
  for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++) {
    int w = mul[(size_t)g * N + s[j]];
    if (dist[w] < 0 || dist[g] < 0) continue;
    if (((dist[w] - dist[g]) & 1) == 0) return 1000000000; /* not bipartite */
  }
  for (int g = 0; g < N; g++) if (dist[g] > D) far++;
  return far;
}
int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: cay MODE(h|c) GROUPFILE SECONDS SEED PREFIX [D]\n"); return 1; }
  char mode = argv[1][0];
  FILE *f = fopen(argv[2], "r"); if (!f) { perror("group"); return 1; }
  double T = atof(argv[3]); rs += (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
  const char *pre = argv[5]; if (argc > 6) D = atoi(argv[6]);
  if (fscanf(f, "%d %d", &d, &ng) != 2) return 1;
  gens = malloc(sizeof(uint16_t) * d * ng);
  for (int t = 0; t < ng; t++) for (int i = 0; i < d; i++) { int v; if (fscanf(f, "%d", &v) != 1) return 1; gens[t * d + i] = v; }
  fclose(f);
  el = malloc(sizeof(uint16_t) * (size_t)MAXN * d);
  closure();
  printf("group order N=%d degree=%d\n", N, d); fflush(stdout);
  if (N > MAXN) return 2;
  mul = malloc(sizeof(uint16_t) * (size_t)N * N);
  inv = malloc(sizeof(int) * N);
  build_mul();
  dist = malloc(sizeof(int) * 2 * N); qu = malloc(sizeof(int) * 2 * N);
  double t0 = now();
  int best = 1 << 30; long evals = 0;
  if (mode == 'h') {
    int bx = 0, by = 0;
    while (now() - t0 < T) {
      int x = 1 + rnd() % (N - 1), y;
      do y = 1 + rnd() % (N - 1); while (y == x);
      int c = haar_cost(x, y), stall = 0;
      while (stall < 3000 && now() - t0 < T) {
        int nx = x, ny = y;
        if (rnd() & 1) { do nx = 1 + rnd() % (N - 1); while (nx == ny); }
        else { do ny = 1 + rnd() % (N - 1); while (ny == nx); }
        int c2 = haar_cost(nx, ny); evals++;
        if (c2 <= c) { if (c2 < c) stall = 0; else stall++; c = c2; x = nx; y = ny; } else stall++;
        if (c < best) { best = c; bx = x; by = y; printf("best cost %d x=%d y=%d (evals %ld, %.1fs)\n", best, bx, by, evals, now() - t0); fflush(stdout); }
        if (c == 0) break;
      }
      if (best == 0) break;
    }
    printf("RESULT mode=h N=%d best_cost=%d x=%d y=%d evals=%ld\n", N, best, bx, by, evals);
    if (best == 0) {
      char fn[512]; snprintf(fn, sizeof fn, "%s.sol", pre);
      FILE *o = fopen(fn, "w"); fprintf(o, "%d %d %d\n", N, bx, by); fclose(o);
      snprintf(fn, sizeof fn, "%s.edges", pre); o = fopen(fn, "w");
      fprintf(o, "%d\n", 2 * N);
      for (int g = 0; g < N; g++) { fprintf(o, "%d %d\n", g, N + g); fprintf(o, "%d %d\n", g, N + mul[(size_t)g * N + bx]); fprintf(o, "%d %d\n", g, N + mul[(size_t)g * N + by]); }
      fclose(o); printf("wrote %s.sol and %s.edges\n", pre, pre);
    }
  } else {
    int *inls = malloc(sizeof(int) * N); int ni = 0;
    for (int g = 1; g < N; g++) if (mul[(size_t)g * N + g] == 0) inls[ni++] = g;
    printf("involutions: %d\n", ni);
    int bs[3] = {0, 0, 0};
    if (ni < 3) return 3;
    while (now() - t0 < T) {
      int s[3]; for (int j = 0; j < 3; j++) s[j] = inls[rnd() % ni];
      if (s[0] == s[1] || s[1] == s[2] || s[0] == s[2]) continue;
      int c = cay_cost(s[0], s[1], s[2]), stall = 0;
      while (stall < 2000 && now() - t0 < T) {
        int r = rnd() % 3, ns[3] = {s[0], s[1], s[2]};
        ns[r] = inls[rnd() % ni];
        if (ns[0] == ns[1] || ns[1] == ns[2] || ns[0] == ns[2]) continue;
        int c2 = cay_cost(ns[0], ns[1], ns[2]); evals++;
        if (c2 <= c) { if (c2 < c) stall = 0; else stall++; c = c2; s[0] = ns[0]; s[1] = ns[1]; s[2] = ns[2]; } else stall++;
        if (c < best) { best = c; memcpy(bs, s, sizeof bs); printf("best cost %d gens=%d %d %d (evals %ld, %.1fs)\n", best, bs[0], bs[1], bs[2], evals, now() - t0); fflush(stdout); }
        if (c == 0) break;
      }
      if (best == 0) break;
    }
    printf("RESULT mode=c N=%d best_cost=%d gens=%d %d %d evals=%ld\n", N, best, bs[0], bs[1], bs[2], evals);
    if (best == 0) {
      char fn[512]; snprintf(fn, sizeof fn, "%s.sol", pre);
      FILE *o = fopen(fn, "w"); fprintf(o, "%d %d %d %d\n", N, bs[0], bs[1], bs[2]); fclose(o);
      snprintf(fn, sizeof fn, "%s.edges", pre); o = fopen(fn, "w");
      fprintf(o, "%d\n", N);
      for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++) { int h2 = mul[(size_t)g * N + bs[j]]; if (g < h2) fprintf(o, "%d %d\n", g, h2); }
      fclose(o); printf("wrote %s.sol and %s.edges\n", pre, pre);
    }
  }
  return 0;
}
