/* tann.c -- targeted annealing of Z_8 voltages on the lift of H(q) + one hop matching (j = 1), squad card d4.
 * Cost = number of unreached (source, target) pairs at distance <= 8, i.e. liftdiam's unreached_pairs over all
 * 2N base sources (exact bit-parallel BFS: 64 sources per batch, group Z_8 in 8 words, duplicated for rotation).
 * Moves: (a) voltage of an edge near a currently unreached pair: the pair (x,v) is taken from the failing list,
 * the anchor is x or v at random, and the edge is drawn from all edges with an endpoint within distance R of the
 * anchor; (b) with prob PSWAP, swap the hop targets of two points, one of them the anchor (or the hop partner of
 * an anchor line). Metropolis on the full cost; temperature geometric in wall time; the acceptance threshold is
 * drawn first, so a rejected candidate stops as soon as its partial count exceeds it.
 * usage: tann gh.txt seconds T0 T1 seed R out_base.txt [pswap]
 * gh.txt: "q N", then N lines with the q+1 point ids of each line (dumpgh.py format).
 * out_base.txt: liftdiam format "NB 8 1 E", then "u v a 0" (dart point u -> line vertex v carries voltage a).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MG 8

static int q, N, NB, NF, E, DEG;
static int *eu, *ev, *evol;   /* edge e: point eu[e], line vertex ev[e] (>= N), dart eu->ev carries evol[e] */
static int *inc;              /* inc[v*DEG+i]: incident edge ids */
static int *dto, *dw;         /* darts v -> dto[v*DEG+i] with voltage dw[v*DEG+i], rebuilt per evaluation */
static uint64_t *A, *B;       /* per base vertex 16 words: word g (and g+8) = bits of sources reaching (v,g) */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return ((rnd() >> 11) + 0.5) * (1.0 / 9007199254740992.0); }

typedef struct { int *x, *v; long long n, cap; } plist;
static void pl_push(plist *p, int x, int v) {
  if (p->n == p->cap) {
    p->cap = p->cap ? 2 * p->cap : (1 << 16);
    p->x = realloc(p->x, sizeof(int) * p->cap); p->v = realloc(p->v, sizeof(int) * p->cap);
    if (!p->x || !p->v) { fprintf(stderr, "oom\n"); exit(1); }
  }
  p->x[p->n] = x; p->v[p->n] = v; p->n++;
}

static void build_inc(void) {
  int *deg = calloc(NB, sizeof(int));
  for (int e = 0; e < E; e++) {
    inc[eu[e] * DEG + deg[eu[e]]++] = e;
    inc[ev[e] * DEG + deg[ev[e]]++] = e;
  }
  for (int v = 0; v < NB; v++) if (deg[v] != DEG) { fprintf(stderr, "degree %d at %d\n", deg[v], v); exit(1); }
  free(deg);
}

static void build_darts(void) {
  for (int v = 0; v < NB; v++) for (int i = 0; i < DEG; i++) {
    int e = inc[v * DEG + i];
    if (eu[e] == v) { dto[v * DEG + i] = ev[e]; dw[v * DEG + i] = evol[e]; }
    else { dto[v * DEG + i] = eu[e]; dw[v * DEG + i] = (MG - evol[e]) & (MG - 1); }
  }
}

/* Full unreached count (sources x = 0..NB-1 at group element 0, targets (v,g) at distance > DD), with the list of
 * unreached pairs (x,v) filled into out. Returns -1 as soon as the running count exceeds limit (list incomplete). */
static long long evaluate(long long limit, plist *out) {
  build_darts();
  out->n = 0;
  long long total = 0;
  for (int b0 = 0; b0 < NB; b0 += 64) {
    int nb = NB - b0 < 64 ? NB - b0 : 64;
    uint64_t full = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
    memset(A, 0, sizeof(uint64_t) * 16 * (size_t)NB);
    for (int i = 0; i < nb; i++) { int x = b0 + i; A[x * 16 + 0] |= 1ULL << i; A[x * 16 + 8] |= 1ULL << i; }
    uint64_t *cur = A, *nxt = B;
    for (int lev = 0; lev < 8; lev++) {
      for (int v = 0; v < NB; v++) {
        uint64_t acc[8];
        const uint64_t *cv = cur + v * 16;
        for (int g = 0; g < 8; g++) acc[g] = cv[g];
        for (int i = 0; i < DEG; i++) {
          const uint64_t *cu = cur + (size_t)dto[v * DEG + i] * 16 + dw[v * DEG + i];
          for (int g = 0; g < 8; g++) acc[g] |= cu[g];
        }
        uint64_t *nv = nxt + v * 16;
        for (int g = 0; g < 8; g++) { nv[g] = acc[g]; nv[g + 8] = acc[g]; }
      }
      uint64_t *t = cur; cur = nxt; nxt = t;
    }
    for (int v = 0; v < NB; v++) for (int g = 0; g < 8; g++) {
      uint64_t m = ~cur[v * 16 + g] & full;
      while (m) { int i = __builtin_ctzll(m); m &= m - 1; total++; pl_push(out, b0 + i, v); }
    }
    if (total > limit) return -1;
  }
  return total;
}

static void write_base(const char *fn, const int *vol, const int *ee_u, const int *ee_v) {
  FILE *o = fopen(fn, "w");
  if (!o) { perror(fn); exit(1); }
  fprintf(o, "%d %d 1 %d\n", NB, MG, E);
  for (int e = 0; e < E; e++) fprintf(o, "%d %d %d 0\n", ee_u[e], ee_v[e], vol[e]);
  fclose(o);
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: tann gh.txt seconds T0 T1 seed R out_base.txt [pswap]\n"); return 1; }
  double secs = atof(argv[2]), T0 = atof(argv[3]), T1 = atof(argv[4]);
  rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
  int R = atoi(argv[6]); const char *outfn = argv[7];
  double pswap = argc > 8 ? atof(argv[8]) : 0.1;

  FILE *f = fopen(argv[1], "r");
  if (!f || fscanf(f, "%d %d", &q, &N) != 2) { fprintf(stderr, "bad gh file\n"); return 1; }
  DEG = q + 2; NB = 2 * N; NF = N * (q + 1); E = NF + N;
  eu = malloc(sizeof(int) * E); ev = malloc(sizeof(int) * E); evol = malloc(sizeof(int) * E);
  for (int k = 0; k < N; k++) for (int i = 0; i <= q; i++) {
    int p; if (fscanf(f, "%d", &p) != 1) { fprintf(stderr, "short gh file\n"); return 1; }
    int e = k * (q + 1) + i; eu[e] = p; ev[e] = N + k; evol[e] = rnd() % MG;
  }
  fclose(f);
  /* hop matching: random bijection points -> lines, random voltages */
  int *s = malloc(sizeof(int) * N); for (int p = 0; p < N; p++) s[p] = p;
  for (int i = N - 1; i > 0; i--) { int r = rnd() % (i + 1); int t = s[i]; s[i] = s[r]; s[r] = t; }
  for (int p = 0; p < N; p++) { int e = NF + p; eu[e] = p; ev[e] = N + s[p]; evol[e] = rnd() % MG; }
  inc = malloc(sizeof(int) * NB * DEG); dto = malloc(sizeof(int) * NB * DEG); dw = malloc(sizeof(int) * NB * DEG);
  build_inc();
  A = malloc(sizeof(uint64_t) * 16 * (size_t)NB); B = malloc(sizeof(uint64_t) * 16 * (size_t)NB);

  plist cur_l = {0}, cand_l = {0};
  long long cur = evaluate(1LL << 62, &cur_l);
  long long best = cur; int *bestvol = malloc(sizeof(int) * E), *bestu = malloc(sizeof(int) * E), *bestv = malloc(sizeof(int) * E);
  memcpy(bestvol, evol, sizeof(int) * E); memcpy(bestu, eu, sizeof(int) * E); memcpy(bestv, ev, sizeof(int) * E);
  printf("initial unreached %lld (list %lld)\n", cur, cur_l.n); fflush(stdout);

  /* scratch for neighbourhoods */
  int *depth = malloc(sizeof(int) * NB), *queue = malloc(sizeof(int) * NB), *stamp_e = calloc(E, sizeof(int));
  int *near = malloc(sizeof(int) * E); int *hopinv = malloc(sizeof(int) * N);
  for (int v = 0; v < NB; v++) depth[v] = -1;
  int estamp = 0;
  long long iters = 0, accepted = 0, evals = 0; double t0 = now(), tlast = t0, tsave = t0;

  while (cur > 0) {
    double el = now() - t0; if (el > secs) break;
    double T = T0 * pow(T1 / T0, el / secs);
    if (now() - tsave > 60) { write_base(outfn, bestvol, bestu, bestv); tsave = now(); }
    if (now() - tlast > 30) {
      printf("t %.0f T %.3f cur %lld best %lld iters %lld acc %lld\n", el, T, cur, best, iters, accepted); fflush(stdout);
      tlast = now();
    }
    iters++;
    long long idx = rnd() % cur_l.n;
    int x = cur_l.x[idx], v = cur_l.v[idx];
    int anchor = (rnd() & 1) ? x : v;
    double u = rnd01();
    double thr = (double)cur - T * log(u);   /* accept iff new <= thr (Metropolis) */
    long long limit = (long long)floor(thr);
    if (rnd01() < pswap) {
      /* hop swap at a point near the anchor */
      int p1;
      if (anchor < N) p1 = anchor;
      else { for (int p = 0; p < N; p++) hopinv[ev[NF + p] - N] = p; p1 = hopinv[anchor - N]; }
      int p2 = rnd() % N; if (p2 == p1) continue;
      int t = ev[NF + p1]; ev[NF + p1] = ev[NF + p2]; ev[NF + p2] = t;
      build_inc();
      evals++;
      long long r = evaluate(limit, &cand_l);
      if (r >= 0 && r <= limit) { cur = r; plist tmp = cur_l; cur_l = cand_l; cand_l = tmp; accepted++; }
      else { t = ev[NF + p1]; ev[NF + p1] = ev[NF + p2]; ev[NF + p2] = t; build_inc(); }
    } else {
      /* voltage change on an edge near the anchor (R-ball around anchor, all edges touching it) */
      build_darts();
      estamp++; int qh = 0, qt = 0, nn = 0;
      queue[qt++] = anchor; depth[anchor] = 0;
      while (qh < qt) {
        int w = queue[qh++]; int d = depth[w];
        for (int i = 0; i < DEG; i++) {
          int e = inc[w * DEG + i];
          if (stamp_e[e] != estamp) { stamp_e[e] = estamp; near[nn++] = e; }
          if (d < R) { int y = dto[w * DEG + i]; if (depth[y] < 0) { depth[y] = d + 1; queue[qt++] = y; } }
        }
      }
      for (int i = 0; i < qt; i++) depth[queue[i]] = -1;
      int e = near[rnd() % nn];
      int old = evol[e];
      int nvv = (old + 1 + (int)(rnd() % (MG - 1))) & (MG - 1);
      evol[e] = nvv;
      evals++;
      long long r = evaluate(limit, &cand_l);
      if (r >= 0 && r <= limit) { cur = r; plist tmp = cur_l; cur_l = cand_l; cand_l = tmp; accepted++; }
      else evol[e] = old;
    }
    if (cur < best) {
      best = cur;
      memcpy(bestvol, evol, sizeof(int) * E); memcpy(bestu, eu, sizeof(int) * E); memcpy(bestv, ev, sizeof(int) * E);
    }
  }
  write_base(outfn, bestvol, bestu, bestv);
  printf("done: evals %lld accepted %lld best %lld final_cur %lld time %.1f\n", evals, accepted, best, cur, now() - t0);
  return 0;
}
