/* tann3.c -- tann2.c (targeted annealing on Z_M lifts of H(q) + j hop matchings: same exact evaluation, same
 * voltage and hop-swap moves, same schedule) plus a multi-edge penalty.
 * cost = unreached + LAM * multi, where multi = number of pairs of parallel lift darts at a base vertex with equal
 * voltage (liftdiam's multi_edges; a lift double edge is counted at both base endpoints). LAM = environment variable
 * LAM (default 10). While multi > 0, half of the proposals re-voltage one edge of a random duplicate dart pair.
 * usage: LAM=10 tann3 gh.txt j M seconds T0 T1 seed R out_base.txt [pswap] [resume_base.txt]
 * Output file (liftdiam format): the best state with multi = 0 (minimal unreached), or the best total-cost state
 * if no multi-free state was seen. Stdout: "imp t <sec> unreached <u>" at each new best multi-free state.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <limits.h>

static int MG, J;
static int q, N, NB, NF, E, DEG;
static int *eu, *ev, *evol;   /* edge e: point eu[e], line vertex ev[e] (>= N), dart eu->ev carries evol[e] */
static int *inc;              /* inc[v*DEG+i]: incident edge ids */
static int *dto, *dw;         /* darts v -> dto[v*DEG+i] with voltage dw[v*DEG+i], rebuilt per evaluation */
static uint64_t *A, *B;
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
    else { dto[v * DEG + i] = eu[e]; dw[v * DEG + i] = (MG - evol[e]) % MG; }
  }
}

/* unchanged from tann2.c: unreached (source x, lift vertex (v,g)) pairs at distance > 8, early exit above limit */
static long long evaluate(long long limit, plist *out) {
  build_darts();
  out->n = 0;
  long long total = 0;
  const int W = 2 * MG;
  for (int b0 = 0; b0 < NB; b0 += 64) {
    int nb = NB - b0 < 64 ? NB - b0 : 64;
    uint64_t full = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
    memset(A, 0, sizeof(uint64_t) * W * (size_t)NB);
    for (int i = 0; i < nb; i++) { int x = b0 + i; A[(size_t)x * W + 0] |= 1ULL << i; A[(size_t)x * W + MG] |= 1ULL << i; }
    uint64_t *cur = A, *nxt = B;
    for (int lev = 0; lev < 8; lev++) {
      for (int v = 0; v < NB; v++) {
        uint64_t acc[64];
        const uint64_t *cv = cur + (size_t)v * W;
        for (int g = 0; g < MG; g++) acc[g] = cv[g];
        for (int i = 0; i < DEG; i++) {
          const uint64_t *cu = cur + (size_t)dto[v * DEG + i] * W + dw[v * DEG + i];
          for (int g = 0; g < MG; g++) acc[g] |= cu[g];
        }
        uint64_t *nv = nxt + (size_t)v * W;
        for (int g = 0; g < MG; g++) { nv[g] = acc[g]; nv[g + MG] = acc[g]; }
      }
      uint64_t *t = cur; cur = nxt; nxt = t;
    }
    for (int v = 0; v < NB; v++) for (int g = 0; g < MG; g++) {
      uint64_t m = ~cur[(size_t)v * W + g] & full;
      while (m) { int i = __builtin_ctzll(m); m &= m - 1; total++; pl_push(out, b0 + i, v); }
    }
    if (total > limit) return -1;
  }
  return total;
}

/* multi-edge count of the state whose darts were built by build_darts(); dup list kept in dupv/dupi/dupj */
static int *dupv, *dupi, *dupj; static long long ndup;
static long long multi_count(void) {
  ndup = 0;
  for (int v = 0; v < NB; v++) {
    const int *dt = dto + v * DEG, *dwt = dw + v * DEG;
    for (int i = 0; i < DEG; i++) for (int j = i + 1; j < DEG; j++)
      if (dt[i] == dt[j] && dwt[i] == dwt[j]) { dupv[ndup] = v; dupi[ndup] = i; dupj[ndup] = j; ndup++; }
  }
  return ndup;
}

static void write_base(const char *fn, const int *vol, const int *ee_u, const int *ee_v) {
  FILE *o = fopen(fn, "w");
  if (!o) { perror(fn); exit(1); }
  fprintf(o, "%d %d 1 %d\n", NB, MG, E);
  for (int e = 0; e < E; e++) fprintf(o, "%d %d %d 0\n", ee_u[e], ee_v[e], vol[e]);
  fclose(o);
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static int *fvol, *fu, *fv, *tvol, *tu, *tv;   /* best multi-free state, best total-cost state */
static long long best_feas = LLONG_MAX; static double best_tot = 1e300;
static void snapshot(int *vol, int *u, int *v) { memcpy(vol, evol, sizeof(int) * E); memcpy(u, eu, sizeof(int) * E); memcpy(v, ev, sizeof(int) * E); }
static void save_out(const char *fn) {
  if (best_feas != LLONG_MAX) write_base(fn, fvol, fu, fv); else write_base(fn, tvol, tu, tv);
}

int main(int argc, char **argv) {
  if (argc < 10) { fprintf(stderr, "usage: LAM=10 tann3 gh.txt j M seconds T0 T1 seed R out_base.txt [pswap] [resume]\n"); return 1; }
  J = atoi(argv[2]); MG = atoi(argv[3]);
  if (J < 1 || J > 4 || MG < 2 || MG > 64) { fprintf(stderr, "need 1 <= j <= 4, 2 <= M <= 64\n"); return 1; }
  double secs = atof(argv[4]), T0 = atof(argv[5]), T1 = atof(argv[6]);
  rs ^= (uint64_t)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
  int R = atoi(argv[8]); const char *outfn = argv[9];
  double pswap = argc > 10 ? atof(argv[10]) : 0.1;
  double LAM = getenv("LAM") ? atof(getenv("LAM")) : 10.0;

  FILE *f = fopen(argv[1], "r");
  if (!f || fscanf(f, "%d %d", &q, &N) != 2) { fprintf(stderr, "bad gh file\n"); return 1; }
  DEG = q + 1 + J; NB = 2 * N; NF = N * (q + 1); E = NF + J * N;
  eu = malloc(sizeof(int) * E); ev = malloc(sizeof(int) * E); evol = malloc(sizeof(int) * E);
  for (int k = 0; k < N; k++) for (int i = 0; i <= q; i++) {
    int p; if (fscanf(f, "%d", &p) != 1) { fprintf(stderr, "short gh file\n"); return 1; }
    int e = k * (q + 1) + i; eu[e] = p; ev[e] = N + k; evol[e] = rnd() % MG;
  }
  fclose(f);
  int *s = malloc(sizeof(int) * N);
  for (int k = 0; k < J; k++) {
    for (int p = 0; p < N; p++) s[p] = p;
    for (int i = N - 1; i > 0; i--) { int r = rnd() % (i + 1); int t = s[i]; s[i] = s[r]; s[r] = t; }
    for (int p = 0; p < N; p++) { int e = NF + k * N + p; eu[e] = p; ev[e] = N + s[p]; evol[e] = rnd() % MG; }
  }
  if (argc > 11) {
    FILE *g = fopen(argv[11], "r"); int nb2, m1, m2, e2;
    if (!g || fscanf(g, "%d %d %d %d", &nb2, &m1, &m2, &e2) != 4 || nb2 != NB || e2 != E || m1 != MG) { fprintf(stderr, "bad resume file\n"); return 1; }
    for (int e = 0; e < E; e++) { int u, v, a, b; if (fscanf(g, "%d %d %d %d", &u, &v, &a, &b) != 4) { fprintf(stderr, "short resume\n"); return 1; } eu[e] = u; ev[e] = v; evol[e] = ((a % MG) + MG) % MG; }
    fclose(g); fprintf(stderr, "resumed from %s\n", argv[11]);
  }
  inc = malloc(sizeof(int) * NB * DEG); dto = malloc(sizeof(int) * NB * DEG); dw = malloc(sizeof(int) * NB * DEG);
  build_inc();
  A = malloc(sizeof(uint64_t) * 2 * MG * (size_t)NB); B = malloc(sizeof(uint64_t) * 2 * MG * (size_t)NB);
  dupv = malloc(sizeof(int) * NB * DEG * DEG); dupi = malloc(sizeof(int) * NB * DEG * DEG); dupj = malloc(sizeof(int) * NB * DEG * DEG);
  fvol = malloc(sizeof(int) * E); fu = malloc(sizeof(int) * E); fv = malloc(sizeof(int) * E);
  tvol = malloc(sizeof(int) * E); tu = malloc(sizeof(int) * E); tv = malloc(sizeof(int) * E);

  plist cur_l = {0}, cand_l = {0};
  build_darts();
  long long cur_m = multi_count();
  long long cur_u = evaluate(1LL << 62, &cur_l);
  if (cur_m == 0) { best_feas = cur_u; snapshot(fvol, fu, fv); }
  best_tot = cur_u + LAM * cur_m; snapshot(tvol, tu, tv);
  printf("initial unreached %lld multi %lld (list %lld) LAM %.2f\n", cur_u, cur_m, cur_l.n, LAM); fflush(stdout);

  int *depth = malloc(sizeof(int) * NB), *queue = malloc(sizeof(int) * NB), *stamp_e = calloc(E, sizeof(int));
  int *near = malloc(sizeof(int) * E); int *hopinv = malloc(sizeof(int) * N);
  for (int v = 0; v < NB; v++) depth[v] = -1;
  int estamp = 0;
  long long iters = 0, accepted = 0, evals = 0; double t0 = now(), tlast = t0, tsave = t0;

  while (1) {
    double el = now() - t0; if (el > secs) break;
    if (cur_u == 0 && cur_m == 0) break;
    double T = T0 * pow(T1 / T0, el / secs);
    if (now() - tsave > 60) { save_out(outfn); tsave = now(); }
    if (now() - tlast > 30) {
      printf("t %.0f T %.3f cur_u %lld cur_m %lld best_feas %lld iters %lld acc %lld\n", el, T, cur_u, cur_m,
             best_feas == LLONG_MAX ? -1LL : best_feas, iters, accepted);
      fflush(stdout); tlast = now();
    }
    iters++;
    double thr = (double)cur_u + LAM * (double)cur_m - T * log(rnd01());   /* accept iff new total <= thr */

    if (cur_m > 0) { build_darts(); multi_count(); }   /* duplicate dart pairs of the current state */
    int do_multi = cur_m > 0 && (cur_l.n == 0 || rnd01() < 0.5);
    int mv, anchor = -1;   /* mv: 0 = re-voltage a duplicate edge, 1 = hop swap, 2 = voltage near anchor */
    if (do_multi) mv = 0;
    else {
      long long idx = rnd() % cur_l.n;
      int x = cur_l.x[idx], vv = cur_l.v[idx];
      anchor = (rnd() & 1) ? x : vv;
      mv = (rnd01() < pswap) ? 1 : 2;
    }

    int e_mod = -1, old_vol = 0, hop_k = -1, p1 = -1, p2 = -1;
    if (mv == 0) {
      long long di = rnd() % ndup;
      int v0 = dupv[di], i = (rnd() & 1) ? dupi[di] : dupj[di];
      e_mod = inc[v0 * DEG + i];
      old_vol = evol[e_mod];
      evol[e_mod] = (old_vol + 1 + (int)(rnd() % (MG - 1))) % MG;
    } else if (mv == 1) {
      hop_k = rnd() % J; int base = NF + hop_k * N;
      if (anchor < N) p1 = anchor;
      else { for (int p = 0; p < N; p++) hopinv[ev[base + p] - N] = p; p1 = hopinv[anchor - N]; }
      p2 = rnd() % (N - 1); if (p2 >= p1) p2++;
      int t = ev[base + p1]; ev[base + p1] = ev[base + p2]; ev[base + p2] = t;
      build_inc();
    } else {
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
      e_mod = near[rnd() % nn];
      old_vol = evol[e_mod];
      evol[e_mod] = (old_vol + 1 + (int)(rnd() % (MG - 1))) % MG;
    }

    build_darts();
    long long cm = multi_count();
    double lim_real = thr - LAM * (double)cm;
    long long r = -1, lim = -1;
    if (lim_real >= 0) { lim = (long long)floor(lim_real); evals++; r = evaluate(lim, &cand_l); }
    if (r >= 0 && r <= lim) {
      cur_u = r; cur_m = cm; plist tmp = cur_l; cur_l = cand_l; cand_l = tmp; accepted++;
      if (cur_m == 0 && cur_u < best_feas) {
        best_feas = cur_u; snapshot(fvol, fu, fv);
        printf("imp t %.1f unreached %lld\n", now() - t0, best_feas); fflush(stdout);
      }
      double tot = (double)cur_u + LAM * (double)cur_m;
      if (tot < best_tot) { best_tot = tot; snapshot(tvol, tu, tv); }
    } else {
      if (mv == 1) {
        int base = NF + hop_k * N; int t = ev[base + p1]; ev[base + p1] = ev[base + p2]; ev[base + p2] = t; build_inc();
      } else evol[e_mod] = old_vol;
    }
  }
  save_out(outfn);
  printf("done: evals %lld accepted %lld best_feas %lld best_tot %.1f final_u %lld final_m %lld time %.1f\n", evals,
         accepted, best_feas == LLONG_MAX ? -1LL : best_feas, best_tot, cur_u, cur_m, now() - t0);
  return 0;
}
