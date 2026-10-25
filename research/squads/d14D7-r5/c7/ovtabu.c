/* ovtabu.c: k-fixed tabu search for large sets of pairwise non-orthogonal points of Q(6,11)
   (partial ovoids).  Conflict = B(x,y)=0 for distinct points of the input list.
   Grows k whenever a conflict-free set of size k is found.
   usage: ovtabu POINTS.txt -t SECONDS -s SEED [-k K0] [-o OUT.txt] [-w WARM.txt] [-T TT]
   Build: gcc -O3 -march=native -o ovtabu ovtabu.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

#define QQ 11
static int n;
static int (*P)[7];
static uint64_t *bits; static int W;
static int *deg, **nb;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int adj(int i, int j){ return (int)((bits[(size_t)i * W + (j >> 6)] >> (j & 63)) & 1ULL); }
static int Bf(const int *x, const int *y){
  long s = (long)x[0]*y[4] + (long)x[4]*y[0] + (long)x[1]*y[5] + (long)x[5]*y[1] + (long)x[2]*y[6] + (long)x[6]*y[2] - 2L*x[3]*y[3];
  s %= QQ; if (s < 0) s += QQ; return (int)s;
}
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int inv11(int a){ int r = 1, e = 9; a %= QQ; while (e) { if (e & 1) r = r * a % QQ; a = a * a % QQ; e >>= 1; } return r; }
static void normalize(int *x){
  int i = 0; while (i < 7 && x[i] == 0) i++;
  if (i == 7) return;
  int s = inv11(x[i]); for (int j = 0; j < 7; j++) x[j] = ((x[j] % QQ + QQ) * s) % QQ;
}
static long code(const int *x){ long c = 0; for (int j = 6; j >= 0; j--) c = c * QQ + x[j]; return c; }

static int *inS, *conf, *tabu, *Slist, *Spos, k_cur;
static long f_cur;
static void addv(int v){
  inS[v] = 1; Spos[v] = k_cur; Slist[k_cur++] = v; f_cur += conf[v];
  for (int t = 0; t < deg[v]; t++) conf[nb[v][t]]++;
}
static void remv(int u){
  f_cur -= conf[u];
  inS[u] = 0; int p = Spos[u]; int last = Slist[--k_cur]; Slist[p] = last; Spos[last] = p;
  for (int t = 0; t < deg[u]; t++) conf[nb[u][t]]--;
}

static void write_set(const char *path, const int *list, int k){
  FILE *fo = fopen(path, "w"); if (!fo) return;
  fprintf(fo, "# ovtabu set, n=%d\n", k);
  for (int i = 0; i < k; i++){
    for (int j = 0; j < 7; j++) fprintf(fo, "%d ", P[list[i]][j]);
    fprintf(fo, "\n");
  }
  fclose(fo);
}

int main(int argc, char **argv){
  if (argc < 2) { fprintf(stderr, "usage: ovtabu POINTS -t SEC -s SEED [-k K0] [-o OUT] [-w WARM] [-T TT]\n"); return 1; }
  const char *inp = argv[1], *outp = "ovtabu_out.txt", *warm = NULL;
  double T = 60; uint64_t seed = 1; int K0 = 1, TT = 7; 
  for (int a = 2; a + 1 < argc; a += 2){
    if (!strcmp(argv[a], "-t")) T = atof(argv[a + 1]);
    else if (!strcmp(argv[a], "-s")) seed = strtoull(argv[a + 1], NULL, 10);
    else if (!strcmp(argv[a], "-k")) K0 = atoi(argv[a + 1]);
    else if (!strcmp(argv[a], "-o")) outp = argv[a + 1];
    else if (!strcmp(argv[a], "-w")) warm = argv[a + 1];
    else if (!strcmp(argv[a], "-T")) TT = atoi(argv[a + 1]);
  }
  rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
  /* read points */
  FILE *fi = fopen(inp, "r"); if (!fi) { perror(inp); return 1; }
  int cap = 1 << 16; n = 0; P = malloc(sizeof(*P) * cap);
  char line[256];
  while (fgets(line, sizeof line, fi)){
    if (line[0] == '#' || line[0] == '\n') continue;
    int x[7]; if (sscanf(line, "%d %d %d %d %d %d %d", &x[0], &x[1], &x[2], &x[3], &x[4], &x[5], &x[6]) != 7) continue;
    for (int j = 0; j < 7; j++) x[j] = ((x[j] % QQ) + QQ) % QQ;
    normalize(x);
    int s = (x[0]*x[4] + x[1]*x[5] + x[2]*x[6] - x[3]*x[3]) % QQ; if (s < 0) s += QQ;
    if (s != 0) { fprintf(stderr, "warning: non-singular point skipped\n"); continue; }
    if (n == cap) { cap *= 2; P = realloc(P, sizeof(*P) * cap); }
    memcpy(P[n], x, sizeof x); n++;
  }
  fclose(fi);
  fprintf(stderr, "read %d singular points\n", n);
  W = (n + 63) / 64; bits = calloc((size_t)n * W, sizeof(uint64_t));
  deg = calloc(n, sizeof(int));
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (Bf(P[i], P[j]) == 0){
    bits[(size_t)i * W + (j >> 6)] |= 1ULL << (j & 63);
    bits[(size_t)j * W + (i >> 6)] |= 1ULL << (i & 63);
    deg[i]++; deg[j]++;
  }
  nb = malloc(sizeof(int*) * n);
  for (int i = 0; i < n; i++){
    nb[i] = malloc(sizeof(int) * (deg[i] + 1)); int c = 0;
    for (int j = 0; j < n; j++) if (adj(i, j)) nb[i][c++] = j;
  }
  long avgdeg = 0; for (int i = 0; i < n; i++) avgdeg += deg[i];
  fprintf(stderr, "conflict graph: n=%d avg degree %.1f\n", n, n ? (double)avgdeg / n : 0.0);
  /* index of points by code (for warm start) */
  int *idx = NULL;
  if (warm){ idx = malloc(sizeof(int) * 19487171L); for (long i = 0; i < 19487171L; i++) idx[i] = -1;
    for (int i = 0; i < n; i++) idx[code(P[i])] = i; }
  inS = calloc(n, sizeof(int)); conf = calloc(n, sizeof(int)); tabu = calloc(n, sizeof(int));
  Slist = malloc(sizeof(int) * n); Spos = malloc(sizeof(int) * n); int *best = malloc(sizeof(int) * n);
  int bestk = 0; k_cur = 0; f_cur = 0;
  int K = K0;
  if (warm){
    FILE *fw = fopen(warm, "r"); int cnt = 0; int x[7];
    while (fgets(line, sizeof line, fw)){
      if (line[0] == '#' || line[0] == '\n') continue;
      if (sscanf(line, "%d %d %d %d %d %d %d", &x[0], &x[1], &x[2], &x[3], &x[4], &x[5], &x[6]) != 7) continue;
      for (int j = 0; j < 7; j++) x[j] = ((x[j] % QQ) + QQ) % QQ; normalize(x);
      int id = idx[code(x)]; if (id < 0 || inS[id]) continue; addv(id); cnt++;
    }
    fclose(fw);
    fprintf(stderr, "warm start: %d points, f=%ld\n", cnt, f_cur);
    K = k_cur;
  }
  /* initial random fill up to K */
  while (k_cur < K){
    int best_v = -1, bc = 1 << 30, ties = 0;
    for (int v = 0; v < n; v++) if (!inS[v]){
      if (conf[v] < bc){ bc = conf[v]; best_v = v; ties = 1; }
      else if (conf[v] == bc){ ties++; if (rnd() % ties == 0) best_v = v; }
    }
    addv(best_v);
  }
  double t0 = now(); long it = 0; long last_imp = 0; long bestf = f_cur;
  fprintf(stderr, "start k=%d f=%ld\n", k_cur, f_cur);
  while (now() - t0 < T){
    it++;
    if (f_cur == 0){
      bestk = k_cur; memcpy(best, Slist, sizeof(int) * k_cur);
      write_set(outp, best, bestk);
      fprintf(stderr, "k=%d found at it=%ld t=%.1fs\n", bestk, it, now() - t0);
      /* grow */
      int bv = -1, bc2 = 1 << 30, ties = 0;
      for (int v = 0; v < n; v++) if (!inS[v]){
        if (conf[v] < bc2){ bc2 = conf[v]; bv = v; ties = 1; }
        else if (conf[v] == bc2){ ties++; if (rnd() % ties == 0) bv = v; }
      }
      addv(bv); bestf = f_cur; last_imp = it;
      continue;
    }
    /* choose u in S: max conf among non-tabu (random ties) */
    int u = -1, uc = -1, ties = 0;
    for (int t = 0; t < k_cur; t++){
      int s = Slist[t]; if (tabu[s] > it) continue;
      if (conf[s] > uc){ uc = conf[s]; u = s; ties = 1; }
      else if (conf[s] == uc){ ties++; if (rnd() % ties == 0) u = s; }
    }
    if (u < 0) u = Slist[rnd() % k_cur];
    /* choose v not in S: min conf[v]-adj(u,v) among non-tabu */
    int v = -1, vc = 1 << 30; ties = 0;
    for (int w = 0; w < n; w++) if (!inS[w] && tabu[w] <= it){
      int c = conf[w] - adj(u, w);
      if (c < vc){ vc = c; v = w; ties = 1; }
      else if (c == vc){ ties++; if (rnd() % ties == 0) v = w; }
    }
    if (v < 0) { do { v = rnd() % n; } while (inS[v]); }
    remv(u); addv(v);
    tabu[u] = (int)it + 1 + (int)(rnd() % (TT + 1)) + 1;     /* u may not come back soon */
    tabu[v] = (int)it + 1 + (int)(rnd() % 3);                /* v may not leave at once */
    if (f_cur < bestf){ bestf = f_cur; last_imp = it; }
    if (it - last_imp > 200000){            /* stagnation: random perturbation */
      for (int r = 0; r < 3; r++){
        int a = Slist[rnd() % k_cur]; int b; do { b = rnd() % n; } while (inS[b]);
        remv(a); addv(b); tabu[a] = (int)it + 5;
      }
      bestf = f_cur; last_imp = it;
    }
    if ((it & 0x3FFFF) == 0) fprintf(stderr, "  it=%ld k=%d f=%ld bestk=%d t=%.0fs\n", it, k_cur, f_cur, bestk, now() - t0);
  }
  fprintf(stderr, "done: it=%ld bestk=%d\n", it, bestk);
  printf("RESULT ovtabu n_points=%d best=%d iters=%ld\n", n, bestk, it);
  return 0;
}
