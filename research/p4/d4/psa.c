// Simulated annealing for Theorem B at Delta = q+2 on W(3,q) with a free partial spread:
// choose lines P (pairwise disjoint) and points M with |M & l| <= 1 + [l in P] for every t.i. line l.
// Maximise |P| + |M|. Instance: inst_po_q*.txt (all lines). Optional init: file with "P j" / "M p" lines.
// usage: psa INST seconds seed OUT [lambda] [init]
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static unsigned long long rs;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

int n, L, K;
int **lp, **pl, *pdeg;
int *x, *y, *c, *d;  // x points in M, y lines in P, c[l] = |M & l|, d[p] = # P-lines through p
long long viol;

static inline int v1(int dp) { return dp > 1 ? dp - 1 : 0; }
static inline int v2(int cl, int yl) { int e = cl - 1 - yl; return e > 0 ? e : 0; }

// delta of violations for flipping point p
static int dflip_x(int p) {
  int s = x[p] ? -1 : 1, dv = 0;
  for (int i = 0; i < pdeg[p]; i++) { int l = pl[p][i]; dv += v2(c[l] + s, y[l]) - v2(c[l], y[l]); }
  return dv;
}
static int dflip_y(int l) {
  int s = y[l] ? -1 : 1, dv = v2(c[l], y[l] + s) - v2(c[l], y[l]);
  for (int i = 0; i < K; i++) { int p = lp[l][i]; dv += v1(d[p] + s) - v1(d[p]); }
  return dv;
}
static void do_x(int p) {
  int s = x[p] ? -1 : 1;
  for (int i = 0; i < pdeg[p]; i++) { int l = pl[p][i]; viol += v2(c[l] + s, y[l]) - v2(c[l], y[l]); c[l] += s; }
  x[p] ^= 1;
}
static void do_y(int l) {
  int s = y[l] ? -1 : 1;
  viol += v2(c[l], y[l] + s) - v2(c[l], y[l]);
  for (int i = 0; i < K; i++) { int p = lp[l][i]; viol += v1(d[p] + s) - v1(d[p]); d[p] += s; }
  y[l] ^= 1;
}

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r");
  double secs = atof(argv[2]);
  rs = 0x2545F4914F6CDD1DULL ^ (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
  double lam = argc > 5 ? atof(argv[5]) : 1.5;
  if (fscanf(f, "%d %d", &n, &L) != 2) return 1;
  lp = malloc(L * sizeof(int *)); pdeg = calloc(n, sizeof(int));
  for (int l = 0; l < L; l++) {
    int cap; if (fscanf(f, "%d %d", &cap, &K) != 2) return 1;
    lp[l] = malloc(K * sizeof(int));
    for (int i = 0; i < K; i++) { if (fscanf(f, "%d", &lp[l][i]) != 1) return 1; pdeg[lp[l][i]]++; }
  }
  pl = malloc(n * sizeof(int *)); int *fill = calloc(n, sizeof(int));
  for (int p = 0; p < n; p++) pl[p] = malloc(pdeg[p] * sizeof(int));
  for (int l = 0; l < L; l++) for (int i = 0; i < K; i++) { int p = lp[l][i]; pl[p][fill[p]++] = l; }
  x = calloc(n, sizeof(int)); y = calloc(L, sizeof(int)); c = calloc(L, sizeof(int)); d = calloc(n, sizeof(int));
  if (argc > 6) {
    FILE *g = fopen(argv[6], "r"); char t[4]; int v;
    while (g && fscanf(g, "%3s %d", t, &v) == 2) { if (t[0] == 'P') do_y(v); else do_x(v); }
    if (g) fclose(g);
  }
  int best = -1;
  long long score = 0;
  for (int p = 0; p < n; p++) score += x[p];
  for (int l = 0; l < L; l++) score += y[l];
  clock_t t0 = clock();
  double T0 = 0.6, T = T0;
  long long it = 0;
  while (1) {
    if ((it & 0x3FFF) == 0) {
      double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
      if (el > secs) break;
      double ph = fmod(el, 120.0) / 120.0;   // reheat every 2 minutes
      T = T0 * (1 - ph) + 0.04;
    }
    it++;
    int move = rnd() % 4;
    double dobj;
    if (move < 3) {
      int p = rnd() % n;
      int dv = dflip_x(p);
      dobj = (x[p] ? -1 : 1) - lam * dv;
      if (dobj >= 0 || urand() < exp(dobj / T)) { score += x[p] ? -1 : 1; do_x(p); }
    } else {
      int l = rnd() % L;
      int dv = dflip_y(l);
      dobj = (y[l] ? -1 : 1) - lam * dv;
      if (dobj >= 0 || urand() < exp(dobj / T)) { score += y[l] ? -1 : 1; do_y(l); }
    }
    if (viol == 0 && score > best) {
      best = (int)score;
      int np = 0; for (int l = 0; l < L; l++) np += y[l];
      FILE *o = fopen(argv[4], "w");
      for (int l = 0; l < L; l++) if (y[l]) fprintf(o, "P %d\n", l);
      for (int p = 0; p < n; p++) if (x[p]) fprintf(o, "M %d\n", p);
      fclose(o);
      printf("%.1fs |P|+|M|=%d (|P|=%d)\n", (double)(clock() - t0) / CLOCKS_PER_SEC, best, np); fflush(stdout);
    }
  }
  printf("done best=%d it=%lld\n", best, it);
  return 0;
}
