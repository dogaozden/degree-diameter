// Weighted m-ovoid search by simulated annealing: w(p) in {0..wmax}, minimise sum_lines |line sum - m|.
// Moves keep sum w = m*(number of points)/(points per line) ... (i.e. transfer one unit from p to p').
// Instance: same format as hs.c (n nlines, then "cap size v...", cap ignored; lines with cap < 0 skipped).
// usage: wov INST m wmax seconds seed OUT [skip_spread_caps]
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static unsigned long long rs;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r");
  int m = atoi(argv[2]), wmax = atoi(argv[3]);
  double secs = atof(argv[4]);
  rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
  int n, L;
  if (fscanf(f, "%d %d", &n, &L) != 2) return 1;
  int **lp = malloc(L * sizeof(int *)), *ls = malloc(L * sizeof(int));
  int *deg = calloc(n, sizeof(int));
  for (int e = 0; e < L; e++) {
    int c;
    if (fscanf(f, "%d %d", &c, &ls[e]) != 2) return 1;
    lp[e] = malloc(ls[e] * sizeof(int));
    for (int i = 0; i < ls[e]; i++) { if (fscanf(f, "%d", &lp[e][i]) != 1) return 1; deg[lp[e][i]]++; }
  }
  int **pl = malloc(n * sizeof(int *)), *fill = calloc(n, sizeof(int));
  for (int v = 0; v < n; v++) pl[v] = malloc(deg[v] * sizeof(int));
  for (int e = 0; e < L; e++) for (int i = 0; i < ls[e]; i++) { int v = lp[e][i]; pl[v][fill[v]++] = e; }
  int *w = calloc(n, sizeof(int)), *s = calloc(L, sizeof(int));
  long long total = (long long)m * L * 1 / 1;  // sum over lines of line sums = sum_p w(p) deg(p)
  int D = deg[0];
  long long W = (long long)m * L / D;  // total weight
  for (long long k = 0; k < W; k++) {
    int v;
    do v = rnd() % n; while (w[v] >= wmax);
    w[v]++;
  }
  for (int v = 0; v < n; v++) for (int i = 0; i < deg[v]; i++) s[pl[v][i]] += w[v];
  long long cost = 0;
  for (int e = 0; e < L; e++) cost += labs(s[e] - m);
  long long best = cost;
  double T0 = 2.0, T = T0;
  clock_t t0 = clock();
  long long it = 0;
  int *mark = calloc(L, sizeof(int));
  while (cost > 0) {
    if ((it & 0xFFFF) == 0) {
      double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
      if (el > secs) break;
      T = T0 * (1.0 - el / secs) + 0.05;
    }
    it++;
    // pick p with w>0 on an over-full line preferably
    int p, p2;
    do p = rnd() % n; while (w[p] == 0);
    do p2 = rnd() % n; while (w[p2] >= wmax || p2 == p);
    long long d = 0;
    for (int i = 0; i < deg[p]; i++) { int e = pl[p][i]; mark[e] = 1; }
    for (int i = 0; i < deg[p2]; i++) { int e = pl[p2][i]; if (mark[e]) mark[e] = 2; }
    for (int i = 0; i < deg[p]; i++) { int e = pl[p][i]; if (mark[e] == 1) d += labs(s[e] - 1 - m) - labs(s[e] - m); }
    for (int i = 0; i < deg[p2]; i++) { int e = pl[p2][i]; if (mark[e] != 2) d += labs(s[e] + 1 - m) - labs(s[e] - m); }
    for (int i = 0; i < deg[p]; i++) mark[pl[p][i]] = 0;
    for (int i = 0; i < deg[p2]; i++) mark[pl[p2][i]] = 0;
    if (d <= 0 || urand() < exp(-d / T)) {
      for (int i = 0; i < deg[p]; i++) s[pl[p][i]]--;
      for (int i = 0; i < deg[p2]; i++) s[pl[p2][i]]++;
      w[p]--; w[p2]++;
      cost += d;
      if (cost < best) { best = cost; }
    }
  }
  printf("cost=%lld best=%lld it=%lld\n", cost, best, it);
  if (cost == 0) {
    FILE *o = fopen(argv[6], "w");
    for (int v = 0; v < n; v++) fprintf(o, "%d\n", w[v]);
    fclose(o);
  }
  return cost != 0;
}
