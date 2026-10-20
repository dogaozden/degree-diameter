// Capacitated hypergraph independent set by tabu search with a fixed target size k.
// Instance (text): n m, then m lines "cap size v1 v2 ...". Find a set X of k vertices with |X & e| <= cap(e) for all e.
// Penalty = sum_e max(0, |X & e| - cap(e)). On reaching penalty 0, save X and set k = k+1.
// usage: hs INSTANCE k0 seconds seed OUTFILE [init_file]   (starts at min(k0, greedy size + 1))
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n, m;
static int *cap, *esz, **ev;   // hyperedges
static int *vdeg, **ve;        // incidence
static int *cnt;               // |X & e|
static int *in;                // membership
static int *addc;              // # e containing v with cnt >= cap  (cost to add v, if v not in X)
static int *remg;              // # e containing v with cnt > cap   (gain from removing v, if v in X)
static long long *tabu;
static int *X, *pos, xs;       // X as list
static unsigned long long rs;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void inc(int e) {
  int c = cnt[e]++;
  if (c + 1 == cap[e]) for (int i = 0; i < esz[e]; i++) addc[ev[e][i]]++;
  if (c + 1 == cap[e] + 1) for (int i = 0; i < esz[e]; i++) remg[ev[e][i]]++;
}
static void dec(int e) {
  int c = cnt[e]--;
  if (c == cap[e]) for (int i = 0; i < esz[e]; i++) addc[ev[e][i]]--;
  if (c == cap[e] + 1) for (int i = 0; i < esz[e]; i++) remg[ev[e][i]]--;
}
static long long pen;
static void add(int v) {
  for (int i = 0; i < vdeg[v]; i++) { int e = ve[v][i]; if (cnt[e] >= cap[e]) pen++; inc(e); }
  in[v] = 1; pos[v] = xs; X[xs++] = v;
}
static void rem(int v) {
  for (int i = 0; i < vdeg[v]; i++) { int e = ve[v][i]; if (cnt[e] > cap[e]) pen--; dec(e); }
  in[v] = 0; int p = pos[v]; X[p] = X[--xs]; pos[X[p]] = p;
}
// cost to add v given that u was just removed is approximated by addc[v] (exact after the removal).

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
  FILE *f = fopen(argv[1], "r");
  int k = atoi(argv[2]); double secs = atof(argv[3]); rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[4]) * 2654435761ULL;
  if (fscanf(f, "%d %d", &n, &m) != 2) return 1;
  cap = malloc(m * sizeof(int)); esz = malloc(m * sizeof(int)); ev = malloc(m * sizeof(int *));
  vdeg = calloc(n, sizeof(int));
  for (int e = 0; e < m; e++) {
    if (fscanf(f, "%d %d", &cap[e], &esz[e]) != 2) return 1;
    ev[e] = malloc(esz[e] * sizeof(int));
    for (int i = 0; i < esz[e]; i++) { if (fscanf(f, "%d", &ev[e][i]) != 1) return 1; vdeg[ev[e][i]]++; }
  }
  fclose(f);
  ve = malloc(n * sizeof(int *));
  int *fill = calloc(n, sizeof(int));
  for (int v = 0; v < n; v++) ve[v] = malloc(vdeg[v] * sizeof(int));
  for (int e = 0; e < m; e++) for (int i = 0; i < esz[e]; i++) { int v = ev[e][i]; ve[v][fill[v]++] = e; }
  cnt = calloc(m, sizeof(int)); in = calloc(n, sizeof(int)); addc = calloc(n, sizeof(int)); remg = calloc(n, sizeof(int));
  tabu = calloc(n, sizeof(long long)); X = malloc(n * sizeof(int)); pos = malloc(n * sizeof(int)); xs = 0;
  for (int e = 0; e < m; e++) if (cap[e] == 0) for (int i = 0; i < esz[e]; i++) addc[ev[e][i]]++;
  // initial: from file or greedy
  if (argc > 6) {
    FILE *g = fopen(argv[6], "r"); int v;
    while (g && fscanf(g, "%d", &v) == 1) add(v);
    if (g) fclose(g);
  }
  // greedy fill with zero-cost vertices
  {
    int *ord = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) ord[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
    for (int i = 0; i < n; i++) if (!in[ord[i]] && addc[ord[i]] == 0) add(ord[i]);
    free(ord);
  }
  if (pen == 0 && k > xs + 1) k = xs + 1;  // grow from the greedy start (k0 only caps it)
  int best = pen == 0 ? xs : 0;
  if (best) { FILE *o = fopen(argv[5], "w"); for (int i = 0; i < xs; i++) fprintf(o, "%d\n", X[i]); fclose(o); printf("init %d\n", best); fflush(stdout); }
  while (xs < k) { // add cheapest
    int bv = -1, bc = 1 << 30;
    for (int v = 0; v < n; v++) if (!in[v] && addc[v] < bc) { bc = addc[v]; bv = v; }
    add(bv);
  }
  clock_t t0 = clock();
  long long it = 0;
  int tt = 7;
  int *cand = malloc(n * sizeof(int));
  while (1) {
    if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
    it++;
    if (pen == 0) {
      if (xs > best) {
        best = xs;
        FILE *o = fopen(argv[5], "w"); for (int i = 0; i < xs; i++) fprintf(o, "%d\n", X[i]); fclose(o);
        printf("%.1fs it=%lld size=%d\n", (double)(clock() - t0) / CLOCKS_PER_SEC, it, best); fflush(stdout);
      }
      // grow: add cheapest vertex
      int nc = 0, bc = 1 << 30;
      for (int v = 0; v < n; v++) if (!in[v]) { if (addc[v] < bc) { bc = addc[v]; nc = 0; } if (addc[v] == bc) cand[nc++] = v; }
      add(cand[rnd() % nc]);
      continue;
    }
    // pick u in X: maximize remg (conflicting), not tabu unless aspiration
    int nc = 0, bg = -1;
    for (int i = 0; i < xs; i++) { int u = X[i]; if (tabu[u] > it) continue; if (remg[u] > bg) { bg = remg[u]; nc = 0; } if (remg[u] == bg) cand[nc++] = u; }
    if (nc == 0) { int u = X[rnd() % xs]; cand[0] = u; nc = 1; }
    int u = cand[rnd() % nc];
    rem(u);
    tabu[u] = it + tt + (rnd() % 10);
    nc = 0; int bc = 1 << 30;
    for (int v = 0; v < n; v++) {
      if (in[v] || v == u) continue;
      int c = addc[v];
      if (tabu[v] > it && pen + c != 0) continue;
      if (c < bc) { bc = c; nc = 0; }
      if (c == bc) cand[nc++] = v;
    }
    if (nc == 0) { add(u); continue; }
    int v = cand[rnd() % nc];
    add(v);
    tabu[v] = it + tt + (rnd() % 10);
  }
  printf("done best=%d it=%lld\n", best, it);
  return 0;
}
