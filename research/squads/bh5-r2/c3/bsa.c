/* bsa.c (squad bh5-r2 card c3): simulated annealing over bi-coset graphs, |H| = |K| = 2, degree DEG = 7.
 * Left vertices Hx, right vertices Ky (n = |G| vertices total). Edge (Hx, Ky) iff x y^-1 in S, S a union of double
 * cosets HgK; deg = |S|/2. Double cosets have contribution c = |HgK|/2 in {1,2}; a state is a set of double cosets
 * with contributions summing to DEG. Moves: swap two same-contribution items, split a c=2 item into two c=1 items,
 * merge two c=1 items into one c=2 item. Cost = vertices at distance > 5 from the two base vertices (left Hx0 and
 * right Ky0); G acts by right multiplication, so cost 0 <=> diameter <= 5.
 * usage: bsa GROUPFILE SECS STEPS RESTARTS SEED OUTPREFIX
 *   GROUPFILE: "N e" then N rows, row g col h = index of g*h.  Writes OUTPREFIX.edges if cost 0 is found, and
 *   prints one RESULT line per group.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

#define DIAM 5
#define DEG 7
static int N, E, *mul, *inv;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int n) { return (int)(urand() * n); }

static int Hel[2], Kel[2];
static int *Lc, *Rc, nL, nR, *repL, *repR;
static int *dcl, *dcstart, *dcsz, *dcel, ndc;
static int nitems, *items, *itemc, *flag;
static int *adj;            /* (nL+nR) * DEG */
static uint64_t *mark;      /* per vertex stamps */
static uint64_t stamp = 0;
static int *dist, *bq;
static int chosen[8], nsel;

static int build_pair(int h, int k) {
  Hel[0] = E; Hel[1] = h; Kel[0] = E; Kel[1] = k;
  for (int x = 0; x < N; x++) { Lc[x] = -1; Rc[x] = -1; }
  nL = 0; nR = 0;
  for (int x = 0; x < N; x++) {
    if (Lc[x] < 0) { for (int t = 0; t < 2; t++) Lc[mul[Hel[t] * N + x]] = nL; repL[nL++] = x; }
    if (Rc[x] < 0) { for (int t = 0; t < 2; t++) Rc[mul[Kel[t] * N + x]] = nR; repR[nR++] = x; }
  }
  for (int x = 0; x < N; x++) dcl[x] = -1;
  ndc = 0; int pos = 0;
  for (int g = 0; g < N; g++) if (dcl[g] < 0) {
    int lab = ndc++; dcstart[lab] = pos; int cnt = 0;
    for (int a = 0; a < 2; a++) for (int b = 0; b < 2; b++) {
      int y = mul[mul[Hel[a] * N + g] * N + Kel[b]];
      if (dcl[y] < 0) { dcl[y] = lab; dcel[pos++] = y; cnt++; }
    }
    dcsz[lab] = cnt;
  }
  nitems = 0;
  for (int lab = 0; lab < ndc; lab++) {
    int c = dcsz[lab] / 2;
    if (c == 1 || c == 2) { items[nitems] = lab; itemc[nitems] = c; flag[nitems] = 0; nitems++; }
  }
  return nitems;
}

/* returns cost (unreached count), or -1 if degrees are wrong */
static int evaluate(void) {
  int S[2 * DEG + 2], ns = 0;
  for (int p = 0; p < nsel; p++) {
    int lab = items[chosen[p]];
    for (int t = dcstart[lab]; t < dcstart[lab] + dcsz[lab]; t++) S[ns++] = dcel[t];
  }
  if (ns != 2 * DEG) return -1;
  for (int i = 0; i < nL; i++) {
    int x = repL[i], cnt = 0; stamp++;
    for (int s = 0; s < ns; s++) {
      int j = Rc[mul[inv[S[s]] * N + x]];
      if (mark[j] != stamp) { mark[j] = stamp; if (cnt >= DEG) return -1; adj[i * DEG + cnt++] = nL + j; }
    }
    if (cnt != DEG) return -1;
  }
  for (int j = 0; j < nR; j++) {
    int y = repR[j], cnt = 0; stamp++;
    for (int s = 0; s < ns; s++) {
      int i = Lc[mul[S[s] * N + y]];
      if (mark[nL + i] != stamp) { mark[nL + i] = stamp; if (cnt >= DEG) return -1; adj[(nL + j) * DEG + cnt++] = i; }
    }
    if (cnt != DEG) return -1;
  }
  int V = nL + nR, cost = 0;
  int bases[2] = { 0, nL + 0 };
  for (int b = 0; b < 2; b++) {
    for (int v = 0; v < V; v++) dist[v] = -1;
    int h = 0, t = 0; bq[t++] = bases[b]; dist[bases[b]] = 0;
    while (h < t) {
      int v = bq[h++];
      if (dist[v] >= DIAM) continue;
      for (int d = 0; d < DEG; d++) { int w = adj[v * DEG + d]; if (dist[w] < 0) { dist[w] = dist[v] + 1; bq[t++] = w; } }
    }
    for (int v = 0; v < V; v++) if (dist[v] < 0) cost++;
  }
  return cost;
}

static int pick_unchosen(int c) {
  for (int tries = 0; tries < 100000; tries++) {
    int p = irand(nitems);
    if (!flag[p] && itemc[p] == c) return p;
  }
  return -1;
}

/* propose a move in place; returns 0 if none possible. old[] receives the previous chosen list */
static int propose(int *old, int *oldn) {
  *oldn = nsel; memcpy(old, chosen, sizeof(int) * nsel);
  int c1 = 0, c2 = 0, u1 = 0, u2 = 0;
  for (int p = 0; p < nsel; p++) { if (itemc[chosen[p]] == 1) c1++; else c2++; }
  for (int p = 0; p < nitems; p++) if (!flag[p]) { if (itemc[p] == 1) u1++; else u2++; }
  int feas[3], nf = 0;
  if (nsel > 0) feas[nf++] = 0;            /* swap same size */
  if (c2 > 0 && u1 >= 2) feas[nf++] = 1;   /* split */
  if (c1 >= 2 && u2 >= 1) feas[nf++] = 2;  /* merge */
  if (nf == 0) return 0;
  int mt = feas[irand(nf)];
  if (mt == 0) {
    int q = irand(nsel); int c = itemc[chosen[q]];
    int j = pick_unchosen(c); if (j < 0) return 0;
    flag[chosen[q]] = 0; chosen[q] = j; flag[j] = 1;
  } else if (mt == 1) {
    int q; do { q = irand(nsel); } while (itemc[chosen[q]] != 2);
    int a = pick_unchosen(1); if (a < 0) return 0;
    flag[a] = 1;
    int b = -1; for (int tries = 0; tries < 100000 && b < 0; tries++) { int p = irand(nitems); if (!flag[p] && itemc[p] == 1) b = p; }
    if (b < 0) { flag[a] = 0; return 0; }
    flag[chosen[q]] = 0; chosen[q] = a; chosen[nsel++] = b; flag[b] = 1;
  } else {
    int q1, q2;
    do { q1 = irand(nsel); } while (itemc[chosen[q1]] != 1);
    do { q2 = irand(nsel); } while (itemc[chosen[q2]] != 1 || q2 == q1);
    int j = pick_unchosen(2); if (j < 0) return 0;
    int hi = q1 > q2 ? q1 : q2, lo = q1 < q2 ? q1 : q2;
    flag[chosen[q1]] = 0; flag[chosen[q2]] = 0;
    chosen[lo] = j; chosen[hi] = chosen[--nsel]; flag[j] = 1;
  }
  return 1;
}

static void undo(const int *old, int oldn) {
  for (int p = 0; p < nsel; p++) flag[chosen[p]] = 0;
  nsel = oldn; memcpy(chosen, old, sizeof(int) * oldn);
  for (int p = 0; p < nsel; p++) flag[chosen[p]] = 1;
}

static int init_state(void) {
  for (int tries = 0; tries < 2000; tries++) {
    for (int p = 0; p < nitems; p++) flag[p] = 0;
    nsel = 0; int sum = 0;
    int *perm = malloc(sizeof(int) * nitems);
    for (int p = 0; p < nitems; p++) perm[p] = p;
    for (int p = nitems - 1; p > 0; p--) { int q = irand(p + 1); int t = perm[p]; perm[p] = perm[q]; perm[q] = t; }
    for (int r = 0; r < nitems && sum < DEG; r++) {
      int p = perm[r];
      if (sum + itemc[p] <= DEG && irand(3) > 0) { chosen[nsel++] = p; flag[p] = 1; sum += itemc[p]; }
    }
    free(perm);
    if (sum == DEG) return 1;
    for (int p = 0; p < nitems; p++) flag[p] = 0;
    nsel = 0;
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: bsa GROUPFILE SECS STEPS RESTARTS SEED OUTPREFIX\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); if (!f) { perror("group"); return 1; }
  if (fscanf(f, "%d %d", &N, &E) != 2) return 1;
  mul = malloc(sizeof(int) * N * N); inv = malloc(sizeof(int) * N);
  for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 1;
  fclose(f);
  double secs = atof(argv[2]); long steps = atol(argv[3]); int restarts = atoi(argv[4]);
  rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)atoll(argv[5]) * 2654435761ULL); if (!rs) rs = 1;
  const char *outp = argv[6];
  for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul[x * N + y] == E) inv[x] = y;
  int *inv_list = malloc(sizeof(int) * N), ni = 0;
  for (int t = 0; t < N; t++) if (t != E && mul[t * N + t] == E) inv_list[ni++] = t;
  /* conjugacy classes of involutions */
  int *cls = malloc(sizeof(int) * N); for (int t = 0; t < N; t++) cls[t] = -1;
  int *reps = malloc(sizeof(int) * N), nreps = 0;
  for (int a = 0; a < ni; a++) {
    int t = inv_list[a]; if (cls[t] >= 0) continue;
    reps[nreps] = t;
    for (int g = 0; g < N; g++) cls[mul[mul[g * N + t] * N + inv[g]]] = nreps;
    nreps++;
  }
  Lc = malloc(sizeof(int) * N); Rc = malloc(sizeof(int) * N); repL = malloc(sizeof(int) * N); repR = malloc(sizeof(int) * N);
  dcl = malloc(sizeof(int) * N); dcstart = malloc(sizeof(int) * N); dcsz = malloc(sizeof(int) * N); dcel = malloc(sizeof(int) * N);
  items = malloc(sizeof(int) * N); itemc = malloc(sizeof(int) * N); flag = malloc(sizeof(int) * N);
  adj = malloc(sizeof(int) * N * DEG); mark = calloc(N + 4, sizeof(uint64_t));
  dist = malloc(sizeof(int) * N); bq = malloc(sizeof(int) * N);
  int *bestS = NULL; int bestcost = 1 << 30; int best_h = -1, best_k = -1; int bestn = 0;
  int bestadj_ok = 0; int *bestadj = malloc(sizeof(int) * N * DEG); int bestnL = 0;
  clock_t t0 = clock(); long evals = 0; int found = 0; int pairs = 0;
  int bestsel[8], bestseln = 0;
  for (int r = 0; r < nreps && !found; r++) {
    int h = reps[r];
    /* shuffle the K list */
    for (int a = ni - 1; a > 0; a--) { int q = irand(a + 1); int t = inv_list[a]; inv_list[a] = inv_list[q]; inv_list[q] = t; }
    for (int a = 0; a < ni && !found; a++) {
      if ((double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
      int k = inv_list[a];
      int ni2 = build_pair(h, k);
      if (ni2 == 0) continue;
      pairs++;
      for (int rs_i = 0; rs_i < restarts && !found; rs_i++) {
        if (!init_state()) break;
        int cost = evaluate(); evals++;
        if (cost < 0) break;
        int old[8], oldn;
        for (long st = 0; st < steps; st++) {
          double T = 2.0 * pow(0.1 / 2.0, (double)st / (double)steps);
          if (!propose(old, &oldn)) continue;
          int nc = evaluate(); evals++;
          if (nc < 0) { undo(old, oldn); continue; }
          if (nc <= cost || urand() < exp(-(nc - cost) / T)) {
            cost = nc;
            if (cost < bestcost) {
              bestcost = cost; best_h = h; best_k = k; bestn = nL;
              bestseln = nsel; memcpy(bestsel, chosen, sizeof(int) * nsel);
              for (int p = 0; p < nsel; p++) bestsel[p] = bestsel[p]; 
              /* store the group-level pair and the S elements */
              if (bestS == NULL) bestS = malloc(sizeof(int) * N);
              int ns = 0;
              for (int p = 0; p < nsel; p++) { int lab = items[chosen[p]]; for (int t = dcstart[lab]; t < dcstart[lab] + dcsz[lab]; t++) bestS[ns++] = dcel[t]; }
              bestnL = nL;
              (void)bestadj_ok;
              memcpy(bestadj, adj, sizeof(int) * N * DEG);
            }
            if (cost == 0) { found = 1; break; }
          } else undo(old, oldn);
        }
      }
    }
  }
  double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
  printf("RESULT N=%d best_cost=%d n_vertices=%d H=%d K=%d pairs=%d evals=%ld found=%d time=%.1fs\n",
         N, bestcost, N, best_h, best_k, pairs, evals, found, el);
  if (bestcost < (1 << 30)) {
    char fn[600]; snprintf(fn, sizeof fn, "%s.edges", outp);
    FILE *fo = fopen(fn, "w");
    int V = bestnL * 2;
    fprintf(fo, "%d\n", V);
    for (int i = 0; i < bestnL; i++) for (int d = 0; d < DEG; d++) fprintf(fo, "%d %d\n", i, bestadj[i * DEG + d]);
    fclose(fo);
    printf("WROTE %s cost=%d\n", fn, bestcost);
  }
  return 0;
}
