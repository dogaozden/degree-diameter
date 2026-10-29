/* bicoset.c: exhaustive / sampled search over bi-coset graphs (card c8).
 *
 * G finite (mult table from gap_tab.g), H, K subgroups of order h (H up to conjugacy, K arbitrary).
 * Vertices: left = H\G (cosets Hx), right = K\G (cosets Ky). Edge (Hx, Ky) iff x y^-1 in S, where S is a union of
 * double cosets HgK. Well defined since S is H-left and K-right invariant. Degree = |S|/h. Each double coset HgK
 * contributes c = |HgK|/h to the degree; we choose item sets with total contribution DEG.
 * G acts by right multiplication, so diameter = max(ecc(H), ecc(K)) of the two base vertices.
 * cost = number of vertices at distance > DIAM (or unreached) from the two base vertices, summed.
 *
 * usage: bicoset GROUPFILE h DEG SECS MAXCAND SEED [OUTEDGES]
 * GROUPFILE: first line "N e" (e = identity index), then N rows, row g col k = index of g*k.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define DIAM 5
static int N, E, *mul, *inv, W, H_ORD, DEG;
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

typedef struct { int el[64]; uint64_t *bits; } Sub;
static Sub *subs; static int nsubs = 0, capsubs = 0;

static int find_sub(uint64_t *bits) {
  for (int i = 0; i < nsubs; i++) if (memcmp(subs[i].bits, bits, W * 8) == 0) return i;
  return -1;
}
/* closure of gens (k of them) inside G; returns size, or -1 if it exceeds H_ORD */
static int closure(const int *gens, int k, int *mem, uint64_t *bits) {
  memset(bits, 0, W * 8);
  int sz = 0;
  mem[sz++] = E; bits[E >> 6] |= 1ULL << (E & 63);
  for (int p = 0; p < sz; p++) {
    for (int t = 0; t < k; t++) {
      int y = mul[mem[p] * N + gens[t]];
      if (!(bits[y >> 6] >> (y & 63) & 1)) {
        if (sz >= H_ORD) return -1;
        bits[y >> 6] |= 1ULL << (y & 63); mem[sz++] = y;
      }
    }
  }
  return sz;
}
static void gen_subgroups(void) {
  int mem[64]; uint64_t *bits = calloc(W, 8);
  for (int a = 0; a < N; a++) for (int b = a; b < N; b++) {
    int gens[2] = {a, b};
    int k = (a == b) ? 1 : 2;
    int sz = closure(gens, k, mem, bits);
    if (sz != H_ORD) continue;
    if (find_sub(bits) >= 0) continue;
    if (nsubs == capsubs) { capsubs = capsubs ? 2 * capsubs : 64; subs = realloc(subs, capsubs * sizeof(Sub)); }
    subs[nsubs].bits = malloc(W * 8); memcpy(subs[nsubs].bits, bits, W * 8);
    memcpy(subs[nsubs].el, mem, sz * sizeof(int));
    nsubs++;
  }
  free(bits);
}

static int *dcl, *dcsz, *dcstart, *dcel, *dcrep;   /* double cosets */
static int *Lc, *Rc, *repL, *repR, nL, nR;

static uint64_t bestcost_dummy;
static long long evaluated = 0;
static int best_cost = 1 << 30;
static char best_desc[512];
static int found = 0;
static const char *outedges = NULL;
static int *chosen; static int nchosen;
static int *items, nitems, *itemc;   /* item -> double coset label, contribution */
static unsigned long long fcnt[2100][16];
static int Hidx, Kidx;
static int *Hel, *Kel;
static int n_vertices_half;
static int adj[2 * 1024][8];
static int badj[2 * 1024][8];
static int deg_ok;
static clock_t t_start; static double secs_limit;
static int stop_now = 0;

static void evaluate(void) {
  /* S elements */
  static int Sel[256]; int ns = 0;
  for (int c = 0; c < nchosen; c++) {
    int lab = items[chosen[c]];
    for (int t = dcstart[lab]; t < dcstart[lab] + dcsz[lab]; t++) Sel[ns++] = dcel[t];
  }
  int n = nL; int V = nL + nR;
  deg_ok = 1;
  /* left adjacency: left i (rep x) -> right Rc[s^-1 x] */
  for (int i = 0; i < nL; i++) {
    int x = repL[i]; int cnt = 0;
    for (int s = 0; s < ns; s++) {
      int y = mul[inv[Sel[s]] * N + x];
      int j = Rc[y];
      int dup = 0;
      for (int q = 0; q < cnt; q++) if (adj[i][q] == n + j) { dup = 1; break; }
      if (!dup) { if (cnt >= DEG) { deg_ok = 0; break; } adj[i][cnt++] = n + j; }
    }
    if (cnt != DEG) deg_ok = 0;
  }
  for (int j = 0; j < nR; j++) {
    int y = repR[j]; int cnt = 0;
    for (int s = 0; s < ns; s++) {
      int x = mul[Sel[s] * N + y];
      int i = Lc[x];
      int dup = 0;
      for (int q = 0; q < cnt; q++) if (adj[n + j][q] == i) { dup = 1; break; }
      if (!dup) { if (cnt >= DEG) { deg_ok = 0; break; } adj[n + j][cnt++] = i; }
    }
    if (cnt != DEG) deg_ok = 0;
  }
  if (!deg_ok) { fprintf(stderr, "degree error\n"); exit(2); }
  /* BFS depth-limited from the two base vertices (left: coset of E, right: coset of E) */
  int cost = 0;
  int bases[2] = { Lc[E], n + Rc[E] };
  static int dist[2 * 1024], q[2 * 1024];
  for (int b = 0; b < 2; b++) {
    for (int v = 0; v < V; v++) dist[v] = -1;
    int h = 0, t = 0; q[t++] = bases[b]; dist[bases[b]] = 0;
    while (h < t) {
      int v = q[h++];
      if (dist[v] >= DIAM) continue;
      for (int d = 0; d < DEG; d++) { int w = adj[v][d]; if (dist[w] < 0) { dist[w] = dist[v] + 1; q[t++] = w; } }
    }
    for (int v = 0; v < V; v++) if (dist[v] < 0) cost++;
  }
  evaluated++;
  if (cost < best_cost) {
    best_cost = cost;
    memcpy(badj, adj, sizeof adj);
    snprintf(best_desc, sizeof best_desc, "H=%d K=%d n=%d items:", Hidx, Kidx, n);
    for (int c = 0; c < nchosen; c++) { char b[32]; snprintf(b, 32, " %d(c%d)", items[chosen[c]], itemc[chosen[c]]); strncat(best_desc, b, 511 - strlen(best_desc)); }
  }
  if (cost == 0 && !found) {
    found = 1;
    printf("VALID cost 0 n=%d vertices=%d H=%d K=%d\n", n, 2 * n, Hidx, Kidx);
    if (outedges) {
      FILE *f = fopen(outedges, "w");
      fprintf(f, "%d\n", 2 * n);
      for (int i = 0; i < nL; i++) for (int d = 0; d < DEG; d++) if (adj[i][d] > i) fprintf(f, "%d %d\n", i, adj[i][d]);
      fclose(f);
    }
    stop_now = 1;
  }
}

static void rec(int i, int s) {
  if (stop_now) return;
  if (s == 0) { evaluate(); return; }
  if (i == nitems) return;
  if (fcnt[i][s] == 0) return;
  if (s >= itemc[i] && fcnt[i + 1][s - itemc[i]] > 0) {
    chosen[nchosen++] = i; rec(i + 1, s - itemc[i]); nchosen--;
    if (stop_now) return;
  }
  if (fcnt[i + 1][s] > 0) rec(i + 1, s);
}

static void sample_one(void) {
  nchosen = 0; int s = DEG;
  for (int i = 0; i < nitems && s > 0; i++) {
    double pin = 0.0;
    if (s >= itemc[i] && fcnt[i + 1][s - itemc[i]] > 0) {
      pin = (double)fcnt[i + 1][s - itemc[i]] / (double)fcnt[i][s];
    }
    double u = (double)(rnd() >> 11) / 9007199254740992.0;
    if (u < pin) { chosen[nchosen++] = i; s -= itemc[i]; }
  }
  if (s == 0) evaluate();
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: bicoset GROUPFILE h DEG SECS MAXCAND SEED [OUTEDGES]\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); if (!f) { perror("group"); return 1; }
  if (fscanf(f, "%d %d", &N, &E) != 2) return 1;
  mul = malloc(sizeof(int) * N * N); inv = malloc(sizeof(int) * N);
  for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 1;
  fclose(f);
  H_ORD = atoi(argv[2]); DEG = atoi(argv[3]); secs_limit = atof(argv[4]);
  long long MAXC = atoll(argv[5]); rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[6]) * 2654435761ULL; if (!rs) rs = 1;
  if (argc > 7) outedges = argv[7];
  for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul[x * N + y] == E) inv[x] = y;
  W = (N + 63) / 64;
  t_start = clock();
  gen_subgroups();
  /* conjugacy classes of subgroups */
  int *rep = calloc(nsubs, sizeof(int)); int nreps = 0; char *vis = calloc(nsubs, 1);
  for (int i = 0; i < nsubs; i++) if (!vis[i]) {
    rep[nreps++] = i; vis[i] = 1;
    for (int g = 0; g < N; g++) {
      uint64_t *bits = calloc(W, 8); int ok = 1;
      for (int t = 0; t < H_ORD; t++) { int x = subs[i].el[t]; int y = mul[mul[g * N + x] * N + inv[g]]; bits[y >> 6] |= 1ULL << (y & 63); }
      int j = find_sub(bits); if (j < 0) ok = 0;
      if (ok) vis[j] = 1;
      free(bits);
    }
  }
  n_vertices_half = N / H_ORD;
  Lc = malloc(sizeof(int) * N); Rc = malloc(sizeof(int) * N);
  repL = malloc(sizeof(int) * N); repR = malloc(sizeof(int) * N);
  dcl = malloc(sizeof(int) * N); dcsz = malloc(sizeof(int) * N); dcstart = malloc(sizeof(int) * N);
  dcel = malloc(sizeof(int) * N * 2); items = malloc(sizeof(int) * N); itemc = malloc(sizeof(int) * N);
  chosen = malloc(sizeof(int) * N); Hel = malloc(sizeof(int) * N); Kel = malloc(sizeof(int) * N);
  long long pairs = 0; int any_items = 0;
  for (int r = 0; r < nreps && !stop_now; r++) {
    Hidx = rep[r];
    memcpy(Hel, subs[Hidx].el, H_ORD * sizeof(int));
    { int cen = 1; for (int g = 0; g < N; g++) if (mul[mul[g * N + Hel[1]] * N + inv[g]] != Hel[1]) { cen = 0; break; }
      if (cen) { printf("SKIP central H (Haar case) N=%d\n", N); continue; } }
    /* K = H only: every K conjugate to H gives an isomorphic graph (S -> Sg), and K not conjugate to H gives even degree */
    for (int k = Hidx; k == Hidx && !stop_now; k++) {
      if ((double)(clock() - t_start) / CLOCKS_PER_SEC > secs_limit) { stop_now = 1; break; }
      Kidx = k; memcpy(Kel, subs[k].el, H_ORD * sizeof(int));
      /* left cosets Hx and right cosets Ky */
      for (int g = 0; g < N; g++) { Lc[g] = -1; Rc[g] = -1; }
      nL = 0; nR = 0;
      for (int g = 0; g < N; g++) {
        if (Lc[g] < 0) { for (int t = 0; t < H_ORD; t++) Lc[mul[Hel[t] * N + g]] = nL; repL[nL++] = g; }
        if (Rc[g] < 0) { for (int t = 0; t < H_ORD; t++) Rc[mul[Kel[t] * N + g]] = nR; repR[nR++] = g; }
      }
      /* double cosets HgK */
      for (int g = 0; g < N; g++) dcl[g] = -1;
      int ndc = 0; int pos = 0;
      for (int g = 0; g < N; g++) if (dcl[g] < 0) {
        int lab = ndc++; dcstart[lab] = pos; int cnt = 0;
        for (int a = 0; a < H_ORD; a++) for (int b = 0; b < H_ORD; b++) {
          int y = mul[mul[Hel[a] * N + g] * N + Kel[b]];
          if (dcl[y] < 0) { dcl[y] = lab; dcel[pos++] = y; cnt++; }
        }
        dcsz[lab] = cnt;
      }
      /* items: double cosets with contribution c = |HgK|/h in 1..DEG */
      nitems = 0;
      for (int lab = 0; lab < ndc; lab++) {
        int c = dcsz[lab] / H_ORD;
        if (dcsz[lab] % H_ORD) { fprintf(stderr, "bad size\n"); return 3; }
        if (c >= 1 && c <= DEG) { items[nitems] = lab; itemc[nitems] = c; nitems++; }
      }
      /* counts f[i][s] = number of subsets of items[i..] with contribution sum s */
      memset(fcnt, 0, sizeof fcnt);
      fcnt[nitems][0] = 1;
      for (int i = nitems - 1; i >= 0; i--) for (int s = 0; s <= DEG; s++) {
        fcnt[i][s] = fcnt[i + 1][s] + ((s >= itemc[i]) ? fcnt[i + 1][s - itemc[i]] : 0);
        if (fcnt[i][s] > 1000000000000000ULL) fcnt[i][s] = 1000000000000000ULL;
      }
      pairs++;
      { int nN = 0; for (int g = 0; g < N; g++) { int y = mul[mul[g * N + Hel[1]] * N + inv[g]]; if (y == Hel[1]) nN++; }
        printf("CLASS Hidx=%d |N(H)|=%d items=%d S_count_deg%d=%llu\n", Hidx, nN, nitems, DEG, (unsigned long long)fcnt[0][DEG]); }
      if (fcnt[0][DEG] == 0) continue;
      any_items = 1;
      /* dcel is indexed by dcstart: rebuild start positions are already consistent (pos ascending by label) */
      if (fcnt[0][DEG] <= (unsigned long long)MAXC) { nchosen = 0; rec(0, DEG); }
      else { for (long long t = 0; t < MAXC && !stop_now; t++) sample_one(); }
    }
  }
  double el = (double)(clock() - t_start) / CLOCKS_PER_SEC;
  printf("GROUP %s N=%d h=%d n=%d subgroups=%d Hclasses=%d pairs=%lld evaluated=%lld best_cost=%d found=%d time=%.1fs\n",
         argv[1], N, H_ORD, n_vertices_half, nsubs, nreps, pairs, evaluated, best_cost, found, el);
  printf("BEST %s\n", best_desc);
  if (outedges && !found && best_cost < (1 << 30)) {
    char fn[600]; snprintf(fn, sizeof fn, "%s.best", outedges);
    FILE *fo = fopen(fn, "w"); fprintf(fo, "%d\n", 2 * n_vertices_half);
    for (int i = 0; i < n_vertices_half; i++) for (int d = 0; d < DEG; d++) if (badj[i][d] > i) fprintf(fo, "%d %d\n", i, badj[i][d]);
    fclose(fo);
  }
  (void)any_items;
  return found ? 0 : 0;
}
