/* delete-and-rematch for cubic bipartite graphs, diameter D (=7). Usage:
   dr ex1 EDGES OUT                     exhaustive k=1 (delete one white + one black, all rematchings)
   dr sa EDGES OUT k secs seed T0 T1 pmix  annealing over (deleted set, cubic rematch)            */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXN 200
#define WB 4
#define D 7
#define DEG 3
typedef uint64_t u64;
int n0, E0[MAXN][3], E0d[MAXN], side[MAXN];
int pres[MAXN], nbr[MAXN][8], dg[MAXN];
unsigned char gm[MAXN][MAXN];
int farv[MAXN];
static u64 rs = 88172645463325252ULL;
static inline u64 rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int m){ return (int)(rnd() % (u64)m); }

void add_edge(int a, int b){ nbr[a][dg[a]++] = b; nbr[b][dg[b]++] = a; gm[a][b] = gm[b][a] = 1; }
void del_edge(int a, int b){
  for (int i = 0; i < dg[a]; i++) if (nbr[a][i] == b) { nbr[a][i] = nbr[a][--dg[a]]; break; }
  for (int i = 0; i < dg[b]; i++) if (nbr[b][i] == a) { nbr[b][i] = nbr[b][--dg[b]]; break; }
  gm[a][b] = gm[b][a] = 0;
}
void build_from_E0(void){
  memset(dg, 0, sizeof dg); memset(gm, 0, sizeof gm);
  for (int u = 0; u < n0; u++) if (pres[u])
    for (int i = 0; i < E0d[u]; i++) { int v = E0[u][i]; if (v > u && pres[v]) add_edge(u, v); }
}
/* exact ball-of-radius-D bitsets; returns far unordered pairs; farv[v] = #vertices at dist > D from v */
int eval(void){
  static u64 A[MAXN][WB], B[MAXN][WB];
  u64 (*cur)[WB] = A, (*nxt)[WB] = B;
  int P = 0;
  for (int v = 0; v < n0; v++) if (pres[v]) {
    P++; memset(cur[v], 0, sizeof cur[v]); cur[v][v >> 6] |= 1ULL << (v & 63);
  }
  for (int s = 0; s < D; s++) {
    for (int v = 0; v < n0; v++) if (pres[v]) {
      for (int w = 0; w < WB; w++) nxt[v][w] = cur[v][w];
      for (int i = 0; i < dg[v]; i++) { int x = nbr[v][i];
        for (int w = 0; w < WB; w++) nxt[v][w] |= cur[x][w]; }
    }
    u64 (*t)[WB] = cur; cur = nxt; nxt = t;
  }
  int f2 = 0;
  for (int v = 0; v < n0; v++) if (pres[v]) {
    int c = 0; for (int w = 0; w < WB; w++) c += __builtin_popcountll(cur[v][w]);
    farv[v] = P - c; f2 += farv[v];
  }
  return f2 / 2;
}
/* augment: give every present vertex with dg<3 its missing edges (simple, bipartite), along alternating paths */
int repair(void){
  static int par[MAXN], vis[MAXN], q[MAXN];
  for (;;) {
    int any = 0;
    for (int v = 0; v < n0; v++) if (pres[v]) { if (dg[v] > DEG) return 0; if (dg[v] < DEG) any = 1; }
    if (!any) return 1;
    memset(vis, 0, sizeof vis); int qh = 0, qt = 0, found = -1;
    int off = rndi(n0);
    for (int k = 0; k < n0; k++) { int v = (k + off) % n0;
      if (pres[v] && side[v] == 0 && dg[v] < DEG) { vis[v] = 1; par[v] = -1; q[qt++] = v; } }
    while (qh < qt && found < 0) {
      int u = q[qh++];
      if (side[u] == 0) {
        int o2 = rndi(n0);
        for (int k = 0; k < n0; k++) { int b = (k + o2) % n0;
          if (!pres[b] || side[b] != 1 || vis[b] || gm[u][b]) continue;
          vis[b] = 1; par[b] = u;
          if (dg[b] < DEG) { found = b; break; }
          q[qt++] = b;
        }
      } else {
        for (int i = 0; i < dg[u]; i++) { int w = nbr[u][i];
          if (!vis[w]) { vis[w] = 1; par[w] = u; q[qt++] = w; } }
      }
    }
    if (found < 0) return 0;
    int cur = found;
    while (par[cur] != -1) {
      int p = par[cur];
      if (side[cur] == 1) add_edge(p, cur); else del_edge(cur, p);
      cur = p;
    }
  }
}
void write_graph(const char *fn){
  int id[MAXN], n = 0;
  for (int v = 0; v < n0; v++) id[v] = pres[v] ? n++ : -1;
  FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", n);
  for (int u = 0; u < n0; u++) if (pres[u]) for (int i = 0; i < dg[u]; i++) { int v = nbr[u][i];
    if (v > u) fprintf(f, "%d %d\n", id[u], id[v]); }
  fclose(f);
}
/* ---- exhaustive k=1 ---- */
int wl[16], bl[16], nw, nbk, used[16];
int bestc = 1 << 30; char bestfn[512]; long leaves = 0;
void enum_rec(int i){
  if (i == nw) { int c = eval(); leaves++;
    if (c < bestc) { bestc = c; write_graph(bestfn); }
    return; }
  int w = wl[i];
  for (int j = 0; j < nbk; j++) { if (used[j]) continue; int b = bl[j]; if (gm[w][b]) continue;
    used[j] = 1; add_edge(w, b); enum_rec(i + 1); del_edge(w, b); used[j] = 0; }
}
/* ---- state save/restore ---- */
typedef struct { int pres[MAXN], nbr[MAXN][8], dg[MAXN], farv[MAXN]; unsigned char gm[MAXN][MAXN]; } St;
St sv;
void save(void){ memcpy(sv.pres, pres, sizeof pres); memcpy(sv.nbr, nbr, sizeof nbr); memcpy(sv.dg, dg, sizeof dg);
  memcpy(sv.farv, farv, sizeof farv); memcpy(sv.gm, gm, sizeof gm); }
void restore(void){ memcpy(pres, sv.pres, sizeof pres); memcpy(nbr, sv.nbr, sizeof nbr); memcpy(dg, sv.dg, sizeof dg);
  memcpy(farv, sv.farv, sizeof farv); memcpy(gm, sv.gm, sizeof gm); }

int move_2sw(void){
  int ws[MAXN], nws = 0;
  for (int v = 0; v < n0; v++) if (pres[v] && side[v] == 0 && dg[v] > 0) ws[nws++] = v;
  for (int tr = 0; tr < 20; tr++) {
    int a = ws[rndi(nws)], c = ws[rndi(nws)];
    if (a == c) continue;
    int b = nbr[a][rndi(dg[a])], d = nbr[c][rndi(dg[c])];
    if (b == d || gm[a][d] || gm[c][b]) continue;
    del_edge(a, b); del_edge(c, d); add_edge(a, d); add_edge(c, b);
    return 1;
  }
  return 0;
}
int move_swap(void){
  int s = rndi(2);
  /* y: present on side s, prefer far vertices */
  int cand[MAXN], nc = 0, cf[MAXN], ncf = 0, absn[MAXN], na = 0;
  for (int v = 0; v < n0; v++) if (side[v] == s) {
    if (pres[v]) { cand[nc++] = v; if (farv[v] > 0) cf[ncf++] = v; } else absn[na++] = v; }
  if (na == 0) return 0;
  int y = (ncf > 0 && rndi(2) == 0) ? cf[rndi(ncf)] : cand[rndi(nc)];
  int x = absn[rndi(na)];
  while (dg[y] > 0) del_edge(y, nbr[y][0]);
  pres[y] = 0; pres[x] = 1;
  int t = 1 + rndi(3);
  for (int i = 0; i < t && dg[x] < DEG; i++) {
    int oc[MAXN], no = 0;
    for (int v = 0; v < n0; v++) if (pres[v] && side[v] != s && !gm[x][v]) oc[no++] = v;
    if (!no) break;
    int c = oc[rndi(no)];
    add_edge(x, c);
    if (dg[c] > DEG) { int d; do { d = nbr[c][rndi(dg[c])]; } while (d == x); del_edge(c, d); }
  }
  return repair();
}
int main(int argc, char **argv){
  if (argc < 4) { fprintf(stderr, "usage\n"); return 1; }
  FILE *f = fopen(argv[2], "r"); int n; if (fscanf(f, "%d", &n) != 1) return 1; n0 = n;
  int u, v; memset(E0d, 0, sizeof E0d);
  while (fscanf(f, "%d %d", &u, &v) == 2) { E0[u][E0d[u]++] = v; E0[v][E0d[v]++] = u; }
  fclose(f);
  for (int i = 0; i < n0; i++) side[i] = -1;
  side[0] = 0; int q[MAXN], qh = 0, qt = 0; q[qt++] = 0;
  while (qh < qt) { int x = q[qh++]; for (int i = 0; i < E0d[x]; i++) { int y = E0[x][i];
    if (side[y] < 0) { side[y] = 1 - side[x]; q[qt++] = y; } } }
  for (int i = 0; i < n0; i++) pres[i] = 1;
  if (!strcmp(argv[1], "ex1")) {
    strcpy(bestfn, argv[3]);
    for (int w = 0; w < n0; w++) if (side[w] == 0) for (int b = 0; b < n0; b++) if (side[b] == 1) {
      for (int i = 0; i < n0; i++) pres[i] = 1;
      pres[w] = pres[b] = 0; build_from_E0();
      nw = nbk = 0;
      for (int x = 0; x < n0; x++) if (pres[x]) {
        for (int r = dg[x]; r < DEG; r++) { if (side[x] == 0) wl[nw++] = x; else bl[nbk++] = x; } }
      if (nw != nbk) { fprintf(stderr, "unbalanced\n"); return 1; }
      /* sort so that whites are enumerated from the list; blacks are the slot list */
      for (int j = 0; j < nbk; j++) used[j] = 0;
      enum_rec(0);
      /* restore: nothing (build_from_E0 rebuilds) */
    }
    printf("ex1 leaves=%ld best_far=%d file=%s\n", leaves, bestc, bestfn);
    return 0;
  }
  if (!strcmp(argv[1], "sa")) {
    int k = atoi(argv[4]); double secs = atof(argv[5]); rs ^= (u64)atoll(argv[6]) * 2654435761ULL + 1;
    double T0 = atof(argv[7]), T1 = atof(argv[8]); int pmix = atoi(argv[9]);
    for (int i = 0; i < 20; i++) rnd();
    int ok = 0;
    while (!ok) {
      for (int i = 0; i < n0; i++) pres[i] = 1;
      int dw = 0, db = 0;
      while (dw < k) { int x = rndi(n0); if (side[x] == 0 && pres[x]) { pres[x] = 0; dw++; } }
      while (db < k) { int x = rndi(n0); if (side[x] == 1 && pres[x]) { pres[x] = 0; db++; } }
      build_from_E0();
      ok = repair();
    }
    int cost = eval(), best = cost; char bfn[512]; strcpy(bfn, argv[3]);
    write_graph(bfn); /* placeholder for best so far */
    int bestmark = cost;
    clock_t t0 = clock(); double el = 0;
    long it = 0;
    /* keep best state's graph in file: write when improved */
    int bestc2 = cost;
    while (1) {
      el = (double)(clock() - t0) / CLOCKS_PER_SEC;
      if (el > secs || bestc2 == 0) break;
      double fr = el / secs; double T = T0 * pow(T1 / T0, fr);
      save();
      int ok2 = (rndi(100) < pmix) ? move_2sw() : move_swap();
      if (!ok2 || !repair()) { restore(); it++; continue; }
      int nc = eval();
      if (nc <= cost || exp((cost - nc) / T) > (rnd() % 1000000) / 1e6) {
        cost = nc;
        if (cost < bestc2) { bestc2 = cost; write_graph(bfn); }
      } else restore();
      it++;
    }
    int nv = 0; for (int i = 0; i < n0; i++) nv += pres[i];
    printf("sa k=%d iters=%ld best_far=%d final_far=%d n_final=%d file=%s\n", k, it, bestc2, cost, nv, bfn);
    (void)best; (void)bestmark;
    return 0;
  }
  return 1;
}
