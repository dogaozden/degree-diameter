/* qanneal.c -- anneal the Z_M2 voltages of a Z_M1 x Z_M2 voltage graph (liftdiam format) on the exact diameter cost.
 *
 * Intended for the quotient bases written by eqlift.py (C-equivariant lifts of H(q) + hops: the Z_M1 = C part of each
 * voltage is fixed by the geometry, the Z_M2 part is free).  Cost(F) = number of lift vertices not reached within D
 * steps from (s, 0), summed over the sources s in a focus set F (the group acts by translation, so the sources (s, 0),
 * s a base vertex, give the exact diameter).  When cost(F) = 0 a full check over all base sources runs and failing
 * sources join F (as in lanneal2.c).  Moves: new random Z_M2 voltage on an edge at base distance <= 1 from a failing
 * source of F (prob 0.8) or on a random edge.  Parallel darts with equal voltage (lift multi-edges) are forbidden.
 * qanneal2: moves are anchored at the failing source or at one of its failing targets (base vertices).
 * qanneal4: repair moves (a walk of length <= D from the source to a failing target copy with the right C-part;
 * one of its edges gets the Z-part that puts the walk on the target).
 * qanneal3: also swaps the targets (orbit, C-offset) of two hop edges of the same matching (prob PSWAP), for bases
 * written by eqlift.py (edges grouped per point orbit: DEG-2 flags, then hop 1, hop 2).
 * usage: qanneal3 base.txt D seconds T0 T1 seed threads out.txt F0 DEG PSWAP [J=2] [STEP=1: voltage moves keep b mod STEP] [PREP=0: probability of a repair move]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <pthread.h>

static int NB, M1, M2, M, E, D, NT, DEG = 0, JH = 2, STEP = 1; static double PREP = 0; static double PSWAP = 0;
static long long V;
static int *eu, *ev, *ea, *eb;
static int *adjstart, *adje; /* incident edge ids per base vertex */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* dart arrays for BFS (pull): for vertex v, darts to u with voltage (a,b) meaning (v,g) ~ (u, g + volt(v->u)) */
static int *dv, *da, *dbb;
static void build_darts(void) {
  int *fill = calloc(NB, sizeof(int));
  for (int v = 0; v < NB; v++) fill[v] = adjstart[v];
  for (int i = 0; i < E; i++) {
    int u = eu[i], v = ev[i];
    int p = fill[u]++; dv[p] = v; da[p] = ea[i]; dbb[p] = eb[i];
    p = fill[v]++; dv[p] = u; da[p] = (M1 - ea[i]) % M1; dbb[p] = (M2 - eb[i]) % M2;
  }
  free(fill);
}

typedef struct { const int *src; int ns; long long *per; int next; pthread_mutex_t mu; } job_t;
static long long *failt; /* failt[i*8+k]: failing target lift vertices of the i-th source of the last evaluation */
static void *worker(void *arg) {
  job_t *J = arg;
  uint64_t *vis = malloc(8 * V), *fr = malloc(8 * V), *nx = malloc(8 * V);
  for (;;) {
    pthread_mutex_lock(&J->mu); int b = J->next++; pthread_mutex_unlock(&J->mu);
    int s0 = b * 64; if (s0 >= J->ns) break;
    int s1 = s0 + 64; if (s1 > J->ns) s1 = J->ns; int nb = s1 - s0;
    uint64_t full = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
    memset(vis, 0, 8 * V); memset(fr, 0, 8 * V);
    for (int i = 0; i < nb; i++) { long long w = (long long)J->src[s0 + i] * M; fr[w] |= 1ULL << i; vis[w] |= 1ULL << i; }
    for (int level = 0; level < D; level++) {
      for (int v = 0; v < NB; v++) {
        uint64_t *nxv = nx + (long long)v * M; memset(nxv, 0, 8 * M);
        for (int e = adjstart[v]; e < adjstart[v + 1]; e++) {
          int u = dv[e], a = da[e], bb = dbb[e]; uint64_t *fru = fr + (long long)u * M;
          for (int g1 = 0; g1 < M1; g1++) {
            int h1 = g1 + a; if (h1 >= M1) h1 -= M1;
            uint64_t *dst = nxv + g1 * M2, *srcp = fru + h1 * M2; int k = M2 - bb;
            for (int g2 = 0; g2 < k; g2++) dst[g2] |= srcp[g2 + bb];
            for (int g2 = k; g2 < M2; g2++) dst[g2] |= srcp[g2 + bb - M2];
          }
        }
        uint64_t *visv = vis + (long long)v * M;
        for (int g = 0; g < M; g++) { uint64_t m = nxv[g] & ~visv[g]; nxv[g] = m; visv[g] |= m; }
      }
      uint64_t *t = fr; fr = nx; nx = t;
    }
    long long cnt[64]; memset(cnt, 0, sizeof cnt);
    for (long long w = 0; w < V; w++) { uint64_t m = (~vis[w]) & full; while (m) { int i = __builtin_ctzll(m); long long c0 = cnt[i]++;
        if (c0 < 8) failt[(s0 + i) * 8 + c0] = w; else if (rnd() % (c0 + 1) < 8) failt[(s0 + i) * 8 + rnd() % 8] = w; m &= m - 1; } }
    for (int i = 0; i < nb; i++) J->per[s0 + i] = cnt[i];
  }
  free(vis); free(fr); free(nx);
  return NULL;
}
static long long evaluate(const int *src, int ns, long long *per) {
  build_darts();
  job_t J = { src, ns, per, 0, PTHREAD_MUTEX_INITIALIZER };
  int nt = NT; int nbat = (ns + 63) / 64; if (nt > nbat) nt = nbat;
  pthread_t th[64]; for (int t = 0; t < nt; t++) pthread_create(&th[t], NULL, worker, &J);
  for (int t = 0; t < nt; t++) pthread_join(th[t], NULL);
  long long s = 0; for (int i = 0; i < ns; i++) s += per[i]; return s;
}
/* would edge i with voltage (ea[i], b) duplicate a parallel dart? */
static int clashes(int i, int b) {
  int u = eu[i], v = ev[i];
  for (int k = adjstart[u]; k < adjstart[u + 1]; k++) { int e = adje[k]; if (e == i) continue;
    if (eu[e] == u && ev[e] == v && ea[e] == ea[i] && eb[e] == b) return 1;
    if (eu[e] == v && ev[e] == u && (ea[e] + ea[i]) % M1 == 0 && (eb[e] + b) % M2 == 0) return 1; }
  return 0;
}

/* ---- repair move: walks of length <= 7 from s to t with prescribed C-part, then fix one edge's Z-part ---- */
typedef struct { int v, c, z, len; int e[4]; signed char sg[4]; } st_t;
static st_t *FW, *BW; static int nFW, nBW, capFW = 0, capBW = 0;
static void grow(st_t **A, int *cap, int n) { if (n >= *cap) { *cap = *cap ? 2 * *cap : 4096; *A = realloc(*A, sizeof(st_t) * *cap); } }
/* enumerate walks from root of length <= maxlen; dart voltage of edge e traversed from its eu side is +, else - */
static void enumerate(int root, int maxlen, st_t **A, int *n, int *cap) {
  *n = 0; grow(A, cap, 0); st_t r = { root, 0, 0, 0, {0}, {0} }; (*A)[(*n)++] = r;
  for (int idx = 0; idx < *n; idx++) {
    st_t cur = (*A)[idx]; if (cur.len >= maxlen) continue;
    int v = cur.v;
    for (int k = adjstart[v]; k < adjstart[v + 1]; k++) {
      int e = adje[k]; if (cur.len > 0 && cur.e[cur.len - 1] == e) continue; /* no immediate backtrack */
      int sg = (eu[e] == v) ? 1 : -1; int w = sg > 0 ? ev[e] : eu[e];
      st_t nx = cur; nx.v = w; nx.c = ((cur.c + sg * ea[e]) % M1 + M1) % M1; nx.z = ((cur.z + sg * eb[e]) % M2 + M2) % M2;
      nx.e[cur.len] = e; nx.sg[cur.len] = (signed char)sg; nx.len = cur.len + 1;
      grow(A, cap, *n); (*A)[(*n)++] = nx;
    }
  }
}
/* pick a walk s -> t with C-sum g1 and set one of its edges so the Z-sum is g2; returns edge id or -1 (old in *oldb) */
static int repair(int s, long long wl, int *oldb) {
  int t = (int)(wl / M), g = (int)(wl % M), g1 = g / M2, g2 = g % M2;
  enumerate(s, 3, &FW, &nFW, &capFW); enumerate(t, 4, &BW, &nBW, &capBW);
  /* candidates: forward f ending at v, backward b ending at v; walk = f then reverse(b): c = f.c - b.c, z = f.z - b.z */
  int tries = 0;
  for (int rep = 0; rep < 2000; rep++) {
    st_t *b = &BW[rnd() % nBW];
    /* scan forward states with the same endpoint (linear scan over a random window) */
    int start = rnd() % nFW;
    for (int k = 0; k < nFW; k++) {
      st_t *f = &FW[(start + k) % nFW];
      if (f->v != b->v || f->len + b->len > D || f->len + b->len == 0) continue;
      if (((f->c - b->c) % M1 + M1) % M1 != g1) continue;
      int tot = f->len + b->len; int pick = rnd() % tot; int e, sg;
      if (pick < f->len) { e = f->e[pick]; sg = f->sg[pick]; } else { e = b->e[pick - f->len]; sg = -b->sg[pick - f->len]; }
      int zsum = ((f->z - b->z) % M2 + M2) % M2;
      int delta = ((g2 - zsum) % M2 + M2) % M2; if (delta == 0) return -1;
      int nb = ((eb[e] + sg * delta) % M2 + M2) % M2;
      if (STEP > 1 && (nb - eb[e]) % STEP != 0) { tries++; break; }
      if (clashes(e, nb)) { tries++; break; }
      *oldb = eb[e]; eb[e] = nb; return e;
    }
  }
  (void)tries; return -1;
}

static void save(const char *fn) {
  FILE *o = fopen(fn, "w"); fprintf(o, "%d %d %d %d\n", NB, M1, M2, E);
  for (int i = 0; i < E; i++) fprintf(o, "%d %d %d %d\n", eu[i], ev[i], ea[i], eb[i]);
  fclose(o);
}

int main(int argc, char **argv) {
  if (argc < 9) { fprintf(stderr, "usage: qanneal base.txt D seconds T0 T1 seed threads out.txt [F0]\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); D = atoi(argv[2]); double secs = atof(argv[3]), T0 = atof(argv[4]), T1 = atof(argv[5]);
  rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
  NT = atoi(argv[7]); const char *out = argv[8]; int F0 = argc > 9 ? atoi(argv[9]) : 64;
  if (argc > 11) { DEG = atoi(argv[10]); PSWAP = atof(argv[11]); } if (argc > 12) JH = atoi(argv[12]); if (argc > 13) STEP = atoi(argv[13]); if (argc > 14) PREP = atof(argv[14]);
  if (fscanf(f, "%d %d %d %d", &NB, &M1, &M2, &E) != 4) return 1;
  M = M1 * M2; V = (long long)NB * M;
  eu = malloc(4 * E); ev = malloc(4 * E); ea = malloc(4 * E); eb = malloc(4 * E);
  int *deg = calloc(NB, 4);
  for (int i = 0; i < E; i++) { if (fscanf(f, "%d %d %d %d", &eu[i], &ev[i], &ea[i], &eb[i]) != 4) return 1;
    ea[i] = ((ea[i] % M1) + M1) % M1; eb[i] = ((eb[i] % M2) + M2) % M2; deg[eu[i]]++; deg[ev[i]]++; }
  adjstart = malloc(4 * (NB + 1)); adjstart[0] = 0; for (int v = 0; v < NB; v++) adjstart[v + 1] = adjstart[v] + deg[v];
  adje = malloc(8 * E); dv = malloc(8 * E); da = malloc(8 * E); dbb = malloc(8 * E);
  int *fill = calloc(NB, 4);
  for (int i = 0; i < E; i++) { adje[adjstart[eu[i]] + fill[eu[i]]++] = i; adje[adjstart[ev[i]] + fill[ev[i]]++] = i; }
  for (int i = 0; i < E; i++) if (clashes(i, eb[i])) { int b; do b = (eb[i] + STEP * (int)(rnd() % (M2 / STEP))) % M2; while (clashes(i, b)); eb[i] = b; }
  int *all = malloc(4 * NB); for (int v = 0; v < NB; v++) all[v] = v;
  long long *perall = malloc(8 * NB), *perF = malloc(8 * NB);
  int *F = malloc(4 * NB), nF = 0; char *inF = calloc(NB, 1); failt = calloc(8 * (size_t)NB, 8);
  long long tot = evaluate(all, NB, perall);
  fprintf(stderr, "start full cost %lld\n", tot);
  long long best = tot; save(out);
  /* initial focus: worst sources first, then random */
  for (int r = 0; r < F0 && nF < NB; r++) { int w = -1; for (int v = 0; v < NB; v++) if (!inF[v] && perall[v] > 0 && (w < 0 || perall[v] > perall[w])) w = v;
    if (w < 0) { do w = rnd() % NB; while (inF[w]); } inF[w] = 1; F[nF++] = w; }
  long long c = evaluate(F, nF, perF);
  double t0 = now(); long long it = 0, acc = 0;
  while (now() - t0 < secs) {
    if (c == 0) {
      tot = evaluate(all, NB, perall);
      fprintf(stderr, "t %.0f it %lld full cost %lld |F| %d\n", now() - t0, it, tot, nF);
      if (tot < best) { best = tot; save(out); }
      if (tot == 0) break;
      for (int r = 0; r < 64; r++) { int w = -1; for (int v = 0; v < NB; v++) if (!inF[v] && perall[v] > 0 && (w < 0 || perall[v] > perall[w])) w = v;
        if (w < 0) break; inF[w] = 1; F[nF++] = w; }
      c = evaluate(F, nF, perF);
      continue;
    }
    it++;
    double frac = (now() - t0) / secs, T = T0 * pow(T1 / T0, frac);
    if (DEG > 0 && (double)(rnd() % 1000000) / 1e6 < PSWAP) {
      int h = DEG - JH + (int)(rnd() % JH);               /* which matching */
      int no = E / DEG;
      int o1 = rnd() % no, o2 = rnd() % no; if (o1 == o2) continue;
      int e1 = o1 * DEG + h, e2 = o2 * DEG + h;
      int nv1 = ev[e2], na1 = ea[e2], nv2 = ev[e1], na2 = ea[e1];
      int ok = 1;
      for (int t = 0; t < DEG && ok; t++) { if (t == h) continue;
        int f1 = o1 * DEG + t, f2 = o2 * DEG + t;
        if (ev[f1] == nv1 && ea[f1] == na1) ok = 0;
        if (ev[f2] == nv2 && ea[f2] == na2) ok = 0; }
      if (!ok) continue;
      int ov1 = ev[e1], oa1 = ea[e1], ov2 = ev[e2], oa2 = ea[e2];
      /* adjacency lists hold edge ids: update the line-side lists */
      int vA = ov1, vB = ov2;
      ev[e1] = nv1; ea[e1] = na1; ev[e2] = nv2; ea[e2] = na2;
      if (vA != vB) { for (int k = adjstart[vA]; k < adjstart[vA + 1]; k++) if (adje[k] == e1) { adje[k] = e2; break; }
                      for (int k = adjstart[vB]; k < adjstart[vB + 1]; k++) if (adje[k] == e2) { adje[k] = e1; break; } }
      long long *tmp = malloc(8 * nF); memcpy(tmp, perF, 8 * nF);
      long long c2 = evaluate(F, nF, perF);
      double T = T0 * pow(T1 / T0, (now() - t0) / secs);
      if (c2 <= c || (T > 0 && exp((double)(c - c2) / T) > (double)(rnd() % 1000000) / 1e6)) { c = c2; acc++; }
      else {
        ev[e1] = ov1; ea[e1] = oa1; ev[e2] = ov2; ea[e2] = oa2;
        if (vA != vB) { for (int k = adjstart[vA]; k < adjstart[vA + 1]; k++) if (adje[k] == e2) { adje[k] = e1; break; }
                        for (int k = adjstart[vB]; k < adjstart[vB + 1]; k++) if (adje[k] == e1) { adje[k] = e2; break; } }
        memcpy(perF, tmp, 8 * nF);
      }
      free(tmp); it++;
      continue;
    }
    if (PREP > 0 && (double)(rnd() % 1000000) / 1e6 < PREP) {
      int k; do k = rnd() % nF; while (perF[k] == 0);
      int nk = perF[k] < 8 ? (int)perF[k] : 8; long long wl = failt[k * 8 + rnd() % nk];
      int oldb, e = repair(F[k], wl, &oldb); if (e < 0) continue;
      long long *tmp = malloc(8 * nF); memcpy(tmp, perF, 8 * nF);
      long long *tmpf = malloc(8 * 8 * (size_t)nF); memcpy(tmpf, failt, 8 * 8 * (size_t)nF);
      long long c2 = evaluate(F, nF, perF);
      double T = T0 * pow(T1 / T0, (now() - t0) / secs);
      if (c2 <= c || (T > 0 && exp((double)(c - c2) / T) > (double)(rnd() % 1000000) / 1e6)) { c = c2; acc++; }
      else { eb[e] = oldb; memcpy(perF, tmp, 8 * nF); memcpy(failt, tmpf, 8 * 8 * (size_t)nF); }
      free(tmp); free(tmpf); it++;
      if (it % 200 == 0) fprintf(stderr, "t %.0f it %lld T %.3f focus cost %lld |F| %d acc %lld\n", now() - t0, it, T, c, nF, acc);
      continue;
    }
    int ei;
    if (rnd() % 10 < 8) {
      int k; do k = rnd() % nF; while (perF[k] == 0);
      int s = F[k];
      if (rnd() & 1) { int nk = perF[k] < 8 ? (int)perF[k] : 8; s = (int)(failt[k * 8 + rnd() % nk] / M); }
      int v = s;
      if (rnd() & 1) { int e0 = adje[adjstart[s] + rnd() % (adjstart[s + 1] - adjstart[s])]; v = eu[e0] == s ? ev[e0] : eu[e0]; }
      ei = adje[adjstart[v] + rnd() % (adjstart[v + 1] - adjstart[v])];
    } else ei = rnd() % E;
    int old = eb[ei], nb = STEP == 1 ? (int)(rnd() % M2) : (old + STEP * (1 + (int)(rnd() % (M2 / STEP - 1)))) % M2;
    if (nb == old || clashes(ei, nb)) continue;
    eb[ei] = nb;
    long long *tmp = malloc(8 * nF); memcpy(tmp, perF, 8 * nF);
    long long c2 = evaluate(F, nF, perF);
    if (c2 <= c || (T > 0 && exp((double)(c - c2) / T) > (double)(rnd() % 1000000) / 1e6)) { c = c2; acc++; }
    else { eb[ei] = old; memcpy(perF, tmp, 8 * nF); }
    free(tmp);
    if (it % 200 == 0) fprintf(stderr, "t %.0f it %lld T %.3f focus cost %lld |F| %d acc %lld\n", now() - t0, it, T, c, nF, acc);
  }
  tot = evaluate(all, NB, perall);
  if (tot < best) { best = tot; save(out); }
  printf("final full cost %lld best %lld it %lld |F| %d\n", tot, best, it, nF);
  return 0;
}
