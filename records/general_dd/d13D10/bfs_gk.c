// bfs_gk.c -- (group file may be Q x Z_k: header p, -L0, k; level j*L0+i, Z_k acts trivially)
// bfs_g.c -- plain explicit BFS check for G = F_p^2 x| Q (cay_mg group file). usage: bfs_g FILE d K lev vr vc ... [lev vr vc (involution)]
// element = (x in Q, (y1,y2)); (u,v)(x,y) = (u x, rho(x)^-1 v + y). Visited/current/next bitsets over x*p*p+y1*p+y2 (3N/8 bytes).
// Independent of cay_mg: explicit element-wise multiplication, no bitset rotations.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef int64_t i64;
#ifndef DIRECT_MAX
#define DIRECT_MAX 300000000LL
#endif
static int p, L, L0, ZK, *Q;
static int mulm(int a, int b){ return (int)(((i64)a * b) % p); }
static void mm(const int *a, const int *b, int *o){
  int t0 = (mulm(a[0], b[0]) + mulm(a[1], b[2])) % p, t1 = (mulm(a[0], b[1]) + mulm(a[1], b[3])) % p;
  int t2 = (mulm(a[2], b[0]) + mulm(a[3], b[2])) % p, t3 = (mulm(a[2], b[1]) + mulm(a[3], b[3])) % p;
  o[0] = t0; o[1] = t1; o[2] = t2; o[3] = t3; }
static int invm(int a){ i64 t = 0, nt = 1, r = p, nr = a % p; while (nr) { i64 q = r / nr, tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; } if (r != 1) { fprintf(stderr, "not invertible\n"); exit(5); } if (t < 0) t += p; return (int)t; }
static int powm(int b, int e){ i64 r = 1, x = b % p; while (e) { if (e & 1) r = r * x % p; x = x * x % p; e >>= 1; } return (int)r; }
static void inv(const int *a, int *o){
  int det = ((mulm(a[0], a[3]) - mulm(a[1], a[2])) % p + p) % p; int di = invm(det);
  o[0] = mulm(a[3], di); o[1] = mulm((p - a[1]) % p, di); o[2] = mulm((p - a[2]) % p, di); o[3] = mulm(a[0], di); }
static int *qidx; // direct index over all p^4 matrices when p^4 is small; else sorted (key, index) pairs + binary search
static i64 *skey; static int *sidx, DIRECT;
static i64 mkey(const int *m){ return ((i64)(m[0] * (i64)p + m[1]) * p + m[2]) * p + m[3]; }
static int findq(const int *m){ i64 c = mkey(m); int r = -1;
  if (DIRECT) r = qidx[c];
  else { int lo = 0, hi = L0 - 1; while (lo <= hi) { int mid = (lo + hi) / 2; if (skey[mid] == c) { r = sidx[mid]; break; } if (skey[mid] < c) lo = mid + 1; else hi = mid - 1; } }
  if (r < 0) { fprintf(stderr, "not in Q\n"); exit(3); } return r; }
static int cmpk(const void *a, const void *b){ i64 x = skey[*(const int *)a], y = skey[*(const int *)b]; return x < y ? -1 : x > y; }
int main(int argc, char **argv){
  FILE *f = fopen(argv[1], "rb"); int hd[2]; if (fread(hd, 4, 2, f) != 2) return 2; p = hd[0];
  if (hd[1] < 0) { L0 = -hd[1]; if (fread(&ZK, 4, 1, f) != 1 || ZK < 1) return 2; } else { L0 = hd[1]; ZK = 1; }
  L = L0 * ZK;
  Q = malloc(16 * L0); if (fread(Q, 16, L0, f) != (size_t)L0) return 2; fclose(f);
  DIRECT = (i64)p * p * p * p <= DIRECT_MAX;
  if (DIRECT) { qidx = malloc(sizeof(int) * (size_t)p * p * p * p); memset(qidx, -1, sizeof(int) * (size_t)p * p * p * p);
    for (int x = 0; x < L0; x++) { i64 c = mkey(Q + 4 * x); if (qidx[c] >= 0) { fprintf(stderr, "duplicate matrix in Q\n"); return 4; } qidx[c] = x; } }
  else { skey = malloc(8 * (size_t)L0); int *ord = malloc(4 * (size_t)L0); i64 *tk = malloc(8 * (size_t)L0); sidx = malloc(4 * (size_t)L0);
    for (int x = 0; x < L0; x++) { skey[x] = mkey(Q + 4 * x); ord[x] = x; }
    qsort(ord, L0, 4, cmpk); for (int i = 0; i < L0; i++) { tk[i] = skey[ord[i]]; sidx[i] = ord[i]; }
    free(skey); skey = tk; for (int i = 1; i < L0; i++) if (skey[i] == skey[i - 1]) { fprintf(stderr, "duplicate matrix in Q\n"); return 4; } }
  int d = atoi(argv[2]), K = atoi(argv[3]); int H = d / 2, INV = d & 1, a = 4;
  int ng = 2 * H + INV; int gl[64], gvr[64], gvc[64]; int g = 0;
  for (int i = 0; i < H + INV; i++) {
    int lev = atoi(argv[a++]), vr = atoi(argv[a++]), vc = atoi(argv[a++]);
    gl[g] = lev; gvr[g] = vr; gvc[g] = vc; g++;
    if (i < H) {   // (u,v)^-1 = (u^-1, -M_{u^-1} v), M_x = rho(x)^-1, so M_{u^-1} = rho(u)
      int ui[4]; inv(Q + 4 * (lev % L0), ui); int il = findq(ui) + ((ZK - lev / L0) % ZK) * L0; const int *M = Q + 4 * (lev % L0);
      int w0 = (mulm(M[0], vr) + mulm(M[1], vc)) % p, w1 = (mulm(M[2], vr) + mulm(M[3], vc)) % p;
      gl[g] = il; gvr[g] = (p - w0) % p; gvc[g] = (p - w1) % p; g++; }
  }
  int *dl = malloc(4 * ng * L); int *Mx = malloc(16 * L);
  for (int x = 0; x < L; x++) inv(Q + 4 * (x % L0), Mx + 4 * x);
  for (int gg = 0; gg < ng; gg++) for (int x = 0; x < L0; x++) { int o[4]; mm(Q + 4 * (gl[gg] % L0), Q + 4 * x, o); int i0 = findq(o);
    for (int j = 0; j < ZK; j++) dl[gg * L + j * L0 + x] = ((gl[gg] / L0 + j) % ZK) * L0 + i0; }
  i64 N = (i64)L * p * p; i64 W = (N + 63) / 64;
  uint64_t *vis = calloc(W, 8), *cur = calloc(W, 8), *nxt = calloc(W, 8);
  if (!vis || !cur || !nxt) { fprintf(stderr, "oom\n"); return 6; }
  cur[0] = 1; vis[0] = 1; i64 nc = 1, total = 1;
  printf("order %lld layers 1", (long long)N);
  for (int t = 1; t <= K && nc; t++) {
    i64 nn = 0;
    #pragma omp parallel for schedule(dynamic, 4096) reduction(+:nn)
    for (i64 w = 0; w < W; w++) {
      uint64_t bits = cur[w];
      while (bits) {
        int b = __builtin_ctzll(bits); bits &= bits - 1;
        i64 e = w * 64 + b; int x = e / ((i64)p * p), y1 = (e / p) % p, y2 = e % p; const int *M = Mx + 4 * x;
        for (int gg = 0; gg < ng; gg++) {
          int w0 = (mulm(M[0], gvr[gg]) + mulm(M[1], gvc[gg])) % p, w1 = (mulm(M[2], gvr[gg]) + mulm(M[3], gvc[gg])) % p;
          int z1 = (w0 + y1) % p, z2 = (w1 + y2) % p; i64 id = ((i64)dl[gg * L + x] * p + z1) * p + z2;
          uint64_t m = 1ULL << (id & 63);
          if (!(__atomic_load_n(&vis[id >> 6], __ATOMIC_RELAXED) & m)) {
            uint64_t old = __atomic_fetch_or(&vis[id >> 6], m, __ATOMIC_RELAXED);
            if (!(old & m)) { __atomic_fetch_or(&nxt[id >> 6], m, __ATOMIC_RELAXED); nn++; } }
        }
      }
    }
    uint64_t *tmp = cur; cur = nxt; nxt = tmp; memset(nxt, 0, W * 8); fflush(stdout); nc = nn; total += nn; printf(" %lld", (long long)nn);
  }
  printf("\nreached %lld defect %lld\n", (long long)total, (long long)(N - total)); return 0;
}
