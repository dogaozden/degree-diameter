/* ILS for pairwise-opposite point sets (partial ovoids of H(11)): R has no two points with B(x,y)=0 mod 11.
   Opposition in H(q) = non-orthogonality on Q(6,q): B(x,y)=x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3.
   usage: ils HEXBIN START|- SEED SECONDS OUT   (START: one id per line)  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define Q 11
static int N;
static unsigned char *X, *V;
static int *c; static char *inR; static int *R, *pos, k = 0;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline int orth(int x, int y) { /* B(x,y) == 0 */
  const unsigned char *a = X + 7 * x, *b = V + 7 * y;
  int s = a[0]*b[0] + a[1]*b[1] + a[2]*b[2] + a[3]*b[3] + a[4]*b[4] + a[5]*b[5] + a[6]*b[6];
  return s % Q == 0;
}
#define MAXLOG 4000000
static int *logop; static int nlog = 0; static int logging = 0; /* +id add, -(id+1) remove */
static void addpt(int r) {
  inR[r] = 1; pos[r] = k; R[k++] = r;
  const unsigned char *b = V + 7 * r;
  for (int x = 0; x < N; x++) { const unsigned char *a = X + 7 * x;
    int s = a[0]*b[0] + a[1]*b[1] + a[2]*b[2] + a[3]*b[3] + a[4]*b[4] + a[5]*b[5] + a[6]*b[6];
    if (s % Q == 0) c[x]++; }
  if (logging && nlog < MAXLOG) logop[nlog++] = r;
}
static void rempt(int r) {
  inR[r] = 0; int p = pos[r]; R[p] = R[--k]; pos[R[p]] = p; pos[r] = -1;
  for (int x = 0; x < N; x++) if (orth(x, r)) c[x]--;
  if (logging && nlog < MAXLOG) logop[nlog++] = -(r + 1);
}
static int *freel, *tx, *tr;
static int try_swap(void) {
  int nt = 0;
  for (int x = 0; x < N; x++) if (!inR[x] && c[x] == 1) {
    int r = -1; for (int i = 0; i < k; i++) if (orth(x, R[i])) { r = R[i]; break; }
    tx[nt] = x; tr[nt] = r; nt++; }
  if (nt < 2) return 0;
  /* shuffle */
  for (int i = nt - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = tx[i]; tx[i] = tx[j]; tx[j] = t; t = tr[i]; tr[i] = tr[j]; tr[j] = t; }
  for (int i = 0; i < nt; i++) for (int j = i + 1; j < nt; j++) {
    if (tr[i] != tr[j]) continue;
    if (!orth(tx[i], tx[j])) {
      int r = tr[i], x = tx[i], y = tx[j];
      rempt(r); addpt(x); addpt(y); return 1; } }
  return 0;
}
static void local_search(void) {
  for (;;) {
    int nf = 0;
    for (int x = 0; x < N; x++) if (!inR[x] && c[x] == 0) freel[nf++] = x;
    if (nf > 0) { addpt(freel[rnd() % nf]); continue; }
    if (try_swap()) continue;
    break;
  }
}
static void undo_log(void) {
  logging = 0;
  for (int i = nlog - 1; i >= 0; i--) { int v = logop[i];
    if (v >= 0) rempt(v); else addpt(-v - 1); }
  nlog = 0; logging = 1;
}
static void save(const char *fn, int *list, int n) {
  FILE *f = fopen(fn, "w"); if (!f) return;
  for (int i = 0; i < n; i++) fprintf(f, "%d\n", list[i]);
  fclose(f);
}
int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: ils HEXBIN START|- SEED SECONDS OUT\n"); return 1; }
  FILE *h = fopen(argv[1], "rb"); if (!h) { perror("hex"); return 1; }
  int hdr[3]; if (fread(hdr, 4, 3, h) != 3) return 1;
  int q = hdr[0], n = hdr[1], L = hdr[2]; N = n;
  fseek(h, 12 + 4L * L * (q + 1), SEEK_SET);
  unsigned char *Xr = malloc((size_t)N * 7);
  if (fread(Xr, 1, (size_t)N * 7, h) != (size_t)N * 7) { fprintf(stderr, "short read\n"); return 1; }
  fclose(h);
  X = Xr; V = malloc((size_t)N * 7);
  for (int x = 0; x < N; x++) { const unsigned char *y = X + 7 * x; unsigned char *v = V + 7 * x;
    v[0] = y[4]; v[1] = y[5]; v[2] = y[6]; v[3] = (unsigned char)((Q * 2 - 2 * y[3]) % Q); v[4] = y[0]; v[5] = y[1]; v[6] = y[2]; }
  c = calloc(N, sizeof(int)); inR = calloc(N, 1); R = malloc(sizeof(int) * N); pos = malloc(sizeof(int) * N);
  freel = malloc(sizeof(int) * N); tx = malloc(sizeof(int) * N); tr = malloc(sizeof(int) * N);
  logop = malloc(sizeof(int) * MAXLOG);
  for (int x = 0; x < N; x++) pos[x] = -1;
  rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
  if (strcmp(argv[2], "-") != 0) {
    FILE *s = fopen(argv[2], "r"); int id;
    while (fscanf(s, "%d", &id) == 1) if (!inR[id] && c[id] == 0) addpt(id); else fprintf(stderr, "skip %d\n", id);
    fclose(s);
  }
  double secs = atof(argv[4]);
  clock_t t0 = clock();
  local_search();
  int best = k; int *bestl = malloc(sizeof(int) * N); memcpy(bestl, R, sizeof(int) * k);
  save(argv[5], bestl, best);
  fprintf(stderr, "start size %d\n", k);
  long it = 0; double last = 0;
  int *cand = malloc(sizeof(int) * N); int nc;
  while (1) {
    double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (el > secs) break;
    it++;
    int cur = k; nlog = 0; logging = 1;
    /* perturb: force-insert a random point with 1 or 2 conflicts */
    nc = 0; for (int x = 0; x < N; x++) if (!inR[x] && (c[x] == 1 || c[x] == 2)) cand[nc++] = x;
    if (nc == 0) break;
    int x = cand[rnd() % nc];
    for (int i = k - 1; i >= 0; i--) { int r = R[i]; if (orth(x, r)) rempt(r); }
    addpt(x);
    local_search();
    logging = 0;
    if (k > best) { best = k; memcpy(bestl, R, sizeof(int) * k); save(argv[5], bestl, best);
      fprintf(stderr, "[%.1fs it %ld] new best %d\n", el, it, best); }
    if (k < cur - 1) { undo_log(); }
    if (el - last > 20) { last = el; fprintf(stderr, "[%.0fs it %ld] cur %d best %d\n", el, it, k, best); }
  }
  printf("VALID-PARTIAL %d\n", best);
  return 0;
}
