/* Haar graph H(G,S) over metacyclic G = Z_m x| Z_n (a,b)(c,d) = (a + r^b c mod m, b+d mod n), |S| = 4, 1 in S.
   a_g ~ b_{g s}. G acts regularly on both sides, so eccentricity is read from a_e and b_e only.
   usage: meta_search d D N tries seed outfile_prefix
   Prints every success (m n r S) and writes the first success's edge list to <prefix>_n<2N>.edges. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned long long rs;
static unsigned rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }

static int gcd(int a,int b){ while(b){int t=a%b;a=b;b=t;} return a; }

int main(int argc, char **argv){
  if (argc < 6) { fprintf(stderr,"usage: d D N tries seed [outprefix]\n"); return 1; }
  int d = atoi(argv[1]); (void)d;
  int D = atoi(argv[2]);
  int N = atoi(argv[3]);
  long tries = atol(argv[4]);
  rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[5]) * 2654435761ULL;
  const char *outp = argc > 6 ? argv[6] : NULL;
  int K = 4;
  int nn = 2*N;
  int *perm = malloc(sizeof(int)*N*K), *iperm = malloc(sizeof(int)*N*K);
  int *dist = malloc(sizeof(int)*nn), *q = malloc(sizeof(int)*nn);
  int *pw = malloc(sizeof(int)*N+ sizeof(int)*1024);
  long found = 0;
  /* list of divisors m of N with n = N/m */
  for (long t = 0; t < tries; t++) {
    /* choose m | N */
    int divs[256], nd = 0;
    for (int m = 1; m <= N; m++) if (N % m == 0) divs[nd++] = m;
    int m = divs[rnd() % nd];
    int n = N / m;
    /* choose r with gcd(r,m)=1, r^n = 1 mod m */
    int r = 1 % (m ? m : 1);
    if (m > 1) {
      int ok = 0;
      for (int k = 0; k < 200 && !ok; k++) {
        int c = 1 + rnd() % (m - 1);
        if (gcd(c, m) != 1) continue;
        long p = 1; for (int i = 0; i < n; i++) p = (p * c) % m;
        if (p % m == 1 % m) { r = c; ok = 1; }
      }
      if (!ok) { if (rnd()%4) continue; r = 1; }
    }
    /* powers of r mod m for exponent b in 0..n-1 */
    int *rp = pw; rp[0] = 1 % m; for (int i = 1; i < n; i++) rp[i] = (int)(((long)rp[i-1] * r) % m);
    /* multiplication g*s for g=(a,b) index a*n+b */
    int S[K]; S[0] = 0;
    int ok = 1;
    for (int k = 1; k < K; k++) {
      int x; int tries2 = 0;
      do { x = rnd() % N; tries2++; } while ((x == 0 || (x==S[1]&&k>1)||(k>2 && x==S[2])) && tries2 < 1000);
      S[k] = x;
    }
    /* check distinct */
    for (int i = 0; i < K && ok; i++) for (int j = i+1; j < K; j++) if (S[i]==S[j]) ok = 0;
    if (!ok) continue;
    /* build right-mult perms for s and s^{-1} */
    for (int k = 0; k < K; k++) {
      int sa = S[k] / n, sb = S[k] % n;
      for (int g = 0; g < N; g++) {
        int ga = g / n, gb = g % n;
        int ha = (ga + (int)(((long)rp[gb] * sa) % m)) % m;
        int hb = (gb + sb) % n;
        perm[k*N + g] = ha * n + hb;
      }
    }
    /* inverse element of s: (a,b)^{-1} = (-r^{-b} a, -b). Use perm: iperm[k] = right mult by s^{-1}. */
    for (int k = 0; k < K; k++) {
      int sa = S[k] / n, sb = S[k] % n;
      /* find inverse element index by search over N (cheap) */
      int inv = -1;
      for (int h = 0; h < N && inv < 0; h++) {
        int ha = h / n, hb = h % n;
        int ca = (ha + (int)(((long)rp[hb] * sa) % m)) % m;
        int cb = (hb + sb) % n;
        if (ca == 0 && cb == 0) inv = h;
      }
      for (int g = 0; g < N; g++) {
        int ga = g / n, gb = g % n;
        int sa2 = inv / n, sb2 = inv % n;
        int ha = (ga + (int)(((long)rp[gb] * sa2) % m)) % m;
        int hb = (gb + sb2) % n;
        iperm[k*N + g] = ha * n + hb;
      }
    }
    /* BFS from a_e (index 0) and from b_e (index N) on 2N vertices.
       a_g (g) adj b_{g s} = N + perm[k][g];  b_h (N+h) adj a_{h s^{-1}} = iperm[k][h] */
    int maxecc = 0, bad = 0;
    for (int src = 0; src < 2 && !bad; src++) {
      for (int v = 0; v < nn; v++) dist[v] = -1;
      int head = 0, tail = 0;
      int s0 = src ? N : 0;
      dist[s0] = 0; q[tail++] = s0;
      while (head < tail) {
        int v = q[head++];
        int dv = dist[v];
        if (v < N) {
          for (int k = 0; k < K; k++) { int w = N + perm[k*N + v]; if (dist[w] < 0) { dist[w] = dv+1; q[tail++] = w; } }
        } else {
          int h = v - N;
          for (int k = 0; k < K; k++) { int w = iperm[k*N + h]; if (dist[w] < 0) { dist[w] = dv+1; q[tail++] = w; } }
        }
      }
      if (tail < nn) { bad = 1; break; }
      int ecc = dist[q[tail-1]];
      if (ecc > maxecc) maxecc = ecc;
      if (ecc > D) bad = 1;
    }
    if (!bad) {
      found++;
      printf("OK m=%d n=%d r=%d S=", m, n, r);
      for (int k = 0; k < K; k++) printf("(%d,%d)", S[k]/n, S[k]%n);
      printf(" diam_ok_ecc=%d vertices=%d\n", maxecc, nn);
      fflush(stdout);
      if (outp && found == 1) {
        char fn[512]; sprintf(fn, "%s_n%d.edges", outp, nn);
        FILE *f = fopen(fn, "w");
        fprintf(f, "%d\n", nn);
        for (int g = 0; g < N; g++) for (int k = 0; k < K; k++) fprintf(f, "%d %d\n", g, N + perm[k*N+g]);
        fclose(f);
        printf("WROTE %s\n", fn);
      }
      if (found >= 3) break;
    }
  }
  printf("done found=%ld\n", found);
  return 0;
}
