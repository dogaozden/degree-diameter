/* gencheck.c: diameter check for an affine permutation lift of a GENERAL base graph (loops allowed).
   Base file: "N m" then edges "u v a b" meaning (u,x) ~ (v, a*x+b mod m), gcd(a,m)=1 (u may equal v).
   BFS from sources (u,x0), u = 0, STEP, ...; x0 = 0, XSTEP, ...; depth DEPTH; counts unreached (v,y).
   usage: gencheck BASE DEPTH STEP XSTEP */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
int N, m, nmaps; int mapid[64][64]; u64 *T;
static inline u64 app(u64 x, int mi) { const u64 *t = T + (size_t)mi * 2048; u64 r = 0;
    for (int b = 0; x; b++, x >>= 8) { unsigned v = x & 255; if (v) r |= t[b * 256 + v]; } return r; }
int getmap(int a, int b) { if (mapid[a][b] >= 0) return mapid[a][b]; int id = nmaps++; mapid[a][b] = id;
    T = realloc(T, sizeof(u64) * 2048 * nmaps); u64 *t = T + (size_t)id * 2048;
    for (int byte = 0; byte < 8; byte++) for (int v = 0; v < 256; v++) { u64 r = 0;
        for (int bit = 0; bit < 8; bit++) if (v >> bit & 1) { int x = byte * 8 + bit; if (x < m) r |= 1ULL << ((a * x + b) % m); }
        t[byte * 256 + v] = r; } return id; }
int inv(int a) { for (int i = 1; i < m; i++) if (a * i % m == 1) return i; return -1; }
int main(int argc, char **argv) {
    int depth = atoi(argv[2]), step = atoi(argv[3]), xstep = atoi(argv[4]);
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d", &N, &m) != 2) return 1;
    memset(mapid, -1, sizeof mapid);
    int cap = 1 << 20, ne = 0; int *E = malloc(16 * cap); int u, v, a, b;
    while (fscanf(f, "%d %d %d %d", &u, &v, &a, &b) == 4) { if (ne == cap) { cap *= 2; E = realloc(E, 16 * cap); } E[4*ne]=u; E[4*ne+1]=v; E[4*ne+2]=a%m; E[4*ne+3]=b%m; ne++; }
    /* directed adjacency: each edge gives u->v with map (a,b) and v->u with inverse */
    int *st = calloc(N + 1, 4); for (int i = 0; i < ne; i++) { st[E[4*i]+1]++; st[E[4*i+1]+1]++; }
    for (int i = 0; i < N; i++) st[i+1] += st[i];
    int *to = malloc(8 * ne), *mp = malloc(8 * ne), *c = calloc(N, 4);
    for (int i = 0; i < ne; i++) { int uu = E[4*i], vv = E[4*i+1], aa = E[4*i+2], bb = E[4*i+3], ai = inv(aa);
        int k = st[uu] + c[uu]++; to[k] = vv; mp[k] = getmap(aa, bb);
        int k2 = st[vv] + c[vv]++; to[k2] = uu; mp[k2] = getmap(ai, (m - ai * bb % m) % m); }
    int maxdeg = 0; for (int i = 0; i < N; i++) if (st[i+1]-st[i] > maxdeg) maxdeg = st[i+1]-st[i];
    u64 FULL = m == 64 ? ~0ULL : (1ULL << m) - 1;
    long long total = 0; int nsrc = 0, worst = 0;
    #pragma omp parallel reduction(+:total,nsrc)
    { u64 *r = malloc(8 * N), *fr = malloc(8 * N), *nf = malloc(8 * N);
      #pragma omp for schedule(dynamic, 4)
      for (int s = 0; s < N; s += step) for (int x0 = 0; x0 < m; x0 += xstep) {
        memset(r, 0, 8 * N); memset(fr, 0, 8 * N); r[s] = fr[s] = 1ULL << x0;
        for (int t = 1; t <= depth; t++) { memset(nf, 0, 8 * N);
            for (int x = 0; x < N; x++) { u64 vv = fr[x]; if (!vv) continue; for (int k = st[x]; k < st[x+1]; k++) nf[to[k]] |= app(vv, mp[k]); }
            for (int y = 0; y < N; y++) { nf[y] &= ~r[y]; r[y] |= nf[y]; } u64 *tmp = fr; fr = nf; nf = tmp; }
        long long un = 0; for (int y = 0; y < N; y++) un += m - __builtin_popcountll(r[y] & FULL);
        total += un; nsrc++;
        #pragma omp critical
        { if (un > worst) worst = (int)un; } }
      free(r); free(fr); free(nf); }
    printf("N=%d m=%d maxdeg=%d depth=%d sources %d total unreached %lld worst %d\n", N, m, maxdeg, depth, nsrc, total, worst);
    return 0; }
