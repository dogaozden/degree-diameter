/* g02 independent check: Haar graph H(G,S), G = Z_m x|_r Z_k, from a hmeta solution file
 * ("d D meta m k r n 1 N" then d lines "<idx> meta(a=A,j=J) z=0"). Own code, plain BFS (not hmeta's bitsets).
 * Vertices (g,A),(g,B), g in G, index a*k+j; edges (g,A)~(s g,B). Diameter <= D iff BFS from (e,A) and from (e,B)
 * both reach all 2N vertices within D (right multiplication is a side-transitive automorphism group). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static ll m, k, r;
static ll pw(ll b, ll e, ll md) { ll x = 1 % md; b %= md; while (e) { if (e & 1) x = (__int128)x * b % md; b = (__int128)b * b % md; e >>= 1; } return x; }
static ll *RP;
static void mul(ll a1, ll j1, ll a2, ll j2, ll *a, ll *j) { *a = (a1 + RP[j1] * a2) % m; *j = (j1 + j2) % k; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    int d, D; char line[512]; char tag[16]; ll n1, NN;
    if (fscanf(f, "%d %d %15s %lld %lld %lld %15s %lld %15s %lld", &d, &D, tag, &m, &k, &r, line, &n1, line, &NN) != 10) { printf("bad header\n"); return 2; }
    if (pw(r, k, m) != 1 % m) { printf("INVALID r^k != 1\n"); return 2; }
    RP = malloc(sizeof(ll) * k); for (ll t = 0; t < k; t++) RP[t] = pw(r, t, m);
    ll N = m * k; if (N != NN) { printf("INVALID N mismatch %lld vs %lld\n", N, NN); return 2; }
    ll *sa = malloc(sizeof(ll) * d), *sj = malloc(sizeof(ll) * d), *ia = malloc(sizeof(ll) * d), *ij = malloc(sizeof(ll) * d);
    int got = 0; ll idx; ll a, j;
    while (got < d && fgets(line, sizeof line, f)) {
        char *p = strstr(line, "meta(a="); if (!p) continue;
        if (sscanf(p, "meta(a=%lld,j=%lld)", &a, &j) == 2) { sa[got] = a % m; sj[got] = j % k; got++; }
    }
    fclose(f); (void)idx;
    if (got != d) { printf("INVALID only %d generators\n", got); return 2; }
    for (int i = 0; i < d; i++) for (int t = 0; t < i; t++) if (sa[i] == sa[t] && sj[i] == sj[t]) { printf("INVALID repeated generator\n"); return 2; }
    for (int i = 0; i < d; i++) { /* inverse: (a,j)^-1 = (-r^{-j} a, -j) */
        ll rinv = RP[(k - sj[i]) % k]; ia[i] = ((-(__int128)rinv * sa[i]) % m + m) % m; ij[i] = (k - sj[i]) % k;
        ll x, y; mul(sa[i], sj[i], ia[i], ij[i], &x, &y); if (x != 0 || y != 0) { printf("INVALID inverse\n"); return 2; } }
    ll V = 2 * N; unsigned char *dist = malloc(V); if (!dist) return 2;
    ll *q = malloc(sizeof(ll) * V);
    int ok = 1;
    for (int side = 0; side < 2 && ok; side++) {
        memset(dist, 255, V); ll h = 0, t = 0; ll src = side * N + 0; dist[src] = 0; q[t++] = src; ll maxd = 0;
        while (h < t) {
            ll v = q[h++]; ll dv = dist[v]; if (dv >= D) continue;
            ll g = v % N; int isB = v >= N; ll ga = g / k, gj = g % k;
            for (int s = 0; s < d; s++) {
                ll na, nj;
                if (!isB) { mul(sa[s], sj[s], ga, gj, &na, &nj); }      /* (g,A) -> (s g, B) */
                else { mul(ia[s], ij[s], ga, gj, &na, &nj); }          /* (h,B) -> (s^-1 h, A) */
                ll w = (isB ? 0 : N) + na * k + nj;
                if (!isB) w = N + na * k + nj; else w = na * k + nj;
                if (dist[w] == 255) { dist[w] = dv + 1; q[t++] = w; if (dv + 1 > maxd) maxd = dv + 1; }
            }
        }
        if (t != V) { ok = 0; printf("INVALID side %d reaches %lld of %lld\n", side, t, V); break; }
        fflush(stdout); printf("side %d: all %lld reached, ecc %lld\n", side, V, maxd);
        if (maxd > D) ok = 0;
    }
    fflush(stdout);
    printf("%s d=%d D=%d m=%lld k=%lld r=%lld N=%lld\n", ok ? "VALID" : "INVALID", d, D, m, k, r, N);
    return ok ? 0 : 1;
}
