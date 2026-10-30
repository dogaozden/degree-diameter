/* sdcheck.c: is a Haar connection set S self-dual by an anti-affine map psi(x) = beta(x)^-1 w (beta in Aut(G))?
 * usage: sdcheck GROUP.ht AUTS.txt s1 ... s7   (prints every (beta, w) with psi(S) = S) */
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int n, x; if (fscanf(f, "%d %d", &n, &x) != 2) return 1;
    int *mul = malloc(sizeof(int) * n * n), *inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 1;
    for (int i = 0; i < n; i++) if (fscanf(f, "%d", &inv[i]) != 1) return 1;
    fclose(f);
    int k = c - 3, S[64]; for (int i = 0; i < k; i++) S[i] = atoi(v[3 + i]);
    char *inS = calloc(n, 1); for (int i = 0; i < k; i++) inS[S[i]] = 1;
    FILE *g = fopen(v[2], "r"); int na; if (fscanf(g, "%d", &na) != 1) return 1;
    int *b = malloc(sizeof(int) * n), hits = 0;
    for (int a = 0; a < na; a++) {
        for (int i = 0; i < n; i++) if (fscanf(g, "%d", &b[i]) != 1) return 1;
        for (int j = 0; j < k; j++) {   /* w with beta(S[0])^-1 w = S[j] */
            int w = mul[b[S[0]] * n + S[j]], ok = 1;
            for (int i = 0; i < k && ok; i++) if (!inS[mul[inv[b[S[i]]] * n + w]]) ok = 0;
            if (ok) { hits++; if (hits <= 5) { int fx = 0; for (int i = 0; i < k; i++) if (mul[inv[b[S[i]]] * n + w] == S[i]) fx++;
                int id = 1; for (int i = 0; i < n; i++) if (b[i] != i) id = 0;
                printf("aut %d (identity %d) w %d fixes %d of S\n", a, id, w, fx); } }
        }
    }
    printf("self-dual maps: %d of %d automorphisms x %d\n", hits, na, k);
    return 0;
}
