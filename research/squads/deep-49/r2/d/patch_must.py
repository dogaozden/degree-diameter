# builds exh3m.c from exh3.c: adds the MUST (both-sides coverage) filter and a hit threshold from env HITMAX
import re, sys
src = open('exh3.c').read()
helper = r'''
/* ---- auditor addition: MUST filter (env MUST=g1,g2,..): a set counts only if every must element g lies at graph
 * distance <= D-1 from both roots (e,A) and (e,B), i.e. g in both (SS^-1)^h and (S^-1 S)^h. ---- */
static int MUSTN = 0, must_el[16];
static int HITMAX = 6;
static int dist_ok(const int *S, int root_side, int g) {
    /* plain BFS on the 2N-vertex graph: A-vertex a ~ B-vertex mul(s,a); B-vertex b ~ A-vertex mul(INV[s], b) */
    static int *d = 0, *q = 0; if (!d) { d = malloc(2 * N * sizeof(int)); q = malloc(2 * N * sizeof(int)); }
    for (int i = 0; i < 2 * N; i++) d[i] = -1;
    int root = root_side ? N + 0 : 0; d[root] = 0; int h = 0, t = 0; q[t++] = root;
    while (h < t) { int v = q[h++]; if (d[v] >= D - 1) continue;
        if (v < N) { for (int i = 0; i < 4; i++) { int w = N + mul(S[i], v); if (d[w] < 0) { d[w] = d[v] + 1; q[t++] = w; } } }
        else { int b = v - N; for (int i = 0; i < 4; i++) { int w = mul(INV[S[i]], b); if (d[w] < 0) { d[w] = d[v] + 1; q[t++] = w; } } } }
    int target = root_side ? N + g : g;
    return d[target] >= 0 && d[target] <= D - 1;
}
static int must_ok(int x, int y, int z) {
    int S[4] = {0, x, y, z};
    for (int i = 0; i < MUSTN; i++) { int g = must_el[i];
        if (!dist_ok(S, 0, g) || !dist_ok(S, 1, g)) return 0; }
    return 1;
}
'''
# insert helper before main()
assert src.count('int main(int argc') == 1
src = src.replace('int main(int argc', helper + '\nint main(int argc', 1)
# parse env and check must elements are fixed by all automorphisms in the list, right after setup of reps
old = '    setup_inv();\n    setup_cosets();\n    build_reps();\n'
assert src.count(old) == 1
new = old + '''    if (getenv("MUST")) { char *s = strdup(getenv("MUST")); char *tok = strtok(s, ",");
        while (tok && MUSTN < 16) { must_el[MUSTN++] = atoi(tok); tok = strtok(NULL, ","); } free(s); }
    if (getenv("HITMAX")) HITMAX = atoi(getenv("HITMAX"));
    for (int i = 0; i < MUSTN; i++) { for (int t = 0; is_meta && t < naut; t++) if (meta_apply(t, must_el[i]) != must_el[i]) {
            fprintf(stderr, "must element %d moved by an automorphism in the list: abort\\n", must_el[i]); return 3; } }
    if (MUSTN) fprintf(stderr, "MUST filter on %d elements (checked: fixed by all %s automorphisms in the list)\\n", MUSTN, is_meta ? "meta" : "table");
'''
src = src.replace(old, new, 1)
old2 = '                if (c <= best) {\n                    int S[4] = { 0, x, y, z };\n                    if (hf && c <= 6)'
assert src.count(old2) == 1, src.count(old2)
src = src.replace(old2, '                if (c <= best && must_ok(x, y, z)) {\n                    int S[4] = { 0, x, y, z };\n                    if (hf && c <= HITMAX)', 1)
open('exh3m.c', 'w').write(src)
print('ok')
