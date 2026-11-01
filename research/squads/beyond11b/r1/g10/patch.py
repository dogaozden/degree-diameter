import sys
p='/home/user/degree-diameter/research/squads/beyond11b/r1/g10/haar_b10.c'
s=open(p).read()
def rep(old,new,count=1):
    global s
    n=s.count(old)
    assert n==count, (n, old[:60])
    s=s.replace(old,new)
# (a) helpers after random_orbit
rep("static i64 ipow_mod(i64 b, i64 e, i64 m)",
"""/* g10: OPAIR=1 constrains orbit slot 0 so that some ordered pair a, b in the orbit has (a^-1 b)^h = -I (h = (D-1)/2, odd D).
 * Then the word a^-1 b ... (2h letters) covers -I from (e,A), and (a b^-1)^h = -I covers it from (e,B). */
static int OPAIR = 0, OH = 0; static el NEGI_E;
static int pairok(const el *o) {
    if (!OPAIR) return 1;
    for (int i = 0; i < OK_; i++) for (int j = 0; j < OK_; j++) { if (i == j) continue;
        el x = emul(einv(o[i]), o[j]); el y = E_ID;
        for (int t = 0; t < OH; t++) y = emul(y, x);
        if (eeq(y, NEGI_E)) return 1; }
    return 0;
}
static int random_orbit_ok(int j, el *o) {
    for (int t = 0; t < 1000000; t++) { if (!random_orbit(j, o)) return 0; if (j != 0 || pairok(o)) return 1; }
    return 0;
}
static i64 ipow_mod(i64 b, i64 e, i64 m)""")
# (b) setup after OF0 line
rep("    OF0 = (OF == 0); if (OF0 && getenv(\"FIXF\")) { fprintf(stderr, \"FIXF needs f >= 1\\n\"); return 2; }\n",
"""    OF0 = (OF == 0); if (OF0 && getenv("FIXF")) { fprintf(stderr, "FIXF needs f >= 1\\n"); return 2; }
    OPAIR = getenv("OPAIR") ? atoi(getenv("OPAIR")) : 0; OH = (D - 1) / 2; NEGI_E = (el){P - 1, 0, 0, P - 1, 0};
    if (OPAIR && (D % 2 == 0 || OK_ < 3)) { fprintf(stderr, "OPAIR needs odd D and k >= 3\\n"); return 2; }
    if (OPAIR) fprintf(stderr, "OPAIR: slot 0 constrained, h=%d\\n", OH);
""")
# (c) init
rep("else for (int j = 0; j < OM; j++) { el o[MAXD]; if (!random_orbit(j, o)) { fprintf(stderr, \"no orbit\\n\"); return 2; }",
    "else for (int j = 0; j < OM; j++) { el o[MAXD]; if (!random_orbit_ok(j, o)) { fprintf(stderr, \"no orbit\\n\"); return 2; }")
# (d) RANDORB
rep("{ el o[MAXD]; random_orbit(j, o); for (int i = 0; i < OK_; i++) S[ostart(j) + i] = o[i]; }",
    "{ el o[MAXD]; if (!random_orbit_ok(j, o)) { fprintf(stderr, \"no orbit\\n\"); return 2; } for (int i = 0; i < OK_; i++) S[ostart(j) + i] = o[i]; }")
# (e) annealing candidates
rep("                if (!ok) random_orbit(j, o);\n",
    "                if (!ok) random_orbit(j, o);\n                if (j == 0 && !pairok(o)) random_orbit_ok(j, o);\n")
open(p,'w').write(s)
print("patched")
