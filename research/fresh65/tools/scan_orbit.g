# Orbit-symmetric Haar graphs at (6,5), exhaustively (job fresh-6-5).
# For every group K of order n in [NLO, NHI] (SmallGroups) and every class of automorphisms alpha of order k
# in KS (up to conjugacy in Aut(K)), export G = K x| <alpha> with L = R = <alpha>. The bi-coset graphs of
# (G, L, L) are exactly the Haar graphs H(K, S) with alpha(S) = S, and bicoset.c scans all of them.
# Usage: gap -q -c 'NLO:=343;; NHI:=351;; KS:=[2,3,6];; OUTDIR:="../bc/orb";; SKIP:=[352,360];;' bicoset.g scan_orbit.g
if not IsBound(SKIP) then SKIP := []; fi;
if not IsBound(MAXGROUPS) then MAXGROUPS := 400; fi;
for n in [NLO..NHI] do
    if n in SKIP or NrSmallGroups(n) > MAXGROUPS then
        Print("SKIPORDER ", n, " groups=", NrSmallGroups(n), "\n");
        continue;
    fi;
    for i in [1..NrSmallGroups(n)] do
        K := SmallGroup(n, i);
        if IsAbelian(K) then continue; fi;   # abelian Haar graphs: too many word collisions (costs in the hundreds)
        A := AutomorphismGroup(K);
        iso := IsomorphismPermGroup(A);
        P := Image(iso);
        for k in KS do
            cls := Filtered(ConjugacyClasses(P), c -> Order(Representative(c)) = k);
            j := 0;
            for c in cls do
                j := j + 1;
                alpha := PreImagesRepresentative(iso, Representative(c));
                lab := Concatenation("orb", String(k), "_n", String(n), "_i", String(i), "_a", String(j));
                r := ExportOrbitHaar(K, alpha, Concatenation(OUTDIR, "/", lab, ".tmp"), lab);
                Exec(Concatenation("mv ", OUTDIR, "/", lab, ".tmp ", OUTDIR, "/", lab, ".txt"));
                Print("EXPORT ", lab, " ", StructureDescription(K), " orbits=", r[2], " fix=", r[3], "\n");
            od;
        od;
    od;
od;
Print("ALLDONE\n");
QUIT;
