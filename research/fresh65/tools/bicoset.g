# Bi-coset graphs B(G; L, R; D) for the bipartite degree-diameter problem (job fresh-6-5).
#
# Side A = right cosets L g, side B = right cosets R g. The base vertex L is joined to a union N0 of
# L-orbits on G/R (equivalently a union D of (L,R)-double cosets), and the edge set is the G-orbit of those
# edges: L g ~ x g for x in N0. G acts on each side transitively, so two BFS (from L and from R) give the
# exact diameter. Haar graphs are L = R = 1; orbit-symmetric Haar graphs H(K, S) with alpha(S) = S are
# G = K x| <alpha>, L = R = <alpha>; building (Weyl-distance) graphs are L = R = a parabolic subgroup.
#
# ExportBicoset(G, L, R, fname, label) writes the file read by bicoset.c:
#   line 1: label (no spaces)
#   line 2: nA nB baseA baseB      (0-based indices of the cosets L and R)
#   nA lines: the images of the nB points of G/R under the transversal element of each A-coset
#   then: number of L-orbits on G/R, and one line per orbit: size, then the points (0-based)

ExportBicoset := function(G, L, R, fname, label)
    local tA, tR, nA, nB, permOf, baseA, baseB, T, gensL, orbs, out, row, o, iso;
    if not IsPermGroup(G) then   # coset positions are much faster in a permutation group
        iso := IsomorphismPermGroup(G);
        iso := iso * SmallerDegreePermutationRepresentation(Image(iso));
        G := Image(iso); L := Image(iso, L); R := Image(iso, R);
    fi;
    tA := RightTransversal(G, L);
    tR := RightTransversal(G, R);
    nA := Length(tA); nB := Length(tR);
    permOf := g -> List([1..nB], i -> PositionCanonical(tR, tR[i] * g));
    baseA := PositionCanonical(tA, One(G));
    baseB := PositionCanonical(tR, One(G));
    gensL := List(GeneratorsOfGroup(L), g -> PermList(permOf(g)));
    if gensL = [] then gensL := [()]; fi;
    orbs := Orbits(Group(gensL), [1..nB]);
    out := OutputTextFile(fname, false);
    SetPrintFormattingStatus(out, false);
    AppendTo(out, label, "\n", nA, " ", nB, " ", baseA - 1, " ", baseB - 1, "\n");
    for row in tA do
        AppendTo(out, JoinStringsWithSeparator(List(permOf(row), i -> String(i - 1)), " "), "\n");
    od;
    AppendTo(out, Length(orbs), "\n");
    for o in orbs do
        AppendTo(out, Length(o), " ", JoinStringsWithSeparator(List(o, i -> String(i - 1)), " "), "\n");
    od;
    CloseStream(out);
    return [nA, nB, Length(orbs), List(orbs, Length)];
end;

# Number of candidate unions of L-orbits on G/R whose sizes add up to d (to budget a scan before exporting).
CountUnions := function(G, L, R, d)
    local sizes, cnt, k, ways;
    sizes := List(DoubleCosetRepsAndSizes(G, R, L), x -> x[2] / Size(R));   # L-orbits on G/R <-> double cosets R x L
    # ways[s+1] = number of sub-multisets (of distinct orbits) with total s
    ways := List([0..d], i -> 0); ways[1] := 1;
    for k in sizes do
        if k <= d then
            ways := List([0..d], s -> ways[s+1] + (function() if s >= k then return ways[s-k+1]; fi; return 0; end)());
        fi;
    od;
    return ways[d+1];
end;

# Orbit-symmetric Haar graphs H(K, S), alpha(S) = S, in bicoset.c format without building K x| <alpha>:
# the cosets of L = <alpha> are the elements of K, the A-vertex a is joined to x*a (x in S), and the
# L-orbits are the alpha-orbits on K. Same graphs as ExportBicoset(K x| <alpha>, <alpha>, <alpha>, ...).
ExportOrbitHaar := function(K, alpha, fname, label)
    local elms, n, idx, e, out, a, o, orbs, seen, x, orb, y;
    elms := AsSSortedList(K); n := Length(elms);
    e := Position(elms, One(K));
    out := OutputTextFile(fname, false);
    SetPrintFormattingStatus(out, false);
    AppendTo(out, label, "\n", n, " ", n, " ", e - 1, " ", e - 1, "\n");
    for a in elms do
        AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(Position(elms, x * a) - 1)), " "), "\n");
    od;
    orbs := []; seen := BlistList([1..n], []);
    for x in [1..n] do
        if not seen[x] then
            orb := [x]; seen[x] := true; y := Position(elms, Image(alpha, elms[x]));
            while y <> x do Add(orb, y); seen[y] := true; y := Position(elms, Image(alpha, elms[y])); od;
            Add(orbs, orb);
        fi;
    od;
    AppendTo(out, Length(orbs), "\n");
    for o in orbs do
        AppendTo(out, Length(o), " ", JoinStringsWithSeparator(List(o, i -> String(i - 1)), " "), "\n");
    od;
    CloseStream(out);
    return [n, Length(orbs), Number(orbs, o -> Length(o) = 1)];
end;
