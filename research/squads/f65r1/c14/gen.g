# c14: Haar graphs H(K,S) with S invariant under a group H of automorphisms of K (Z4, V4, S3, Z3xZ3).
# Input globals: NN (order), II (SmallGroup index). Writes work/*.txt (bicoset format) and manifest.
ORBDIR := "/home/user/degree-diameter/research/squads/f65r1/c14/work/";

WriteHaarFile := function(K, elms, perms, fname, label)
    local n, e, out, a, orbs, o;
    n := Length(elms);
    e := PositionSorted(elms, One(K));
    orbs := Orbits(Group(perms), [1..n]);
    out := OutputTextFile(fname, false);
    SetPrintFormattingStatus(out, false);
    AppendTo(out, label, "\n", n, " ", n, " ", e - 1, " ", e - 1, "\n");
    for a in elms do
        AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(PositionSorted(elms, x * a) - 1)), " "), "\n");
    od;
    AppendTo(out, Length(orbs), "\n");
    for o in orbs do
        AppendTo(out, Length(o), " ", JoinStringsWithSeparator(List(o, j -> String(j - 1)), " "), "\n");
    od;
    CloseStream(out);
    return orbs;
end;

# keep one subgroup per conjugacy class (subgroups given as lists of elements)
ConjDedupe := function(P, keys)
    local reps, k, H, R;
    reps := [];
    for k in keys do
        H := Group(k);
        if not ForAny(reps, R -> Size(R) = Size(H) and IsConjugate(P, H, R)) then
            Add(reps, H);
        fi;
    od;
    return reps;
end;

FindTypes := function(P)
    local reps, res, g, C, y, els, cands, keys, z4, v4, s3, z33;
    reps := List(ConjugacyClasses(P), Representative);
    els := Elements(P);
    z4 := []; v4 := []; s3 := []; z33 := [];
    for g in reps do
        if Order(g) = 4 then Add(z4, AsSSortedList(Group(g))); fi;
        if Order(g) = 2 then
            C := Centralizer(P, g);
            for y in Elements(C) do
                if Order(y) = 2 and y <> g then Add(v4, AsSSortedList(Group(g, y))); fi;
            od;
            for y in els do
                if Order(y) = 3 and g * y * g = y^-1 then Add(s3, AsSSortedList(Group(g, y))); fi;
            od;
        fi;
        if Order(g) = 3 then
            C := Centralizer(P, g);
            for y in Elements(C) do
                if Order(y) = 3 and not y in Group(g) then Add(z33, AsSSortedList(Group(g, y))); fi;
            od;
        fi;
    od;
    return rec(Z4 := ConjDedupe(P, Set(z4)), V4 := ConjDedupe(P, Set(v4)),
               S3 := ConjDedupe(P, Set(s3)), Z33 := ConjDedupe(P, Set(z33)));
end;

DoGroup := function(n, i, MAN)
    local K, elms, A, iso, P, types, typ, idx, H, gensA, perms, fname, label, orbs, cnt;
    K := SmallGroup(n, i);
    if IsAbelian(K) then return; fi;
    elms := AsSSortedList(K);
    A := AutomorphismGroup(K);
    iso := IsomorphismPermGroup(A);
    P := Image(iso);
    types := FindTypes(P);
    Print("# n=", n, " i=", i, " |Aut|=", Size(A), " Z4=", Length(types.Z4), " V4=", Length(types.V4),
          " S3=", Length(types.S3), " Z33=", Length(types.Z33), "\n");
    for typ in RecNames(types) do
        idx := 0;
        for H in types.(typ) do
            idx := idx + 1;
            gensA := List(GeneratorsOfGroup(H), h -> PreImagesRepresentative(iso, h));
            perms := List(gensA, g -> PermList(List(elms, x -> PositionSorted(elms, Image(g, x)))));
            label := Concatenation("n", String(n), "_i", String(i), "_", typ, "_", String(idx));
            fname := Concatenation(ORBDIR, label, ".txt");
            orbs := WriteHaarFile(K, elms, perms, fname, label);
            AppendTo(MAN, fname, " ", label, " ", Size(H), " ", Length(orbs), " ",
                     Number(orbs, o -> Length(o) = 1), "\n");
        od;
    od;
end;

DoOrder := function(n)
    local MAN, i, k;
    MAN := OutputTextFile(Concatenation(ORBDIR, "manifest_", String(n), ".txt"), false);
    SetPrintFormattingStatus(MAN, false);
    for i in [1..NrSmallGroups(n)] do
        if not IsAbelian(SmallGroup(n, i)) then
            Print("order ", n, " group ", i, " start ", Runtime()/1000, "s\n");
            DoGroup(n, i, MAN);
        fi;
    od;
    CloseStream(MAN);
end;
