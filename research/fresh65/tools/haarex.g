# Export a group for haarex.c: multiplication table (identity first) and the (r, r2) pairs:
# r = Aut-orbit representatives on G\{e}, r2 = Stab_Aut(r)-orbit representatives on G\{e,r}.
# usage: gap -q -c 'K:=SmallGroup(343,3);; FN:="x.txt";;' haarex.g
elms := AsSSortedList(K);
e := One(K);
elms := Concatenation([e], Filtered(elms, x -> x <> e));
n := Length(elms);
A := AutomorphismGroup(K);
iso := IsomorphismPermGroup(A); P := Image(iso);
act := function(x, p) return Image(PreImagesRepresentative(iso, p), x); end;
gensP := GeneratorsOfGroup(P);
permOn := List(gensP, p -> PermList(List(elms, x -> Position(elms, act(x, p)))));
AP := Group(permOn);   # Aut(K) acting on positions 1..n
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
AppendTo(out, n, "\n");
for a in elms do AppendTo(out, JoinStringsWithSeparator(List(elms, b -> String(Position(elms, a * b) - 1)), " "), "\n"); od;
pairs := [];
for O in Orbits(AP, [2..n]) do
    r := O[1];
    St := Stabilizer(AP, r);
    for O2 in Orbits(St, Difference([2..n], [r])) do Add(pairs, [r, O2[1]]); od;
od;
AppendTo(out, Length(pairs), "\n");
for pr in pairs do AppendTo(out, pr[1] - 1, " ", pr[2] - 1, "\n"); od;
CloseStream(out);
Print("EXPORTED ", FN, " n=", n, " |Aut|=", Size(A), " pairs=", Length(pairs), " ", StructureDescription(K), "\n");
QUIT;
