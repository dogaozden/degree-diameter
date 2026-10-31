# Export a group for sdhaar.c: multiplication table (identity first, then AsSSortedList order) and one
# representative of every conjugacy class of automorphisms phi of order 2 (and, if ORD4 is set, of order 4) of K.
# usage: gap -q -c 'K:=SmallGroup(360,53);; FN:="x.txt";;' sdhaar.g
elms := AsSSortedList(K);
e := One(K);
elms := Concatenation([e], Filtered(elms, x -> x <> e));
n := Length(elms);
A := AutomorphismGroup(K);
iso := IsomorphismPermGroup(A);
P := Image(iso);
ords := [2]; if IsBound(ORD4) then ords := [2, 4]; fi;
reps := List(Filtered(ConjugacyClasses(P), c -> Order(Representative(c)) in ords), c -> PreImage(iso, Representative(c)));
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
AppendTo(out, n, "\n");
for a in elms do AppendTo(out, JoinStringsWithSeparator(List(elms, b -> String(Position(elms, a * b) - 1)), " "), "\n"); od;
AppendTo(out, Length(reps), "\n");
for g in reps do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(Position(elms, Image(g, x)) - 1)), " "), "\n"); od;
CloseStream(out);
Print("EXPORTED ", FN, " n=", n, " |Aut|=", Size(A), " phi classes=", Length(reps), " ", StructureDescription(K), "\n");
QUIT;
