# Export a group for haarex2.c: multiplication table (identity first) and generators of Aut(K) as permutations
# of the element indices. usage: gap -q -c 'K:=SmallGroup(351,12);; FN:="x.txt";;' haarex2.g
elms := AsSSortedList(K);
e := One(K);
elms := Concatenation([e], Filtered(elms, x -> x <> e));
n := Length(elms);
A := AutomorphismGroup(K);
gens := GeneratorsOfGroup(A);
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
AppendTo(out, n, "\n");
for a in elms do AppendTo(out, JoinStringsWithSeparator(List(elms, b -> String(Position(elms, a * b) - 1)), " "), "\n"); od;
AppendTo(out, Length(gens), "\n");
for g in gens do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(Position(elms, Image(g, x)) - 1)), " "), "\n"); od;
CloseStream(out);
Print("EXPORTED ", FN, " n=", n, " |Aut|=", Size(A), " gens=", Length(gens), " ", StructureDescription(K), "\n");
QUIT;
