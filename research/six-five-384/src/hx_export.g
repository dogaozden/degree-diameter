# Fast export for haarex2/haarex3: multiplication table (identity = element 0) and Aut(K) generators as
# permutations of the element indices. Same file format as research/s65/tools/haarex2.g, but uses PositionSorted
# (the order-384 groups are pc groups), so a group exports in about a second.
# usage: gap -q -A -c 'K:=SmallGroup(384,5000);; FN:="x.txt";;' hx_export.g
srt := AsSSortedList(K);
e := One(K);
elms := Concatenation([e], Filtered(srt, x -> x <> e));
n := Length(elms);
pos := List(srt, x -> Position(elms, x));       # sorted index -> output index (1-based)
idx := x -> pos[PositionSorted(srt, x)] - 1;
A := AutomorphismGroup(K);
gens := GeneratorsOfGroup(A);
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
AppendTo(out, n, "\n");
for a in elms do AppendTo(out, JoinStringsWithSeparator(List(elms, b -> String(idx(a * b))), " "), "\n"); od;
AppendTo(out, Length(gens), "\n");
for g in gens do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(idx(Image(g, x)))), " "), "\n"); od;
CloseStream(out);
Print("EXPORTED ", FN, " n=", n, " |Aut|=", Size(A), " gens=", Length(gens), "\n");
QUIT;
