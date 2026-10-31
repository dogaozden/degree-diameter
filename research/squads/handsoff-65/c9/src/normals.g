# writes OUT: for each normal subgroup of G=SmallGroup(ORDER,ID): line "size | idx idx ..." (table indices, identity 0)
G := SmallGroup(ORDER, ID);
el := Elements(G);
e := Position(el, One(G));
el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
out := OutputTextFile(OUT, false);
SetPrintFormattingStatus(out, false);
for N in NormalSubgroups(G) do
  AppendTo(out, Size(N), " ", StructureDescription(N), " | ",
    JoinStringsWithSeparator(List(Elements(N), x -> String(Position(el, x) - 1)), " "), "\n");
od;
CloseStream(out);
QUIT;
