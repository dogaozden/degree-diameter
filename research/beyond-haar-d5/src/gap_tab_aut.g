# Usage: gap -q -c 'ORDER:=90; ID:=2; OUT:="x";' src/gap_tab_aut.g  -> x.txt (table, identity 0) and x.aut (Aut(G))
G := SmallGroup(ORDER, ID);
el := Elements(G); e := Position(el, One(G));
el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
out := OutputTextFile(Concatenation(OUT, ".txt"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, String(ORDER), "\n");
for g in el do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, g*h) - 1)), " "), "\n"); od;
CloseStream(out);
A := AutomorphismGroup(G);
out := OutputTextFile(Concatenation(OUT, ".aut"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, String(Size(A)), "\n");
for a in Elements(A) do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, Image(a, h)) - 1)), " "), "\n"); od;
CloseStream(out);
Print(StructureDescription(G), " |Aut| = ", Size(A), "\n");
QUIT;
