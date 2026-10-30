# Usage: gap -q -c 'ORDER:=90; ID:=2; OUT:="x";' gap_tab_gens.g -> x.txt (table, identity 0; same element order as
# ../../beyond-haar-d5/src/gap_tab_aut.g) and x.gens (generators of Aut(G) as image lists), x.info (structure, |Aut|)
G := SmallGroup(ORDER, ID);
el := Elements(G); e := Position(el, One(G));
el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
out := OutputTextFile(Concatenation(OUT, ".txt"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, String(ORDER), "\n");
for g in el do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, g*h) - 1)), " "), "\n"); od;
CloseStream(out);
A := AutomorphismGroup(G);
gens := GeneratorsOfGroup(A);
out := OutputTextFile(Concatenation(OUT, ".gens"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, String(Length(gens)), "\n");
for a in gens do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, Image(a, h)) - 1)), " "), "\n"); od;
CloseStream(out);
out := OutputTextFile(Concatenation(OUT, ".info"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, String(ORDER), " ", String(ID), " ", StructureDescription(G), " |Aut| = ", String(Size(A)), " abelian ", String(IsAbelian(G)), "\n");
CloseStream(out);
QUIT;
