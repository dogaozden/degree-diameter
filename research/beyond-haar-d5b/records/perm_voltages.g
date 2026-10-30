# usage: gap -q -c 'ORDER:=96; ID:=17; TABLE:="g96_17.txt"; VOLTS:=[6,1,2,39,45,81,20]; OUT:="x.perm";' perm_voltages.g
# Writes the elements with the given indices (element numbering of gap_tab_gens.g: identity 0, then Elements(G) order)
# as permutations of a small permutation representation of G, one per line (GAP cycle notation), and checks that the
# table in TABLE is the multiplication table of G in that numbering.
G := SmallGroup(ORDER, ID);
el := Elements(G); e := Position(el, One(G));
el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
iso := SmallerDegreePermutationRepresentation(Image(IsomorphismPermGroup(G)));
phi := IsomorphismPermGroup(G) * iso;
tab := ReadAsFunction(Concatenation(TABLE, ".g"))();
ok := ForAll([1..Size(G)], i -> ForAll([1..Size(G)], j -> el[i] * el[j] = el[tab[i][j] + 1]));
out := OutputTextFile(OUT, false); SetPrintFormattingStatus(out, false);
AppendTo(out, "# SmallGroup(", ORDER, ",", ID, ") = ", StructureDescription(G), " as permutations of degree ", LargestMovedPoint(Image(phi)), "; table check ", ok, "\n");
for v in VOLTS do AppendTo(out, v, " ", Image(phi, el[v + 1]), "\n"); od;
AppendTo(out, "gens ", JoinStringsWithSeparator(List(GeneratorsOfGroup(Image(phi)), String), " "), "\n");
CloseStream(out);
QUIT;
