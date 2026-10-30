# Usage: gap -q -c 'ORDER:=96; ID:=2; OUT:="x";' gap_tab_autlist.g -> x.txt (table, identity 0, same element order as
# gap_tab_gens.g) and x.aut (k, then k automorphisms as image lists: all of Aut(G) if |Aut| <= 5000, else the first
# 5000 elements of an enumerator, which always include the identity). A subset of Aut containing the identity is
# enough for b4a1x's canonical test to stay complete (it then keeps more representatives).
G := SmallGroup(ORDER, ID);
el := Elements(G); e := Position(el, One(G));
el := Concatenation([el[e]], el{Difference([1..Size(G)], [e])});
out := OutputTextFile(Concatenation(OUT, ".txt"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, String(ORDER), "\n");
for g in el do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, g*h) - 1)), " "), "\n"); od;
CloseStream(out);
A := AutomorphismGroup(G);
if Size(A) <= 5000 then L := Elements(A); else en := Enumerator(A); L := List([1..5000], i -> en[i]); fi;
if not IdentityMapping(G) in L then L := Concatenation([IdentityMapping(G)], L{[1..Length(L)-1]}); fi;
out := OutputTextFile(Concatenation(OUT, ".aut"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, String(Length(L)), "\n");
for a in L do AppendTo(out, JoinStringsWithSeparator(List(el, h -> String(Position(el, Image(a, h)) - 1)), " "), "\n"); od;
CloseStream(out);
out := OutputTextFile(Concatenation(OUT, ".info"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, String(ORDER), " ", String(ID), " ", StructureDescription(G), " |Aut| = ", String(Size(A)), " used ", String(Length(L)), "\n");
CloseStream(out);
QUIT;
