# Independent builder (job six-five-384): edge list of the Haar graph H(G,S), G = SmallGroup(ORD, ID), straight from
# GAP's group arithmetic. Element order: identity first, then AsSSortedList order (as in the exports); S is given by
# 0-based indices SIDX in that order. Vertex g of side A = index of g, of side B = n + index; edge g -- s*g.
# usage: gap -q -A -c 'ORD:=342;; ID:=12;; SIDX:=[0,2,4,19,118,207];; FN:="x.edges";;' haar_gap_edges.g
K := SmallGroup(ORD, ID);
e := One(K);
elms := Concatenation([e], Filtered(AsSSortedList(K), x -> x <> e));
n := Length(elms);
S := List(SIDX, i -> elms[i + 1]);
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
AppendTo(out, 2 * n, "\n");
for g in elms do for s in S do AppendTo(out, Position(elms, g) - 1, " ", n + Position(elms, s * g) - 1, "\n"); od; od;
CloseStream(out);
Print("S = ", S, "\n");
QUIT;
