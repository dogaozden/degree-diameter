# aff_export.g: table of G = SmallGroup(N,ID) (identity index 0, as export.g) plus Aut(G) conjugacy class reps.
# Usage: gap -q -c 'N:=605;; ID:=4;; OUT:="x.aff";;' aff_export.g
G := SmallGroup(N, ID);;
n := Size(G);;
els := ShallowCopy(AsSSortedList(G));;
ix := PositionSorted(els, One(G));;
nw := function(i) if i = ix then return 0; elif i = 1 then return ix - 1; else return i - 1; fi; end;;
old := List([0..n-1], k -> 0);;
for i in [1..n] do old[nw(i) + 1] := i; od;
pos := x -> nw(PositionSorted(els, x));;
f := OutputTextFile(OUT, false);; SetPrintFormattingStatus(f, false);
ninv := Number(els, x -> Order(x) = 2);;
AppendTo(f, n, " ", ninv, "\n");
for a in [1..n] do
  x := els[old[a]];
  AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(pos(x * els[old[b]]))), " "), "\n");
od;
AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(pos(els[old[b]]^-1))), " "), "\n");
A := AutomorphismGroup(G);;
toperm := a -> PermList(List([1..n], b -> pos(Image(a, els[old[b]])) + 1));;
P := Group(List(GeneratorsOfGroup(A), toperm));;
cc := ConjugacyClasses(P);;
AppendTo(f, "AUT ", Size(P), " ", Length(cc), "\n");
for c in cc do
  r := Representative(c);
  AppendTo(f, "ALPHA ", Order(r), " ", Size(c), "\n");
  AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(b^r - 1)), " "), "\n");
od;
CloseStream(f);
QUIT;
