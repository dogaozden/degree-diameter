# plain table export (same first lines as export_sd.g: "n ninv", n table rows, inverse row); identity has index 0.
# Usage: gap -q -c 'N:=360;; ID:=118;; OUT:="x.tab";;' export_plain.g
if not IsBound(G) then G := SmallGroup(N, ID); fi;
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
CloseStream(f);
QUIT;
