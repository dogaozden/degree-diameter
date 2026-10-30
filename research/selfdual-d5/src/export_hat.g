# export_hat.g: a group H of order 2n (SmallGroup(N, ID)) as a multiplication table plus, for each normal subgroup
# of index 2 with IdGroup SUBID (any if SUBID is unbound), a line "SUB" with the 0/1 membership of the elements.
# For the independent brute-force check src/brute.c.  Usage: gap -q -c 'N:=672;; ID:=1048;; OUT:="x.hat";;' export_hat.g
H := SmallGroup(N, ID);;
n := Size(H);;
els := ShallowCopy(AsSSortedList(H));;
ix := PositionSorted(els, One(H));;
nw := function(i) if i = ix then return 0; elif i = 1 then return ix - 1; else return i - 1; fi; end;;
old := List([0..n-1], k -> 0);;
for i in [1..n] do old[nw(i) + 1] := i; od;
pos := x -> nw(PositionSorted(els, x));;
f := OutputTextFile(OUT, false);; SetPrintFormattingStatus(f, false);
AppendTo(f, n, "\n");
for a in [1..n] do
  x := els[old[a]];
  AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(pos(x * els[old[b]]))), " "), "\n");
od;
for R in Filtered(NormalSubgroups(H), R -> Index(H, R) = 2) do
  if IsBound(SUBID) and IdGroup(R) <> SUBID then continue; fi;
  AppendTo(f, "SUB ", JoinStringsWithSeparator(List([1..n], b -> String(Number([els[old[b]]], y -> y in R))), " "), "\n");
od;
CloseStream(f);
QUIT;
