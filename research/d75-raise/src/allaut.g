# allaut.g: all automorphisms of G as permutations of the export.g element numbering (one line each), to OUT.
if not IsBound(G) then G := SmallGroup(N, ID); fi;
n := Size(G);; els := ShallowCopy(AsSSortedList(G));; ix := PositionSorted(els, One(G));;
nw := function(i) if i = ix then return 0; elif i = 1 then return ix - 1; else return i - 1; fi; end;;
old := List([0..n-1], k -> 0);; for i in [1..n] do old[nw(i) + 1] := i; od;
pos := x -> nw(PositionSorted(els, x));;
A := AutomorphismGroup(G);;
P := Group(List(GeneratorsOfGroup(A), a -> PermList(List([1..n], b -> pos(Image(a, els[old[b]])) + 1))), ());;
f := OutputTextFile(OUT, false);; SetPrintFormattingStatus(f, false);
AppendTo(f, Size(P), "\n");
for p in Enumerator(P) do AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(b^p - 1)), " "), "\n"); od;
CloseStream(f); QUIT;
