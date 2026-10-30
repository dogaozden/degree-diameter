# c1 variant of research/d75-raise/src/export.g: table, inverses and the ALPHA 4 classes of Aut(G) only (CENT 0).
# export.g: write a group of order n (SmallGroup(N, ID)) as a multiplication table plus representatives of the
# conjugacy classes of automorphisms of prime order 2, 3, 5, 7 (with generators of their centralizers in Aut(G)),
# for haar75.c.  Identity has index 0.  Usage: gap -q -c 'N:=600;; ID:=54;; OUT:="x.ht";;' export.g
# Format: "n NINV" / n rows of the table (row i: i*j, j = 0..n-1) / "inv" row / per automorphism:
#   "ALPHA p" / perm (n images) / "CENT k" / k perms.
if not IsBound(G) then G := SmallGroup(N, ID); fi;
n := Size(G);;
els := ShallowCopy(AsSSortedList(G));;
ix := PositionSorted(els, One(G));;
# new index of sorted position i: swap ix <-> 1, then 0-based
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
if not IsBound(NOAUT) then
  A := AutomorphismGroup(G);;
  toperm := a -> PermList(List([1..n], b -> pos(Image(a, els[old[b]])) + 1));;
  P := Group(List(GeneratorsOfGroup(A), toperm), ());;
  # order-4 classes only (c1 card): ALPHA 4 records with an empty centralizer list
  for c in ConjugacyClasses(P) do
    r := Representative(c);
    if Order(r) = 4 then
      AppendTo(f, "ALPHA ", 4, "\n");
      AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(b^r - 1)), " "), "\n");
      AppendTo(f, "CENT 0\n");
    fi;
  od;
fi;
CloseStream(f);
QUIT;
