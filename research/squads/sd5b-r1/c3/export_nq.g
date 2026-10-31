# export_sd.g: a group G (SmallGroup(N, ID) unless G is bound) as a multiplication table plus the data of all its
# index-2 extensions G^ = G u G t (t^2 = c, t x t^-1 = beta(x)), for sdk.c.  Identity has index 0.
# Usage: gap -q -c 'N:=360;; ID:=118;; OUT:="x.ht";;' export_sd.g     (NOEXT:=1 skips the non-split records)
# Format: "n NINV" / n rows of the table (row i: i*j) / "inv" row / then
#   "ALPHA p" / beta / "CENT k" / k perms     for beta = identity (p = 1) and each class of involutions of Aut(G)
#                                               (c = e: split extensions), centralizer of beta in Aut(G);
#   "EXT c" / beta / "CENT k" / k perms       for each Aut(G)-class of pairs (beta, c), c <> e, beta(c) = c,
#                                               beta^2 = conjugation by c (non-split cosets: t^2 = c), with the
#                                               stabilizer of (beta, c) in Aut(G).
# Permutations are written as the 0-based images of 0..n-1.
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
wperm := function(p) AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(b^p - 1)), " "), "\n"); end;;
wcent := function(C)
  local gs, g;
  gs := GeneratorsOfGroup(C); if Length(gs) > 12 then gs := SmallGeneratingSet(C); fi;
  AppendTo(f, "CENT ", Length(gs), "\n");
  for g in gs do wperm(g); od;
end;;
A := AutomorphismGroup(G);;
toperm := a -> PermList(List([1..n], b -> pos(Image(a, els[old[b]])) + 1));;
P := Group(List(GeneratorsOfGroup(A), toperm), ());;
# x -> g^-1 x g as a permutation of indices 1..n (a homomorphism g -> conjperm(g) for GAP's left-to-right products)
conjperm := g -> PermList(List([1..n], b -> pos(g^-1 * els[old[b]] * g) + 1));;
gG := GeneratorsOfGroup(G);;
InnP := Group(List(gG, conjperm), ());;
hom := GroupHomomorphismByImagesNC(G, InnP, gG, List(gG, conjperm));;
Zl := List(Elements(Centre(G)), z -> z);;
AppendTo(f, "ALPHA 1\n"); wperm(()); wcent(P);
# non-split cosets for beta = identity: c central, c <> e, up to Aut(G)
if not IsBound(NOEXT) then
  cs := Filtered(List(Zl, z -> pos(z) + 1), i -> i <> 1);;
  for o in Orbits(P, cs) do
    AppendTo(f, "EXT ", o[1] - 1, "\n"); wperm(()); wcent(Stabilizer(P, o[1]));
  od;
fi;
for cl in ConjugacyClasses(P) do
  r := Representative(cl);
  if r = () then continue; fi;
  if Order(r) = 2 then AppendTo(f, "ALPHA 2\n"); wperm(r); wcent(Centralizer(P, r)); fi;
  if IsBound(NOEXT) then continue; fi;
  r2 := r^2;
  if not r2 in InnP then continue; fi;
  c0 := PreImagesRepresentative(hom, r2)^-1;;   # beta^2(x) = c0 x c0^-1
  cs := Filtered(List(Zl, z -> pos(c0 * z) + 1), i -> i <> 1 and i^r = i);;
  if Length(cs) = 0 then continue; fi;
  C := Centralizer(P, r);;
  for o in Orbits(C, cs) do
    AppendTo(f, "EXT ", o[1] - 1, "\n"); wperm(r); wcent(Stabilizer(C, o[1]));
  od;
od;
CloseStream(f);
