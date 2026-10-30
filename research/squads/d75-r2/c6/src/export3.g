# export3.g (card c6): group table + order-3 subgroup classes + Stab(H) conjugacy-class reps of automorphisms.
# usage: gap -q -c 'N:=1980;; ID:=5;; OUT:="x.bh";;' export3.g      (or preset G:=<group>; OUT:="x.bh";;)
# Format: "n NINV" / n rows of the table (row i: i*j, 0-based, identity = 0) / inverse row /
#   per class of subgroups H = <a> of order 3 (one per G-class):  "H a NORM" (a = element index, NORM = |N_G(H)|)
#   followed by "BETA" lines: one per conjugacy class (under Stab_Aut(H)) of automorphisms beta with beta(H) = H,
#   each followed by the n images beta(x) (0-based) on the next line.
if not IsBound(G) then G := SmallGroup(N, ID); fi;
n := Size(G);;
els := ShallowCopy(AsSSortedList(G));;
ix := PositionSorted(els, One(G));;
nw := function(i) if i = ix then return 0; elif i = 1 then return ix - 1; else return i - 1; fi; end;;
old := List([0..n-1], k -> 0);;
for i in [1..n] do old[nw(i) + 1] := i; od;
pos := x -> nw(PositionSorted(els, x));;
f := OutputTextFile(OUT, false);; SetPrintFormattingStatus(f, false);
AppendTo(f, n, " 0\n");
for a in [1..n] do
  x := els[old[a]];
  AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(pos(x * els[old[b]]))), " "), "\n");
od;
AppendTo(f, JoinStringsWithSeparator(List([1..n], b -> String(pos(els[old[b]]^-1))), " "), "\n");
# subgroups of order 3, up to conjugacy in G
E3 := Filtered(els, x -> Order(x) = 3);;
subs := Set(List(E3, x -> Group(x)));;
orbs := Orbits(G, subs, function(s, g) return s^g; end);;
reps := List(orbs, o -> o[1]);;
A := AutomorphismGroup(G);;
toperm := a -> PermList(List([1..n], b -> pos(Image(a, els[old[b]])) + 1));;
Pg := Group(List(GeneratorsOfGroup(A), toperm));;
if Size(Pg) <> Size(A) then Print("WARNING: perm rep not faithful\n"); fi;
for H in reps do
  Hset := Set(List(AsList(H), x -> pos(x) + 1));;
  AppendTo(f, "H ", pos(First(AsList(H), x -> x <> One(G))), " ", Size(Normalizer(G, H)), "\n");
  stab := Stabilizer(Pg, Hset, OnSets);;
  for c in ConjugacyClasses(stab) do
    r := Representative(c);
    AppendTo(f, "BETA\n", JoinStringsWithSeparator(List([1..n], b -> String(b^r - 1)), " "), "\n");
  od;
od;
CloseStream(f);
QUIT;
