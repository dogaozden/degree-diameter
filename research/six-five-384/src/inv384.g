# Invariants of SmallGroup(384, i) for i in [I0..I1]: abelian invariants, number of involutions, |Z(G)|,
# whether the Sylow 3-subgroup is normal, IdGroup of G/O_3(G) when it is (a group of order 128).
# usage: gap -q -A -c 'I0:=1;; I1:=100;; FN:="inv.txt";;' inv384.g
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
for i in [I0..I1] do
  G := SmallGroup(384, i);
  ab := AbelianInvariants(G);
  ninv := Number(G, x -> Order(x) = 2);
  z := Size(Centre(G));
  P3 := SylowSubgroup(G, 3);
  n3 := IsNormal(G, P3);
  if n3 then q := IdGroup(G / P3)[2]; else q := 0; fi;
  d := Length(Filtered(ab, x -> x mod 2 = 0));
  AppendTo(out, i, " ab=", JoinStringsWithSeparator(List(ab, String), ","), " r2=", d, " inv=", ninv, " z=", z,
     " n3=", n3, " q128=", q, " dl=", DerivedLength(G), "\n");
od;
CloseStream(out);
QUIT;
