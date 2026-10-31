# For SmallGroup(384, i), i in IDS: Q = G/G'G^2 = C2^r; print "i r v_0 .. v_{2^r-1}" where v_y = number of involutions
# of G (elements of order 2) in the coset with label y (label = exponent vector of the image w.r.t. Pcgs(Q), read as
# a binary number, first pcgs element = bit 0). Used by invcoset.py (inverse-pair refinement of the quotient test).
# usage: gap -q -A -c 'IDS:=[1..100];; FN:="ic.txt";;' invcoset.g
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
for id in IDS do
  G := SmallGroup(384, id);
  N := ClosureGroup(DerivedSubgroup(G), List(GeneratorsOfGroup(G), g -> g^2));
  N := NormalClosure(G, N);
  hom := NaturalHomomorphismByNormalSubgroup(G, N);
  Q := Image(hom);
  r := Length(AbelianInvariants(Q));
  v := List([1..2^r], k -> 0);
  if r > 0 then pq := Pcgs(Q); fi;
  for x in G do
    if Order(x) = 2 then
      if r = 0 then lab := 0; else
        ex := ExponentsOfPcElement(pq, Image(hom, x));
        lab := Sum([1..r], k -> ex[k] * 2^(k-1));
      fi;
      v[lab + 1] := v[lab + 1] + 1;
    fi;
  od;
  AppendTo(out, id, " ", r, " ", JoinStringsWithSeparator(List(v, String), " "), "\n");
od;
CloseStream(out);
QUIT;
