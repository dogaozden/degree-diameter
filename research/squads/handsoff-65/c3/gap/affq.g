# affine group F_q : C_k (C_k = subgroup of order k in GF(q)^*), acting on the q points of GF(q)
AffFq := function(q, k)
  local F, els, z, w, f, gens;
  F := GF(q); els := AsList(F); z := PrimitiveElement(F);
  f := DegreeOverPrimeField(F);
  gens := List([0..f-1], i -> PermList(List(els, x -> Position(els, x + z^i))));
  w := z^((q-1)/k);
  Add(gens, PermList(List(els, x -> Position(els, x * w))));
  return Group(gens);
end;
