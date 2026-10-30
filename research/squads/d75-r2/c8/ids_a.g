# family (a): G = C_p : C_(d*e), C_(d*e) acting on C_p with image of order d (kernel C_e central)
mkMeta := function(p, d, e)
  local Cp, C, r, aut, hom;
  Cp := CyclicGroup(IsPermGroup, p);;
  C := CyclicGroup(IsPermGroup, d*e);;
  r := PrimitiveRootMod(p)^((p-1)/d);;
  aut := AutomorphismGroup(Cp);;
  hom := GroupHomomorphismByImages(C, aut, [C.1], [GroupHomomorphismByImages(Cp, Cp, [Cp.1], [Cp.1^r])]);;
  return SemidirectProduct(C, hom, Cp);
end;;
