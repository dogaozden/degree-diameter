# c4: affine groups F_p^2 : H (faithful H in GL(2,p)) and two non-faithful variants; each file defines G.
mkaff := function(p, mats)
  local F, vs, gens, o, z, e1, e2, M;
  F := GF(p); z := Zero(F); o := One(F);
  vs := AsList(FullRowSpace(F, 2));
  e1 := First(vs, x -> x[1] = o and x[2] = z);
  e2 := First(vs, x -> x[1] = z and x[2] = o);
  gens := [ PermList(List(vs, v -> Position(vs, v + e1))),
            PermList(List(vs, v -> Position(vs, v + e2))) ];
  for M in mats do
    Add(gens, PermList(List(vs, v -> Position(vs, v * M))));
  od;
  return Group(gens);
end;;
# N = C5 x C5 x C31 with an involutory automorphism phi; G = N : <phi>, realised as a permutation group
semi_N := function(phiimg)   # phiimg: function(gens) -> images of the three generators
  local N, gN, elN, phi, Rg, Pphi;
  N := DirectProduct(CyclicGroup(5), CyclicGroup(5), CyclicGroup(31));
  gN := GeneratorsOfGroup(N);
  elN := AsList(N);
  Rg := List(gN, g -> PermList(List(elN, x -> Position(elN, x * g))));
  phi := GroupHomomorphismByImagesNC(N, N, gN, phiimg(gN));
  Pphi := PermList(List(elN, x -> Position(elN, Image(phi, x))));
  return Group(Concatenation(Rg, [Pphi]));
end;;
