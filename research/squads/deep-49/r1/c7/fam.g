Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/lib.g");
# F(k): C13 : C_k with C_k acting faithfully through an element of order k (k | 12)
MkF := function(k)
  local C, N, a, hom;
  N := CyclicGroup(IsPermGroup, 13);
  C := CyclicGroup(IsPermGroup, k);
  a := First(Elements(AutomorphismGroup(N)), x -> Order(x) = k);
  hom := GroupHomomorphismByImages(C, AutomorphismGroup(N),
           [C.1], [a]);
  return SemidirectProduct(C, hom, N);
end;
F4 := Image(IsomorphismPcGroup(MkF(4)));
Print("F4 ", Size(F4), " ", AbelianInvariants(F4), "\n");
Y := Image(IsomorphismPcGroup(SmallGroup(48, 3)));
G := DirectProduct(F4, Y);
Print("G ", Size(G), " ", AbelianInvariants(G), " d ", Length(MinimalGeneratingSet(G)), "\n");
t := Runtime();
Print("metac ", IsMetac(G), " t ", Runtime()-t, "\n");
t := Runtime();
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c7/exp/test2496.exp");
Print("export t ", Runtime()-t, "\n");
QUIT;
