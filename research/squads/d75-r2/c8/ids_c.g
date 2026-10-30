Read("/home/user/degree-diameter/research/squads/d75-r2/c8/ids_a.g");;
# family (c): C_n : C_k, y acting on C_n (n = p*q) by multiplication by u (u^k = 1)
mkC := function(n, k, u)
  local Cn, C, aut, hom;
  Cn := CyclicGroup(IsPermGroup, n);;
  C := CyclicGroup(IsPermGroup, k);;
  aut := AutomorphismGroup(Cn);;
  hom := GroupHomomorphismByImages(C, aut, [C.1], [GroupHomomorphismByImages(Cn, Cn, [Cn.1], [Cn.1^u])]);;
  return SemidirectProduct(C, hom, Cn);
end;;
