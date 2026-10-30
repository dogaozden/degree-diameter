Read("/home/user/degree-diameter/research/squads/d75-r2/c8/ids_a.g");;
mkB := function(m, p, d)
  return Image(IsomorphismPcGroup(DirectProduct(CyclicGroup(IsPermGroup, m), mkMeta(p, d, 1))));
end;;
mkSL := function(m)
  return Image(IsomorphismPcGroup(DirectProduct(SpecialLinearGroup(2,3), CyclicGroup(IsPermGroup, m))));
end;;
mkGL := function(m)
  return Image(IsomorphismPcGroup(DirectProduct(GL(2,3), CyclicGroup(IsPermGroup, m))));
end;;
mkO := function(m)
  return DirectProduct(SmallGroup(48,28), CyclicGroup(IsPermGroup, m));
end;;
mkSL25 := function(m)
  return Image(IsomorphismPcGroup(DirectProduct(SpecialLinearGroup(2,5), CyclicGroup(IsPermGroup, m))));
end;;
