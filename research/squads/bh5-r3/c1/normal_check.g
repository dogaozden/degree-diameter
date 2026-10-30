Chk := function(ORD, id)
  local G, cl, res, x, S;
  G := SmallGroup(ORD, id);
  if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
  res := [];
  for cl in ConjugacyClasses(G) do
    x := Representative(cl);
    if Order(x) = 3 then S := Subgroup(G, [x]); Add(res, IsNormal(G, S)); fi;
  od;
  Print(ORD, " ", id, " order-3 subgroup classes normal? ", res, "\n");
end;
Chk(1815, 3);
QUIT;
