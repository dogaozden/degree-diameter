# c8: non-abelian groups of order 3k, k in 202..220, with a normal subgroup of index 3 (K ⊲ G, G/K = C3),
# and few involutions (<= 3) or odd order. Prints: order id ninv has_index3_normal
for n in [606, 609 .. 660] do
  if n mod 3 <> 0 then continue; fi;
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    if IsAbelian(G) then continue; fi;
    ninv := Number(AsList(G), x -> x <> One(G) and x^2 = One(G));
    if ninv > 3 then continue; fi;
    nn := Filtered(NormalSubgroups(G), H -> Index(G, H) = 3);
    Print(n, " ", i, " ", ninv, " ", Length(nn) > 0, "\n");
  od;
od;
QUIT;
