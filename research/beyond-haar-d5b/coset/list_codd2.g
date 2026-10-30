# usage: gap -q -c 'ORDER:=1248;' list_codd2.g  -> prints the ids of SmallGroup(ORDER, i) whose Hall subgroup of odd
# order is cyclic and normal (G = C_k : P with P a 2-group); "direct" marks the direct products C_k x P.
odd := Product(Filtered(FactorsInt(ORDER), p -> p <> 2));
res := []; dir := [];
for i in [1..NrSmallGroups(ORDER)] do
  G := SmallGroup(ORDER, i);
  K := HallSubgroup(G, Filtered(Set(FactorsInt(ORDER)), p -> p <> 2));
  if IsCyclic(K) and IsNormal(G, K) then Add(res, i);
    P := SylowSubgroup(G, 2); if IsNormal(G, P) then Add(dir, i); fi; fi;
od;
Print("ORDER ", ORDER, " semidirect ", Length(res), " direct ", Length(dir), "\n");
Print("IDS ", res, "\n"); Print("DIRECT ", dir, "\n");
QUIT;
