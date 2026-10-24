# Sanity check: abelian invariants of a nonabelian group are those of G/G'
Print("check S4: ", AbelianInvariants(SymmetricGroup(4)), "  D12=SmallGroup(12,4): ", AbelianInvariants(SmallGroup(12,4)), "\n");
for n in Concatenation([1093..1119], [1121..1140]) do
  if not SmallGroupsAvailable(n) then
    Print("NA ", n, "\n");
  else
    for i in [1..NumberSmallGroups(n)] do
      G := SmallGroup(n,i);
      ab := AbelianInvariants(G);
      o := Product(ab);
      k := Number(ab, x -> x > 1);
      if o <= 24 and k <= 3 then
        Print("CAND ", n, " ", i, " ", StructureDescription(G), " ", o, " ", ab, "\n");
      fi;
    od;
  fi;
od;
QUIT;
