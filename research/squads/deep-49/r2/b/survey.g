ncinv := function(G)
  local Z;
  Z := Center(G);
  return Number(Elements(G), x -> Order(x)=2 and not x in Z);
end;
Print("MIXSURVEY\n");
for n in [2486..2600] do if SmallGroupsAvailable(n) then for i in [1..NrSmallGroups(n)] do
  G := SmallGroup(n, i);
  c := ncinv(G);
  if c >= 10 then Print("M ", n, " ", i, " ", c, " ", AbelianInvariants(G), "\n"); fi;
od; fi; od;
Print("HUBSURVEY\n");
for n in [1992..2100] do if n mod 4 = 0 and SmallGroupsAvailable(n) then for i in [1..NrSmallGroups(n)] do
  G := SmallGroup(n, i);
  s4 := Number(ConjugacyClassesSubgroups(G), c -> Size(Representative(c))=4);
  Print("H ", n, " ", i, " ", AbelianInvariants(G), " ", Length(AbelianInvariants(G)), " sub4classes=", s4, " ", IsSolvable(G), "\n");
od; fi; od;
QUIT;
