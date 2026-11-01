for ORD in [258,264,270] do
  n := NrSmallGroups(ORD);
  for i in [1..n] do
    G := SmallGroup(ORD, i);
    if not IsAbelian(G) then
      c6 := Filtered(ConjugacyClasses(G), c -> Order(Representative(c)) = 6);
      if Length(c6) > 0 then
        Print(ORD, " ", i, " ", StructureDescription(G), " classes6=", Length(c6), "\n");
      fi;
    fi;
  od;
od;
QUIT;
