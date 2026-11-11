# SmallGroups of orders 2440..2485 with |G/G'| <= 309, classified metacyclic or not (metacyclic = some cyclic normal
# subgroup <c> with G/<c> cyclic; c runs over class representatives). Writes sg_list.txt: n i q meta(0/1).
out := OutputTextFile("/home/user/degree-diameter/research/squads/deep-49/r2/c/sg_list.txt", false);
SetPrintFormattingStatus(out, false);
AppendTo(out, "# n i q meta\n");
for n in [2440..2485] do
  if SmallGroupsAvailable(n) then
    for i in [1..NrSmallGroups(n)] do
      G := SmallGroup(n, i);
      q := Product(AbelianInvariants(G));
      if q <= 309 then
        meta := false;
        for c in List(ConjugacyClasses(G), Representative) do
          if not meta then
            C := Subgroup(G, [c]);
            if IsNormal(G, C) and IsCyclic(FactorGroup(G, C)) then meta := true; fi;
          fi;
        od;
        m01 := 0; if meta then m01 := 1; fi;
        AppendTo(out, n, " ", i, " ", q, " ", m01, "\n");
      fi;
    od;
  else
    AppendTo(out, "# order ", n, " not in SmallGroups\n");
  fi;
od;
CloseStream(out);
Print("SGDONE\n");
QUIT;
