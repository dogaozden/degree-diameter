Read("/home/user/degree-diameter/research/squads/deep-49/tools/export_group.g");
out := OutputTextFile("survey.tsv", false); SetPrintFormattingStatus(out, false);
for n in [2486..2530] do
  if SmallGroupsAvailable(n) then
    for i in [1..NumberSmallGroups(n)] do
      G := SmallGroup(n, i); ab := AbelianInvariants(G);
      if Product(ab) <= 309 and Length(ab) <= 3 then
        AppendTo(out, n, "\t", i, "\t", ab, "\t", Size(Centre(G)), "\t", StructureDescription(G), "\n");
        ExportGroup(G, Concatenation("grp/g", String(n), "_", String(i), ".exp"));
      fi;
    od;
  fi;
od;
CloseStream(out);
QUIT;
