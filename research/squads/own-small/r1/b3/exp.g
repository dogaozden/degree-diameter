names := "/home/user/degree-diameter/research/squads/own-small/r1/b3/groups/names.txt";
PrintTo(names, "");
for n in [5..12] do
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n,i);
    L := AsList(G);
    id := One(G);
    L2 := Concatenation([id], Difference(L,[id]));
    f := Concatenation("/home/user/degree-diameter/research/squads/own-small/r1/b3/groups/g", String(n), "_", String(i), ".txt");
    PrintTo(f, n, "\n");
    for a in L2 do
      row := List(L2, b -> Position(L2, a*b)-1);
      AppendTo(f, JoinStringsWithSeparator(List(row, String), " "), "\n");
    od;
    AppendTo(names, n, " ", i, " ", StructureDescription(G), "\n");
  od;
od;
QUIT;
