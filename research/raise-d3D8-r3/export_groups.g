# Round 3: export multiplication tables of all SmallGroups of orders 25..36 (identity code 0), same format as round 2.
# Usage: gap -q -o 4g export_groups.g   (writes groups/g<n>.txt; then perl -0pi -e 's/\\\n//g' on each file)
Dir := "/home/user/degree-diameter/research/raise-d3D8-r3/groups/";
ords := [25..36];
for n in ords do
  f := Concatenation(Dir, "g", String(n), ".txt");
  PrintTo(f, "");
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    N := Size(G);
    els := Concatenation([One(G)], Filtered(AsSortedList(G), x -> x <> One(G)));
    AppendTo(f, "G ", String(n), " ", String(i), " ", String(N), "\n");
    for a in [1..N] do
      s := "";
      for b in [1..N] do
        s := Concatenation(s, String(Position(els, els[a]*els[b]) - 1), " ");
      od;
      AppendTo(f, s, "\n");
    od;
  od;
  Print("order ", n, " done: ", NrSmallGroups(n), " groups\n");
od;
QUIT;
