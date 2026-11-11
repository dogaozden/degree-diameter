# orbit representatives (codes) of Aut(G) on G, same encoding as export_groups.g (solvable groups of these orders)
Dir := "/tmp/claude-0/-home-user-degree-diameter/13af3a61-2560-529d-a65f-9b95e2d73314/scratchpad/tl/groups/";
ords := [37..46];
for n in ords do
  f := Concatenation(Dir, "reps_", String(n), ".txt");
  PrintTo(f, "");
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    N := Size(G);
    pcgs := Pcgs(G);
    ro := RelativeOrders(pcgs);
    code := function(g)
      local e, c, m, j;
      e := ExponentsOfPcElement(pcgs, g); c := 0; m := 1;
      for j in [1..Length(ro)] do
        c := c + e[j] * m; m := m * ro[j];
      od;
      return c;
    end;
    A := AutomorphismGroup(G);
    orbs := Orbits(A, Elements(G), OnPoints);
    reps := List(orbs, o -> code(o[1]));
    Sort(reps);
    AppendTo(f, "R ", String(n), " ", String(i), " ", String(Length(reps)), " ", JoinStringsWithSeparator(List(reps, String), " "), "\n");
  od;
  Print("order ", n, " done\n");
od;
QUIT;
