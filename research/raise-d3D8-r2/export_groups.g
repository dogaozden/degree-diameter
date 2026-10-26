# export multiplication tables of all SmallGroups of the given orders (0-based codes, identity = 0)
Dir := "/tmp/claude-0/-home-user-degree-diameter/13af3a61-2560-529d-a65f-9b95e2d73314/scratchpad/tl/groups/";
ords := Concatenation([37..46], [49..60], [73..90], [145..180]);
for n in ords do
  f := Concatenation(Dir, "g", String(n), ".txt");
  PrintTo(f, "");
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    N := Size(G);
    if IsSolvableGroup(G) then
      pcgs := Pcgs(G);
      ro := RelativeOrders(pcgs);
      els := [];
      for c in [0..N-1] do
        e := []; m := c;
        for j in [1..Length(ro)] do
          Add(e, m mod ro[j]); m := QuoInt(m, ro[j]);
        od;
        Add(els, PcElementByExponents(pcgs, e));
      od;
      code := function(g)
        local e, c, m, j;
        e := ExponentsOfPcElement(pcgs, g); c := 0; m := 1;
        for j in [1..Length(ro)] do
          c := c + e[j] * m; m := m * ro[j];
        od;
        return c;
      end;
    else
      els := Concatenation([One(G)], Filtered(AsSortedList(G), x -> x <> One(G)));
      code := function(g) return Position(els, g) - 1; end;
    fi;
    AppendTo(f, "G ", String(n), " ", String(i), " ", String(N), "\n");
    for a in [0..N-1] do
      s := "";
      for b in [0..N-1] do
        s := Concatenation(s, String(code(els[a+1]*els[b+1])), " ");
      od;
      AppendTo(f, s, "\n");
    od;
  od;
  Print("order ", n, " done\n");
od;
QUIT;
