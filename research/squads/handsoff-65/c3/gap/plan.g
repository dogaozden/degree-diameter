# prints, for each group in GROUPS (list of [label, group]), the orders h with 2|G|/h in [686,800], h>=4
Ch := function(m)
  local hs;
  hs := Filtered([4..m], h -> m mod h = 0 and 686 <= 2*m/h and 2*m/h <= 800);
  return hs;
end;
for gr in GROUPS do
  m := Size(gr[2]);
  Print(gr[1], " |G|=", m, " h=", Ch(m), "\n");
od;
QUIT;
