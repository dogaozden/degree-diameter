Chk := function(ORD, id, idx)
  local G, Hs, H, s;
  G := SmallGroup(ORD, id);
  if not IsPermGroup(G) then G := Image(IsomorphismPermGroup(G)); fi;
  Hs := Filtered(ConjugacyClassesSubgroups(G), c -> Size(Representative(c)) = 3);
  Hs := List(Hs, Representative);
  Print(ORD, " group ", id, " classes of order-3 subgroups ", Length(Hs), " cores ", List(Hs, H -> Size(Core(G, H))), "\n");
end;
Chk(1791, 3); Chk(1734, 5); Chk(1785, 1);
QUIT;
