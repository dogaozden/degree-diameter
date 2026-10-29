# Haar check (COMMON.md): normal subgroup of index h (=2) meeting H trivially
chk := function(n, i)
  local G, Hs, N, res;
  G := SmallGroup(n, i);
  res := Length(Filtered(NormalSubgroups(G), N -> Index(G, N) = 2)) ;
  Print("order ", n, " id ", i, " index-2 normal subgroups: ", res, "\n");
end;
chk(1176, 212);
QUIT;
