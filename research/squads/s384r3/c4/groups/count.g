for N in [172,174,178,182,184,186,188,190] do
  L := Filtered([1..NrSmallGroups(N)], i -> not IsAbelian(SmallGroup(N,i)));
  Print(N, " nonabelian ", Length(L), " of ", NrSmallGroups(N), "\n");
od;
QUIT;
