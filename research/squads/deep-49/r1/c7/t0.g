Print("GAP ok ", GAPInfo.Version, "\n");
Print("SmallGroups avail: ", IsBound(NrSmallGroups), "\n");
for n in [2488,2492,2496,2499,2500,2502,2504,2508,2511,2512,2516,2520,2528] do
  Print(n, " ", Collected(Factors(n)), "\n");
od;
D := SemidirectProduct;
Print(Display(SemidirectProduct), "\n");
QUIT;
