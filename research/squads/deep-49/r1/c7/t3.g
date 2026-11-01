Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/lib.g");
keep := MakeOrder(311, 8, "x");
for pr in keep do
  t := Runtime();
  mc := IsMetac(pr[2]);
  t2 := Runtime();
  d := Length(MinimalGeneratingSet(pr[2]));
  Print(pr[1], " metac ", mc, " d ", d, " ab ", AbelianInvariants(pr[2]), " t_meta ", t2-t, " t_d ", Runtime()-t2, "\n");
od;
QUIT;
