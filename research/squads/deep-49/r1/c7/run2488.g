Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/lib.g");
t := Runtime();
keep := MakeOrder(311, 8, "x");
Print("time ", Runtime()-t, " ms\n");
res := [];
for pr in keep do
  if not IsMetac(pr[2]) and Length(MinimalGeneratingSet(pr[2])) <= 3 then Add(res, pr); fi;
od;
Print("nonmetac d<=3: ", Length(res), "\n");
reps := DedupeG(List(res, p -> p[2]));
Print("iso classes: ", Length(reps), "\n");
for G in reps do
  Print(Size(G), " ab=", AbelianInvariants(G), " d=", Length(MinimalGeneratingSet(G)), "\n");
od;
Print("time ", Runtime()-t, " ms\n");
QUIT;
