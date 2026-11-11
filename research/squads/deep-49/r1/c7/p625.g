Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/famlib.g");
for i in [1..NrSmallGroups(625)] do
  P := PcOf(625, i);
  t := Runtime();
  A := AutomorphismGroup(P);
  Print(i, " ab ", AbelianInvariants(P), " |Aut| ", Size(A), " t ", Runtime()-t, "\n");
od;
QUIT;
