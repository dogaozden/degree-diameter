Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/famlib.g");
F4 := MkFimg(4, 4);
Print("F4 ", Size(F4), " ", AbelianInvariants(F4), "\n");
PairFam("f2496F4", [F4], List([1..NrSmallGroups(48)], i -> PcOf(48, i)), DIR);
QUIT;
