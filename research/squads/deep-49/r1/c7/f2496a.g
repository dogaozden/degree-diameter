Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/famlib.g");
F6 := MkFimg(6, 6);
Print("F6 ", Size(F6), " ", AbelianInvariants(F6), "\n");
PairFam("f2496F6", [F6], List([1..NrSmallGroups(32)], i -> PcOf(32, i)), DIR);
QUIT;
