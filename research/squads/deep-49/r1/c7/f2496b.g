Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/famlib.g");
F8 := MkFimg(8, 4);
Print("F8 ", Size(F8), " ", AbelianInvariants(F8), "\n");
PairFam("f2496F8", [F8], List([1..NrSmallGroups(24)], i -> PcOf(24, i)), DIR);
F12 := MkFimg(12, 12);
Print("F12 ", Size(F12), " ", AbelianInvariants(F12), "\n");
PairFam("f2496F12", [F12], List([1..NrSmallGroups(16)], i -> PcOf(16, i)), DIR);
QUIT;
