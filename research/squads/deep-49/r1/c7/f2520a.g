Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/famlib.g");
Print("counts ", NrSmallGroups(105), " ", NrSmallGroups(315), " ", NrSmallGroups(24), " ", NrSmallGroups(8), " ", NrSmallGroups(210), " ", NrSmallGroups(12), "\n");
PairFam("f2520a", List([1..NrSmallGroups(24)], i -> PcOf(24, i)), List([1..NrSmallGroups(105)], i -> PcOf(105, i)), DIR);
QUIT;
