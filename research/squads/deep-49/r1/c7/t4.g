Read("/home/user/degree-diameter/research/squads/deep-49/r1/c7/lib.g");
keep := MakeOrder(311, 8, "x");
Q := Filtered(keep, p -> p[1]=5);
t := Runtime(); Print("iso1 ", IsomorphismGroups(Q[1][2], Q[2][2]) <> fail, " ", Runtime()-t, "\n");
t := Runtime(); Print("iso2 ", IsomorphismGroups(Q[1][2], Q[3][2]) <> fail, " ", Runtime()-t, "\n");
t := Runtime(); Print("iso3 ", IsomorphismGroups(Q[1][2], Q[5][2]) <> fail, " ", Runtime()-t, "\n");
QUIT;
