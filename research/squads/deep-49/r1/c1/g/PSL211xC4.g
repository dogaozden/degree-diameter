Read("/home/user/degree-diameter/research/squads/deep-49/r1/c1/export_group_c1.g");
G := Image(IsomorphismPermGroup(DirectProduct(PSL(2,11), CyclicGroup(4))));;
Print("PSL211xC4 size ", Size(G), "\n");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/PSL211xC4.exp");;
QUIT;
