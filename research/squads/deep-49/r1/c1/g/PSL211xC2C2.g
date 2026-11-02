Read("/home/user/degree-diameter/research/squads/deep-49/r1/c1/export_group_c1.g");
G := Image(IsomorphismPermGroup(DirectProduct(PSL(2,11), CyclicGroup(2), CyclicGroup(2))));;
Print("PSL211xC2C2 size ", Size(G), "\n");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/PSL211xC2C2.exp");;
QUIT;
