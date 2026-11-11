Read("/home/user/degree-diameter/research/squads/deep-49/r1/c1/export_group_c1.g");
G := Image(IsomorphismPermGroup(DirectProduct(PSL(2,7), CyclicGroup(15))));;
Print("PSL27xC15 size ", Size(G), "\n");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/PSL27xC15.exp");;
QUIT;
