Read("/home/user/degree-diameter/research/squads/deep-49/r1/c1/export_group_c1.g");
G := Image(IsomorphismPermGroup(DirectProduct(AlternatingGroup(6), CyclicGroup(7))));;
Print("A6xC7 size ", Size(G), "\n");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/A6xC7.exp");;
QUIT;
