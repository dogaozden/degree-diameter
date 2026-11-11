Read("/home/user/degree-diameter/research/squads/deep-49/r1/c1/export_group_c1.g");
G := Image(IsomorphismPermGroup(DirectProduct(AlternatingGroup(5), CyclicGroup(3), DihedralGroup(14))));;
Print("A5xC3xD7 size ", Size(G), "\n");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/A5xC3xD7.exp");;
QUIT;
