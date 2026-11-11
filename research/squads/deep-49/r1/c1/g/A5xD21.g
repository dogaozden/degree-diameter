Read("/home/user/degree-diameter/research/squads/deep-49/r1/c1/export_group_c1.g");
G := Image(IsomorphismPermGroup(DirectProduct(AlternatingGroup(5), DihedralGroup(42))));;
Print("A5xD21 size ", Size(G), "\n");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/A5xD21.exp");;
QUIT;
