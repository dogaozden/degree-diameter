Read("/home/user/degree-diameter/research/squads/deep-49/r1/c1/export_group_c1.g");
G := Image(IsomorphismPermGroup(DirectProduct(SL(2,5), SmallGroup(21,1))));;
Print("SL25x_C7C3 size ", Size(G), "\n");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/SL25x_C7C3.exp");;
QUIT;
