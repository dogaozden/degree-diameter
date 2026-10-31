Read("/home/user/degree-diameter/research/squads/sd5b-r1/c4/mk.g");
F := GF(13); a := Z(13)^4; z := Zero(F); o := One(F);
G := mkaff(13, [[[a,z],[z,o]],[[o,z],[z,a]]]);;
OUT := "/home/user/degree-diameter/research/squads/sd5b-r1/c4/B_aff13_c3c3.ht";; NOEXT := 1;;
Print("size ", Size(G), "\n");
Read("/home/user/degree-diameter/research/selfdual-d5/src/export_sd.g");
