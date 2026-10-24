G1 := PcGroupCode(3732073212403969685562167,1372);;
G2 := PcGroupCode(3732073156506459280876343,1372);;
Print("sizes ", Size(G1), " ", Size(G2), " ", StructureDescription(G1), "\n");
Print("isomorphic: ", IsomorphismGroups(G1, G2) <> fail, "\n");
QUIT;
