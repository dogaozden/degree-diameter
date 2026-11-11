Read("/home/user/degree-diameter/research/squads/deep-49/r2/a/exportpc_r2a.g");
dir := "/home/user/degree-diameter/research/squads/deep-49/r2/a/g/";
Xg := Image(IsomorphismPermGroup(DirectProduct(CyclicGroup(7), SymmetricGroup(3))));
G5 := Image(IsomorphismPermGroup(DirectProduct(AlternatingGroup(5), Xg)));
Print("A5xC7S3 size ", Size(G5), "\n");
ExportGroupPc(G5, Concatenation(dir, "A5xC7S3.exp"));
Print("done\n");
QUIT;
