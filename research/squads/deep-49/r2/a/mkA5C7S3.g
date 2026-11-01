Read("/home/user/degree-diameter/research/squads/deep-49/r2/a/export_r2a.g");
dir := "/home/user/degree-diameter/research/squads/deep-49/r2/a/g/";
Xg := Image(IsomorphismPermGroup(DirectProduct(CyclicGroup(7), SymmetricGroup(3))));
P := DirectProduct(AlternatingGroup(5), Xg);
G5 := Image(IsomorphismPermGroup(P));
Print("A5xC7S3 size ", Size(G5), " ab ", AbelianInvariants(G5), " classes ", NrConjugacyClasses(G5), "\n");
ExportGroup(G5, Concatenation(dir, "A5xC7S3.exp"));
Print("done\n");
QUIT;
