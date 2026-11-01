# A5 x (C7 x S3): Aut generators = (Aut(A5) x 1) and (1 x Aut(C7 x S3)); each is an automorphism of the direct product.
dir := "/home/user/degree-diameter/research/squads/deep-49/r2/a/g/";
Xg := Image(IsomorphismPermGroup(DirectProduct(CyclicGroup(7), SymmetricGroup(3))));
A := AlternatingGroup(5);
P := DirectProduct(A, Xg);
e1 := Embedding(P, 1); e2 := Embedding(P, 2); pr1 := Projection(P, 1); pr2 := Projection(P, 2);
alphas := GeneratorsOfGroup(AutomorphismGroup(A));
betas := GeneratorsOfGroup(AutomorphismGroup(Xg));
psis := Concatenation(
  List(alphas, al -> function(g) return Image(e1, Image(al, Image(pr1, g))) * Image(e2, Image(pr2, g)); end),
  List(betas, be -> function(g) return Image(e1, Image(pr1, g)) * Image(e2, Image(be, Image(pr2, g))); end));
Print("A5xC7S3 size ", Size(P), " classes ", NrConjugacyClasses(P), " aut gens ", Length(psis), "\n");
L := ShallowCopy(AsSSortedList(P)); n := Length(L);
pos := Position(L, One(P)); L[pos] := L[1]; L[1] := One(P);
gens := SmallGeneratingSet(P);
out := OutputTextFile(Concatenation(dir, "A5xC7S3.exp"), false); SetPrintFormattingStatus(out, false);
AppendTo(out, n, " ", Length(gens), "\n");
for g in gens do
  AppendTo(out, JoinStringsWithSeparator(List(List(L, x -> Position(L, x * g) - 1), String), " "), "\n");
od;
AppendTo(out, Length(psis), "\n");
for psi in psis do
  AppendTo(out, JoinStringsWithSeparator(List(List(gens, g -> Position(L, psi(g)) - 1), String), " "), "\n");
od;
CloseStream(out);
Print("done\n");
QUIT;
