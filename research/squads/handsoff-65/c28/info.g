G := SmallGroup(294,11);;
Print("order ", Size(G), " ", StructureDescription(G), "\n");
Print("orders ", Collected(List(AsList(G), Order)), "\n");
Print("cyc6 ", Number(Filtered(Set(List(AsList(G), g -> Subgroup(G,[g]))), H -> Size(H)=6)), "\n");
Print("aut ", Size(AutomorphismGroup(G)), "\n");
QUIT;
