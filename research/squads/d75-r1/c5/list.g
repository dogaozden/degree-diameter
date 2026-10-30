LO:=661;; HI:=720;; SKIP:=[672,704,720];;
# list_groups.g: non-abelian SmallGroups of orders LO..HI (except those in SKIP) with their number of involutions.
for n in [LO..HI] do
  if n in SKIP then continue; fi;
  for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i);
    if not IsAbelian(G) then
      Print(n, " ", i, " ", Number(ConjugacyClasses(G), c -> Order(Representative(c)) = 2 ) , " ",
            Sum(Filtered(ConjugacyClasses(G), c -> Order(Representative(c)) = 2), Size), "\n");
    fi;
  od;
od;
QUIT;
