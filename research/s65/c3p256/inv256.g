# involution counts of the groups of order 256 (ids FROM..TO); writes lines "id ninv" for non-abelian groups with ninv <= 15
out := OutputTextFile(Concatenation("inv256_", String(FROM), ".txt"), false); SetPrintFormattingStatus(out, false);
for i in [FROM..TO] do
  P := SmallGroup(256, i);
  if not IsAbelian(P) then
    k := Sum(Filtered(ConjugacyClasses(P), c -> Order(Representative(c)) = 2), Size);
    if k <= 11 then AppendTo(out, i, " ", k, "\n"); fi;
  fi;
od;
CloseStream(out);
QUIT;
