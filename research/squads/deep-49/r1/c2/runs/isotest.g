SetPrintFormattingStatus("*stdout*", false);
mk := function(m,k,r)
  local F, G;
  F := FreeGroup("a","b");
  G := F / [F.1^m, F.2^k, F.2*F.1*F.2^-1*F.1^-r];
  return Image(IsomorphismPcGroup(G));
end;
t:=Runtime();
G1 := mk(23,110,2); G2 := mk(46,55,3);
Print("built ", Runtime()-t, "\n");
I := IsomorphismGroups(G1, G2);
Print("iso ", I <> fail, " ", Runtime()-t, "\n");
G3 := mk(23,110,5);
Print("iso2 ", IsomorphismGroups(G1, G3) <> fail, " ", Runtime()-t, "\n");
QUIT;
