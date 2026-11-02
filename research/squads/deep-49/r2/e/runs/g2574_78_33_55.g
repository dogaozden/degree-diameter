m:=78; k:=33; r:=55;
F := FreeGroup("a","b");
G := F / [F.1^m, F.2^k, F.2*F.1*F.2^-1*F.1^-r];
G := Image(IsomorphismPcGroup(G));
if Size(G) = 2574 then
Read("/home/user/degree-diameter/research/squads/deep-49/tools/export_group.g");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r2/e/runs/g2574_78_33_55.exp");
Print("GAPOK\n");
fi;
QUIT;
