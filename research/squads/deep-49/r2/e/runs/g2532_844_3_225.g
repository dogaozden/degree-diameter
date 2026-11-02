m:=844; k:=3; r:=225;
F := FreeGroup("a","b");
G := F / [F.1^m, F.2^k, F.2*F.1*F.2^-1*F.1^-r];
G := Image(IsomorphismPcGroup(G));
if Size(G) = 2532 then
Read("/home/user/degree-diameter/research/squads/deep-49/tools/export_group.g");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r2/e/runs/g2532_844_3_225.exp");
Print("GAPOK\n");
fi;
QUIT;
