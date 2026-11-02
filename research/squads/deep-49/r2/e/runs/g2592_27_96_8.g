m:=27; k:=96; r:=8;
F := FreeGroup("a","b");
G := F / [F.1^m, F.2^k, F.2*F.1*F.2^-1*F.1^-r];
G := Image(IsomorphismPcGroup(G));
if Size(G) = 2592 then
Read("/home/user/degree-diameter/research/squads/deep-49/tools/export_group.g");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r2/e/runs/g2592_27_96_8.exp");
Print("GAPOK\n");
fi;
QUIT;
