m:=253; k:=10; r:=24;
F := FreeGroup("a","b");
G := F / [F.1^m, F.2^k, F.2*F.1*F.2^-1*F.1^-r];
G := Image(IsomorphismPcGroup(G));
if Size(G) <> 2530 then Print("SIZE MISMATCH\n"); QUIT; fi;
Read("/home/user/degree-diameter/research/squads/deep-49/tools/export_group.g");
ExportGroup(G, "/home/user/degree-diameter/research/squads/deep-49/r1/c2/runs/g2530_253_10_24.exp");
Print("GAPOK\n");
QUIT;
