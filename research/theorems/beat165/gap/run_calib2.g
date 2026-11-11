Read("cosetsearch2.g");
log := "calib2.log";
PrintTo(log, "calibration (v2): D<=5 coset graphs, max degree <= 16, sides 300..54241, total >= 2000\n");
for nm in ["L3(4)", "U3(4)", "U3(5)", "L3(5)", "M22", "J2", "S4(4)", "A9", "M12", "L2(64)", "L2(81)", "S6(2)",
           "A10", "L3(7)", "U4(3)", "G2(3)", "S4(5)", "U3(8)", "U3(7)", "L4(3)"] do
  SearchTom2(nm, 16, 6, 300, 54241, 2000, log);
od;
QUIT;
