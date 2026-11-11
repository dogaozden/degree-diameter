# writes one GAP script per target group: g/NAME.g (export to g/NAME.exp)
import os
T = {
 "A7": "AlternatingGroup(7)",
 "A6xC7": "DirectProduct(AlternatingGroup(6), CyclicGroup(7))",
 "PSL27xC15": "DirectProduct(PSL(2,7), CyclicGroup(15))",
 "SL25x_C7C3": "DirectProduct(SL(2,5), SmallGroup(21,1))",
 "SL25xC21": "DirectProduct(SL(2,5), CyclicGroup(21))",
 "A5x_C7C6": "DirectProduct(AlternatingGroup(5), SmallGroup(42,1))",
 "A5xC42": "DirectProduct(AlternatingGroup(5), CyclicGroup(42))",
 "A5xD21": "DirectProduct(AlternatingGroup(5), DihedralGroup(42))",
 "A5xC3xD7": "DirectProduct(AlternatingGroup(5), CyclicGroup(3), DihedralGroup(14))",
 "A5xC2x_C7C3": "DirectProduct(AlternatingGroup(5), CyclicGroup(2), SmallGroup(21,1))",
 "S5xC21": "DirectProduct(SymmetricGroup(5), CyclicGroup(21))",
 "A5xC43": "DirectProduct(AlternatingGroup(5), CyclicGroup(43))",
 "PSL211xC4": "DirectProduct(PSL(2,11), CyclicGroup(4))",
 "PSL211xC2C2": "DirectProduct(PSL(2,11), CyclicGroup(2), CyclicGroup(2))",
}
d = os.path.dirname(os.path.abspath(__file__)) + "/g"
for name, expr in T.items():
    with open(f"{d}/{name}.g", "w") as f:
        f.write('Read("/home/user/degree-diameter/research/squads/deep-49/r1/c1/export_group_c1.g");\n')
        f.write(f'G := Image(IsomorphismPermGroup({expr}));;\n')
        f.write(f'Print("{name} size ", Size(G), "\\n");\n')
        f.write(f'ExportGroup(G, "{d}/{name}.exp");;\n')
        f.write('QUIT;\n')
print("ok", len(T))
