-- Exact SchurRings plethysm check for d in {3,6,9}.
-- All calculations are over QQ.

needsPackage "SchurRings";

R = schurRing(QQ, s, 9);
V = s_{3};

rectangularCoefficient = (d) -> (
    target := toList(9 : (d // 3));
    expansion := plethysm(s_{d}, V);
    matches := select(listForm expansion, term -> term#0 == target);
    if #matches == 0 then 0 else matches#0#1
);

for d in {3, 6, 9} do (
    c := rectangularCoefficient(d);
    print("d = " | toString d);
    print("target = " | toString toList(9 : (d // 3)));
    print("scalar = " | toString c);
    assert(c == 0);
);

print("RESULT M2 SchurRings exact plethysm d={3,6,9} = 0");
exit 0;
