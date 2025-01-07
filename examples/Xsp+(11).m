AttachSpec("../main/CHIMP.spec");
load "../main/canring.m";
load "../main/hashimoto.m";

// Example: X = X_sp^+(11)
gens := [[0, 8, 2, 0], [9, 0, 0, 7]];  // GL2(N)-generators 
N := 11;  // Level
G := sub<GL(2,Integers(N)) | gens>;
Gamma := PSL2Subgroup(G);
M := ModularSymbols(Gamma, 2, Rationals(), 0); 
S := CuspidalSubspace(M); 
D := Decomposition(S, HeckeBound(S)); 
prec := 100;  // precision 
f1 := qEigenform(D[1],100);

// A known rational CM point on X corresponds to the elliptic curve 49.a2
// j(E) = -3375 = -1*3^(3)*5^(3)

E := EllipticCurve([1, -1, 0, -107, 552]);
C<i> := ComplexField();
tau := Periods(E)[2]/Periods(E)[1];  // this ordering makes sure tau is in the upper half plane 