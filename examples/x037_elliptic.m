AttachSpec("../main/CHIMP.spec");

function EllipticPoints(Gamma_G, N) 
    PSL := PSL2(Integers());
    coset := Transversal(PSL, Gamma_G);
    M1 := PSL![1,1,-1,0];
    M2 := PSL![0, -1, 1, 0];
   

    elliptic_points := [];
    for g in coset do
        if not ((g*M1*g^(-1)) in Gamma_G) then 
            Append(~elliptic_points, <g, 3>);
        elif not ((g*M2*g^(-1)) in Gamma_G) then
            Append(~elliptic_points, <g, 2>);
        end if;
    end for;

    return elliptic_points; 
end function; 

// Gamma0(37)

G := sub<GL(2, Integers(37))|[[10, 19, 0, 13], [32, 2, 0, 25]]>;
Gamma_G := PSL2Subgroup(G);
elliptic_points := EllipticPoints(Gamma_G, 37);

S := CuspForms(Gamma0(37), 2);
f0 := Basis(S)[1];  // f0 = q + q^3 - 2q^4 + O(q^6)
f1 := f0 - 2*Basis(S)[2];  // f1 = q - 2q^2 - 3q^3 + 2q^4 - 2q^5 + O(q^6)