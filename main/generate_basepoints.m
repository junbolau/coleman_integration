gcd_and_lcm_for_fields := function(K1, K2) 
    // Return F, K, f1, f2, g1, g2, where f1 and f2 are the embeddings of F into K1 and K2, and g1 and g2 are the embeddings of K1 and K2 into K.
    e1, e2 := Explode(<0,0>);
    f1, f2, g1, g2 := Explode(<0,0,0,0>);
    K := Compositum(K1, K2);
    print(K);
    // First, extract the intersection F.
    for e in SubfieldLattice(K) do
        x := 0;
        y := 0;
        L := NumberField(e);
        if x eq 0 and IsIsomorphic(K1, L) then 
            e1 := e;
            x := 1;
        end if;
        if y eq 0 and IsIsomorphic(K2, L) then 
            e2 := e;
            y := 1;
        end if;
    end for;
    F := NumberField(e1 meet e2);
    print(F);
    // Next, find the embeddings g1 and g2. 
    for a in Subfields(K) do
        x := 0;
        y := 0;
        L,f := Explode(a);
        if x eq 0 and IsIsomorphic(K1, L) then 
            g1 := f;
            x := 1;
        end if;
        if y eq 0 and IsIsomorphic(K2, L) then 
            g2 := f;
            y := 1;
        end if;
    end for;
    print(g1);
    print(g2);
    // Finally, find the embeddings f1 and f2.
    x := 0;
    for aa in [K1, K2] do
        for a in Subfields(aa) do 
            L, f := Explode(a);
            if IsIsomorphic(F, L) then 
                if x eq 0 then 
                    f1 := f;
                    x := 1;
                else 
                    f2 := f;
                end if;
                break;
            end if;
        end for;
    end for;
    print(f1);
    print(f2);
    return F, K, f1, f2, g1, g2;
end function;

// Finds the intersection of Galois number fields K and L.
common_subfield := function(K, L)
    // printf "K = %o\nL = %o\n", K, L;
    for d in Reverse(Divisors(GCD(Degree(K), Degree(L)))) do
        if d eq 1 then 
            id := IdentityFieldMorphism(RationalField());
            return RationalField(), RationalField(), id, id, id;
        end if;
        for KL in CartesianProduct(Subfields(K, d), Subfields(L, d)) do
            boo, f := IsIsomorphic(KL[1][1], KL[2][1]);
            if not boo then continue; end if;
            MK := KL[1][1];
            ML := KL[2][1];
            fK := KL[1][2];
            fL := KL[2][2];
            // printf "Common subfield: %o\n", MK;
            return MK, ML, fK, fL, f;
        end for;
    end for;
    Error("You should not reach this stage!");
end function;

// Given a number field K, a prime pp of K above p, and a number field L, return a list of primes ppp of K above p "compatible" with pp. The fields K and L are assumed to be Galois over Q.
blah := function(K, L, pp, p)
    // First, find the intersection M of K and L.
    MK, ML, fK, fL, fMKML := common_subfield(K, L);
    if Degree(MK) eq 1 then 
        return [x[1] : x in Decomposition(MaximalOrder(L), p)];
    end if;
    // printf "pp = %o\n", pp;
    // Next, find the prime q of M below pp.
    found := false;
    for x in Decomposition(MaximalOrder(MK), p) do
        q, _ := Explode(x);
        q1, q2 := TwoElement(q);
        qK := ideal<MaximalOrder(K) | fK(q1), fK(q2)>;
        for y in Factorization(qK) do
            if y[1] eq pp then 
                found := true;
                break; 
            end if;
        end for;
        if found then break; end if;
    end for;
    assert found;
    // printf "The prime q of M below pp is %o\n", q;
    // Finally, find the primes of L above q.
    qL := ideal<MaximalOrder(L) | fL(fMKML(q1)), fL(fMKML(q2))>;
    ret := [x[1] : x in Factorization(qL)];
    // printf "The primes of L above q are %o\n", ret;
    return ret;
end function;

// Return: List whose elements are <E, Ebar, tau, H, pp>
asdf := function(p)
    found_j_invariants := {0, 1728 mod p};
    H_s := [];
    pp_s := [* *];
    ret := [* *];
    bd := 2*p^(1/2);
    R<x> := PolynomialRing(Integers());
    ap := -Floor(bd);
    repeat
        // First, get the j-invariant(s) associated to the order Z[phi], where tr(phi) = ap.
        printf "ap = %o\n", ap;
        K<phi> := NumberField(x^2 - ap*x + p);
        O := EquationOrder(K);
        tau := Evaluate(phi, InfinitePlaces(K)[1]);
        j_approx := jInvariant(tau);
        d := #PicardGroup(O);
        print(d);
        min_poly := MinimalPolynomial(j_approx,d);
        H<j> := NumberField(min_poly : DoLinearExtension := true);
        O_H := MaximalOrder(H);
        print(H);
        // Next, choose a suitable prime pp of H above p compatible with all the previous choices.
        if #H_s eq 0 then 
            pp := Decomposition(O_H, p)[1][1];
        else 
            F := Factorization(&+ [&meet blah(H_s[i], H, pp_s[i], p) : i in [1..#H_s]]);
            pp := F[1][1];
        end if;
        Append(~H_s, H);
        Append(~pp_s, pp);

        // Finally, get the 
        _, h := ResidueClassField(pp);
        j_conjugates := [r[1] : r in Roots(PolynomialRing(H)!min_poly)];
        printf "field is %o\n", H;
        printf "conjugates are %o\n", j_conjugates; 
        for j_c in j_conjugates do 
            j_cbar := h(O_H!j_c);
            printf "j = %o\n", j_cbar;
            if j_cbar in found_j_invariants then
                continue;
            end if;
            k := 27*j_c/(j_c-1728);
            kbar := 27*j_cbar/(j_cbar-1728);
            E_c := EllipticCurve([-k/4,-k/4]);
            E_cbar := EllipticCurve([-kbar/4, -kbar/4]);
            E_period := Periods(E_c, 1);
            tau_c := E_period[2]/E_period[1];
            
            Include(~found_j_invariants, j_cbar);
            Append(~ret, <j_cbar, E_c, E_cbar, H, pp, MinimalPolynomial(tau_c, 2)>);
        end for;
        ap +:= 1;
    until ap gt Floor(bd) or #found_j_invariants eq p;
    found_j_invariants;
    return ret;
end function;

find_possible_g_level_structure := function(N, H, Fr, size_A)
    /*
    INPUTS: 
    * "N" -- integer, level of H
    * "H" -- group, subgroup of GL2(N) 
    * "Fr" -- AlgMatElt, Frobenius matrix
    * "size_A" -- integer, order of automorphism group 
    */
    // g such that HgA = HgA*Fr (where Fr is either the Frobenius or Verschiebung depending on things)
    // size_A = 2 (tau = i), 3 (tau = zeta_3) or 1 (else)
    G := GL(2, Integers(N));
    ret := [**];
    A_matrices := [[1,0,0,1],[0,-1,1,0],[1,1,-1,0]];
    A := G!A_matrices[size_A];
    a_list := [A^(i-1) : i in [1..size_A]];
    already_seen := [**];
    T, phi := Transversal(G, H);
    for g in T do
        if &or[phi(g*a) in already_seen : a in a_list] then 
            continue;
        end if;
        if &or[g*Fr*a*g^(-1) in H : a in a_list] then 
            Append(~ret, g);
        end if;
        Append(~already_seen, g);
    end for;
    return ret;
end function;