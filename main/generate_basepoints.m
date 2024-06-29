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
    found_j_invariants := {};
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
        min_poly := MinimalPolynomial(j_approx,d);
        H<j> := NumberField(min_poly : DoLinearExtension := true);
        O_H := MaximalOrder(H);
        
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
        for j_c in j_conjugates do 
            j_cbar := h(O_H!j_c);
            j_cbar;
            if j_cbar in found_j_invariants then
                continue;
            end if;
            E_c := EllipticCurveFromjInvariant(j_c);
            E_cint := IntegralModel(E_c);
            E_period := Periods(E_cint, 1);
            tau_c := E_period[2]/E_period[1];
            try
                Ebar_c := EllipticCurve([h(O_H!c) : c in Coefficients(E_cint)]);
            catch e
                // KodairaSymbol(E_cint, pp);
                // j_cbar;
                continue;
            end try;
            Include(~found_j_invariants, j_cbar);
            Append(~ret, <j_cbar, E_cint, Ebar_c, H, pp, MinimalPolynomial(tau_c, 2)>);
        end for;
        ap +:= 1;
    until ap gt Floor(bd) or #found_j_invariants eq p;
    found_j_invariants;
    return ret;
end function;

