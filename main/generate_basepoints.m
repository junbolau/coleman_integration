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

// Given a number field K, a prime pp of K above p, and a number field L, return a list of primes ppp of L above p "compatible" with pp. The fields K and L are assumed to be Galois over Q.
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


find_possible_g_level_structure := function(N, H, Fr, size_A)
    // g such that HgA = HgA*Fr (where Fr is either the Frobenius or Verschiebung depending on things)
    // size_A = 2 (tau = i), 3 (tau = zeta_3) or 1 (else)
    G := GL(2, Integers(N));
    ret := [**];
    A_matrices := [[1,0,0,1],[0,-1,1,0],[1,1,-1,0]];
    A := G!A_matrices[size_A];
    a_list := [A^(i-1) : i in [1..size_A]];
    already_seen := [**];
    T, phi := Transversal(G, H); //phi sends g to its coset representative
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

declare type BasicBasepoint;
declare attributes BasicBasepoint: p, pp, v, tau;

intrinsic MakeBasicBasepoint(p::RngIntElt, tau::FldNumElt, pp::RngOrdIdl, v::PlcNumElt) -> BasicBasepoint
{Constructor}
    assert(IsPrime(p));
    ret := New(BasicBasepoint);
    ret`p := p;
    ret`tau := tau;
    ret`pp := pp;
    ret`v := v;
    return ret;
end intrinsic;

intrinsic Print(B::BasicBasepoint)
{Print BasicBasepoint}
    printf "p = %o, K = %o with Hilbert class field H_O = %o, tau = %o, pp = %o", B`p, Parent(B`tau), Parent(B`v), B`tau, B`pp; 
end intrinsic;

function find_embedding(x_approx, K)
    for v in InfinitePlaces(K) do 
        if Abs(x_approx - Evaluate(K.1, v)) lt 1e-20 then
            return v;
        end if;
    end for;
    error Error("The precision was not strong enough!");
end function;

function upper_half_conversion(z)
    return (Im(z) gt 0) select z else -z;
end function;

intrinsic GenerateBasicBasepoints(p::RngIntElt) -> SeqEnum
{Generates a list of basepoints whose j-invariants cover all residue classes mod p}
    assert(IsPrime(p) and p gt 3);
    R<x> := PolynomialRing(Integers());
    // H's and pp's are the ring class fields we encounter and the primes we choose above them, created so that we can check compatibility.
    ret := [* *];
    H_s := [* *];
    pp_s := [* *];
    found_j_invariants := {**};
    bd := -Floor(2*p^(1/2));
    for ap in [bd..0] do
        // First, get the j-invariant(s) associated to the order Z[phi], where tr(phi) = ap.
        printf "ap = %o\n", ap; 
        K<tau_Fr> := NumberField(x^2 + ap*x + p); O_K := MaximalOrder(K); 

        DD := ap*ap-4*p; D, bp := SquarefreeFactorization(DD); f0 := (D mod 4 eq 1) select bp else Integers()!(bp/2);

        for f in Reverse(Divisors(f0)) do 
            printf "K = %o, f = %o\n", K, f; 
            tau := (tau_Fr + (bp-ap)/2) * f/f0; // (f + f*sqrt(D))/2
            tau_ := Evaluate(tau, InfinitePlaces(K)[1]);
            O := sub<O_K | 1, tau>;
            P_O := PolynomialRing(K)!HilbertClassPolynomial(D*(Integers()!(f*bp/f0))^2);
            printf "The Hilbert class polynomial here is %o\n", P_O;
            H_O := NumberField(P_O : DoLinearExtension := true); j := H_O.1;
            O_HO := MaximalOrder(H_O);

            v := find_embedding(jInvariant(tau_), H_O);

            // Next, choose a suitable prime pp of H above p compatible with all the previous choices.
            if #H_s eq 0 then 
                pp := Factorization(p*O_HO)[1][1];
            else 
                F := Factorization(&+ [&meet blah(AbsoluteField(H_s[i]), AbsoluteField(H_O), pp_s[i], p) : i in [1..#H_s]]);
                printf "The possible primes to pick is %o\n", F;
                pp := F[1][1];
            end if;
            Append(~H_s, H_O);
            Append(~pp_s, pp);
            
            // Match up the tau's in the class group action with the j-invariants in the Galois action.
            j_conjugates_arithmetic := [r[1] : r in Roots(PolynomialRing(H_O)!P_O)];
            j_conjugates_arithmetic_sorted := [];
            Cl, m := PicardGroup(O);
            printf "order of the Picard group is %o\n", #Cl;
            ba := [Basis(m(g)) : g in Cl | not IsIdentity(g)];
            tau_conjugates := [H_O!(b[2]/b[1]): b in ba];
            Append(~tau_conjugates, H_O!tau);
            j_conjugates_from_tau :=  [jInvariant(upper_half_conversion(Evaluate(ta, v))) : ta in tau_conjugates];
            for z in j_conjugates_from_tau do 
                for w in j_conjugates_arithmetic do 
                    if Abs(z - Evaluate(w, v)) lt 1e-20 then 
                        Append(~j_conjugates_arithmetic_sorted, w);
                        break;
                    end if;
                end for;
            end for;

            // Finally, if you encounter a j-invariant residue class you did not see before, then add that in.
            _, h := ResidueClassField(pp);
            for i in [1..#j_conjugates_arithmetic_sorted] do 
                j_c := j_conjugates_arithmetic_sorted[i];
                j_cbar := h(O_HO!j_c);
                if j_cbar in found_j_invariants then
                    continue;
                end if;
                Append(~ret, MakeBasicBasepoint(p, tau_conjugates[i], pp, v));
                Include(~found_j_invariants, j_cbar);
            end for;
        end for;

        if #found_j_invariants eq p then return ret; end if;
    end for;
    error Error("You did not find all residue classes for some reason.");
end intrinsic;