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

intrinsic CompatiblePrimes(K::FldNum, L::FldNum, pp::RngOrdIdl, p::RngIntElt) -> SeqEnum
{
    Given a number field K, a prime pp of K above p, and a number field L, 
    return a list of primes ppp of L above p "compatible" with pp. 
    The fields K and L are assumed to be Galois over Q.
}
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
end intrinsic;

declare type BasicBasepoint[Basepoint];
declare attributes BasicBasepoint: p, pp, v, tau, j_modp, ap, bp, D, K, H_O;
declare attributes Basepoint: H, N, g, B;
declare attributes CuspBasepoint: H, g, r;



intrinsic MakeBasicBasepoint(p::RngIntElt, tau::FldNumElt, pp::RngOrdIdl, v::PlcNumElt, j_modp::FldFinElt, ap::RngIntElt) -> BasicBasepoint
{Constructor}
    assert(IsPrime(p));
    ret := New(BasicBasepoint);
    ret`p := p;
    ret`H_O := Parent(tau);
    ret`K := BaseField(ret`H_O);
    ret`tau := (ret`K)!tau;
    ret`pp := pp;
    ret`v := v;
    ret`j_modp := j_modp;
    ret`ap := ap;
    DD := ap*ap-4*p; ret`D, ret`bp := SquarefreeFactorization(DD);
    return ret;
end intrinsic;

intrinsic FrobeniusMatrix(N::RngIntElt, B::BasicBasepoint) -> GrpMat
{Returns the Frobenius matrix of the base point}
    G := GL(2, Integers(N));
    r,s := Explode(Flat(B`tau));
    ap := B`ap; p := B`p;
    if (ap eq 0) or (B`tau in B`pp) then 
        return G![ap + r/s, 1/s, -(r^2+r*s*ap+s^2*p)/s, -r/s];
    else 
        return G![-r/s, -1/s, (r^2+r*s*ap+s^2*p)/s, ap + r/s];
    end if;
end intrinsic;

intrinsic InverseJFunction(j:FldComElt) -> FldComElt
{Returns a \tau such that j(\tau) = j. The source is https://math.stackexchange.com/questions/438436/inverting-the-modular-j-function}
    C<i> := ComplexField();
    alpha := (1 + SquareRoot(1-1728/j))/2;
    return i*HypergeometricSeries(1/6,5/6,1,1-alpha)/HypergeometricSeries(1/6,5/6,1,alpha);
end intrinsic;

intrinsic Q(tau:FldComElt) -> FldComElt 
{Returns Q(tau) = e^(2 pi i tau).}
    C<i> := ComplexField();
    return Exp(2*Pi(C)*i*tau);
end intrinsic;

/* NOTE: THIS CODE DOES NOT WORK. It assumes that e.g. [0,-1,1,0] is the automorphism matrix, when the actual matrix could be a conjugate of that! */
intrinsic FindLevelStructures(N::RngIntElt, H::GrpMat, B::BasicBasepoint) -> SeqEnum
{Finds the possible level structures on B defined over F_p}
    size_A := (1728 mod B`p eq B`j_modp) select 2 else ((0 mod B`p eq B`j_modp) select 3 else 1);
    G := GL(2, Integers(N));
    Fr := FrobeniusMatrix(N,B);
    ret := [**];
    A_matrices := [[1,0,0,1],[0,-1,1,0],[1,1,-1,0]];
    A := G!A_matrices[size_A];
    a_list := [A^(i-1) : i in [1..size_A]];
    already_seen := {**};
    T, phi := Transversal(G, H); //phi sends g to its a coset representative of Hg
    for g in T do
        if &or[phi(g*a) in already_seen : a in a_list] then 
            continue;
        end if;
        if &or[g*Fr*a*g^(-1) in H : a in a_list] then 
            Append(~ret, MakeBasepoint(N,H,g,B));
        end if;
        Include(~already_seen, g);
    end for;
    return ret;
end intrinsic;

intrinsic Print(B::BasicBasepoint)
{Print BasicBasepoint}
    printf "(a,b,D) = (%o,%o,%o),\nHilbert class field is %o,\nPrime above %o is %o,\ntau is %o,\nj-invariant residue class is %o mod %o\n", B`ap, B`bp, B`D, B`H_O, B`p, B`pp, B`tau, B`j_modp, B`p;
end intrinsic;

intrinsic MakeBasepoint(N::RngIntElt, H::GrpMat, g::GrpMatElt, B::BasicBasepoint) -> Basepoint
{Constructor for Basepoint}
    ret := New(Basepoint);
    ret`B := B;
    ret`N := N;
    ret`g := g;
    ret`H := H;
    return ret;
end intrinsic;

intrinsic MakeCuspBasepoint(H::GrpMat, g::GrpMatElt, r::FldRatElt) -> CuspBasepoint 
{Constructor for CuspBasepoint}
    ret := New(CuspBasepoint);
    ret`r := r;
    ret`H := H;
    ret`g := g;
    return ret;
end intrinsic;

intrinsic Parent(BB::Basepoint) -> BasicBasepoint
{Parent of BB}
    return BB`B;
end intrinsic;

intrinsic Print(BB:Basepoint)
{Print Basepoint}
    printf "BASEPOINT:\n%oLevel structure given by matrix\n%o\n", Parent(BB), BB`g;
end intrinsic;

intrinsic TaylorExpansion(f::RngSerLaurElt, q0::FldComElt : prec := 100) -> RngSerLaurElt
{Computes the Taylor expansion of f(q) at q0.}
    R<qmq0> := LaurentSeriesRing(ComplexField(): Global := false);
    return &+ [Evaluate(Derivative(f, i), q0)/Factorial(i) * qmq0^i : i in [0..prec]] + O(qmq0^(prec + 1));
end intrinsic;

intrinsic GetUniformizer(BB:Basepoint) -> RngSerLaurElt, Map
{Returns a local uniformizer around the residue disk of the basepoint as a power series in q, NOT necessarily at the basepoint itself. The uniformizer is:
    (1) j(q) - (j mod p) if not in the below cases
    (2) j(q)^(1/3) if j \equiv 0 and g[1,1,-1,0]g^(-1) does not lie in \Gamma_H.
    (3) (j(q)-1728)^(1/2) if j \equiv 1728 and g[0,-1,1,0]g^(-1) does not lie in \Gamma_H.
    (4) (q-r)^(1/h) if cuspidal, where h is the smallest positive integer such that g[1,h,0,1]g^(-1) lies in \Gamma_H.
}
    B := Parent(BB);
    j := B`j_modp; g := BB`g; H := BB`H;
    R<q> := LaurentSeriesRing(Rationals(): Global:=false);
    R2<q2> := LaurentSeriesRing(Rationals(): Global:=false);
    R3<q3> := LaurentSeriesRing(Rationals(): Global:=false);
    f2 := hom<R->R2|q2^2>;
    f3 := hom<R->R3|q3^3>;
    if (j eq 0) and (not g*GL(2,Integers(N))![1,1,-1,0]*g^(-1) in H) then 
        return CubeRoot(f3(jInvariant(q)));
    elif (j eq (1728 mod p)) and (not g*GL(2,Integers(N))![0,1,-1,0]*g^(-1) in H) then
        return SquareRoot(f(jInvariant(q))-1728);
    else 
        return jInvariant(q) - j;
    end if;
end intrinsic;

/*TODO: Figure out what happens when r = \infty.*/
intrinsic GetUniformizer(BB:CuspBasepoint) -> RngSerLaurElt, Map
{See above}
    x := g*(GL(2,Integers(N))![1,1,0,1])*g^(-1);
    y := x;
    h := 1;
    while not (y in BB`H) do 
        h := h+1;
        y := y*x;
    end while;
    C<i> := ComplexField();
    R<q> := LaurentSeriesRing(C: Global:=false);
    return (q-Exp(2*Pi(C)*i*BB`r))^(1/h);
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
    bd := Floor(2*p^(1/2));
    for ap in [0..bd] do
        // First, get the j-invariant(s) associated to the order Z[phi], where tr(phi) = ap.
        printf "ap = %o\n", ap; 
        K<tau_Fr> := NumberField(x^2 - ap*x + p); O_K := MaximalOrder(K); // tau_Fr = (a + sqrt(a^2-4p))/2 = (a + bsqrt(D))/2

        DD := ap*ap-4*p; D, bp := SquarefreeFactorization(DD); f0 := (D mod 4 eq 1) select bp else Integers()!(bp/2);

        for f in Reverse(Divisors(f0)) do 
            printf "K = %o, f = %o\n", K, f; 
            tau := (tau_Fr + (bp-ap)/2) * f/f0; // (f + f*sqrt(D))/2
            tau_ := Evaluate(tau, InfinitePlaces(K)[1]);
            O := sub<O_K | 1, tau>;
            P_O := PolynomialRing(K)!HilbertClassPolynomial(D*(Integers()!(f*bp/f0))^2);
            printf "The Hilbert class polynomial here is %o\n", P_O;
            H_O<j> := NumberField(P_O : DoLinearExtension := true); 
            O_HO := MaximalOrder(H_O);

            v := find_embedding(jInvariant(tau_), H_O);

            // Next, choose a suitable prime pp of H above p compatible with all the previous choices.
            if #H_s eq 0 then 
                pp := Factorization(p*O_HO)[1][1];
            else 
                F := Factorization(&+ [&meet CompatiblePrimes(AbsoluteField(H_s[i]), AbsoluteField(H_O), pp_s[i], p) : i in [1..#H_s]]);
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
                    di := Abs(z - Evaluate(w, v));
                    if di lt 1e-20 then 
                        // printf "Found a match. The difference is %o\n", di; 
                        Append(~j_conjugates_arithmetic_sorted, w);
                        break;
                    end if;
                end for;
            end for;

            // Finally, if you encounter a j-invariant residue class you did not see before, then add that in.
            _, h := ResidueClassField(pp);
            for i in [1..#j_conjugates_arithmetic_sorted] do 
                j_c := j_conjugates_arithmetic_sorted[i];
                j_cbar := h(O_HO!j_c);  // the image of j_c mod pp inside F_p 
                if j_cbar in found_j_invariants then
                    continue;
                end if;
                Append(~ret, MakeBasicBasepoint(p, tau_conjugates[i], pp, v, j_cbar, ap));
                Include(~found_j_invariants, j_cbar);
            end for;
        end for;

        if #found_j_invariants eq p then return ret; end if;
    end for;
    error Error("You did not find all residue classes for some reason.");
end intrinsic;

intrinsic GenerateAllBasepoints(p::RngIntElt, H::GrpMat, N::RngIntElt) -> SeqEnum
{Generates all possible basepoints, WITH the level structure.}
    x := GenerateBasicBasepoints(p);
    return &cat[FindLevelStructures(N,H,B) : B in x];
end intrinsic;