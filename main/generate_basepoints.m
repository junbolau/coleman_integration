declare type BasicBasepoint[Basepoint];
declare attributes BasicBasepoint: p, pp, v, c_v, tau, j_modp, ap, bp, D, K, H_O, j, discrim;
declare attributes Basepoint: B, H, N, g, gamma, tau_new;
declare type CuspBasepoint;
declare attributes CuspBasepoint: H, N, g, gamma, r;
declare type PlcNumEltWithConj; 
declare attributes PlcNumEltWithConj: v, c_v;

intrinsic NewPlaceWithConj(v::PlcNumElt, c_v::BoolElt) -> PlcNumEltWithConj
{Constructor}
    ret := New(PlcNumEltWithConj);
    ret`v := v;
    ret`c_v := c_v;
    return ret;
end intrinsic;

intrinsic Evaluate(alph::FldNumElt, vv::PlcNumEltWithConj) -> FldComElt
{Evaluates alph at the place v.}
    // require Parent(alph) eq Parent(vv`v) : "Not a valid place of the number field specified";
    return (vv`c_v select ComplexConjugate(Evaluate(alph,vv`v)) else Evaluate(alph,vv`v));
end intrinsic;

intrinsic InfinitePlacesWithConj(K::FldNum) -> SeqEnum 
{Given a number field, returns the infinite places with conjugation}
    x := InfinitePlaces(K);
    return &cat [IsReal(v) select [NewPlaceWithConj(v,true)] else [NewPlaceWithConj(v,true),NewPlaceWithConj(v,false)] : v in x];
end intrinsic;

intrinsic MakeBasicBasepoint(j::FldNumElt, tau::FldNumElt, pp::RngOrdIdl, v::PlcNumEltWithConj, ap::RngIntElt, discrim::RngIntElt) -> BasicBasepoint
{Constructor}
    ret := New(BasicBasepoint);
    ret`p := Min(pp);
    ret`H_O := Parent(tau);
    ret`K := BaseField(ret`H_O);
    ret`tau := (ret`K)!tau;
    ret`pp := pp;
    ret`v := v;
    ret`j := j;
    _, h := ResidueClassField(ret`pp); ret`j_modp := h(MaximalOrder(ret`H_O)!j);
    ret`ap := ap;
    ret`discrim := discrim;
    DD := ap*ap-4*ret`p; ret`D, ret`bp := SquarefreeFactorization(DD);
    return ret;
end intrinsic;

intrinsic FrobeniusMatrix(N::RngIntElt, B::BasicBasepoint) -> GrpMat
{Returns the Frobenius matrix of the base point}
    G := GL(2, Integers(N));
    //r,s := Explode(Flat(B`tau));
    r,s := Explode(Eltseq(B`tau));
    ap := B`ap; p := B`p;
    tau_Fr := B`K.1; tau_Fr := B`H_O!tau_Fr;
    if (ap eq 0) or (tau_Fr in B`pp) then 
        return G![ap + r/s, 1/s, -(r^2+r*s*ap+s^2*p)/s, -r/s];
    else 
        return G![-r/s, -1/s, (r^2+r*s*ap+s^2*p)/s, ap + r/s];
    end if;
end intrinsic;

intrinsic FindLevelStructures(N::RngIntElt, H::GrpMat, B::BasicBasepoint) -> SeqEnum
{Finds the possible level structures on B defined over F_p
 NOTE: This code assumes that [0,-1,1,0], and [1,1,-1,0] are the automorphism matrices 
 when a priori they might be only be conjugate to that matrix. 
 This is fine because in GenerateBasicBasepoints we have hardcoded in the basepoints for j-invariants 0 and 1728. 
 The downside is that you do not get anything about the Frobenius matrix if p is inert in one of those number fields.
}
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

// Finds a determinant d matrix in H by randomly choosing elements.
function find_det_d_matrix(d, H, N)
    assert(GCD(d,N) eq 1);
    if d eq 1 then return H![1,0,0,1]; end if;
    while true do 
        x := Random(H);
        if Determinant(x) eq d then 
            return x;
        end if;
    end while;
end function;

// Finds a determinant 1 matrix whose reduction is M.
function lift_matrix_to_sl2z(M, N)
    a := Integers()!(M[1][1]); b := Integers()!(M[1][2]); c := Integers()!(M[2][1]); d := Integers()!(M[2][2]);
    if a*d-b*c eq 1 then return SL(2,Integers())![a,b,c,d]; end if;
    if b eq 0 then b := b+N; end if;
    while not (GCD(a,b) eq 1) do 
        a := a+N;
    end while;
    k := (a*d-b*c-1)/N; 
    x,_ := Solution(a,Integers()!(-k),b);
    y := (a*x+k)/b;
    return SL(2,Integers())![a,b,c+y*N,d+x*N];
end function;

intrinsic FindCuspLevelStructures(N::RngIntElt, H::GrpMat, p::RngIntElt) -> SeqEnum
{Finds all cusp level structures defined over F_p}
    G := GL(2, Integers(N));
    A := G![1,1,0,1];
    Fr := G![p,0,0,1];
    a_list := [A^(i-1) : i in [1..N]];
    already_seen := {**};
    ret := [**];
    T, phi := Transversal(G, H);
    for g in T do
        if &or[phi(g*a) in already_seen : a in a_list] then 
            continue;
        end if;
        if &or[g*Fr*a*g^(-1) in H : a in a_list] then 
            Append(~ret, MakeCuspBasepoint(N,H,g));
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
    // Now we need to create tau_new...
    M := lift_matrix_to_sl2z(find_det_d_matrix(Determinant(g)^(-1), H, N)*g, N);
    a := M[1][1]; b := M[1][2]; c := M[2][1]; d := M[2][2];
    ret`gamma := M;
    tau := B`tau;
    ret`tau_new := (a*tau+b)/(c*tau+d);
    return ret;
end intrinsic;

intrinsic MakeCuspBasepoint(N::RngIntElt, H::GrpMat, g::GrpMatElt) -> CuspBasepoint 
{Constructor for CuspBasepoint}
    ret := New(CuspBasepoint);
    ret`H := H;
    ret`N := N;
    ret`g := g;
    // Now we need to create r...
    M := lift_matrix_to_sl2z(find_det_d_matrix(Determinant(g)^(-1), H, N)*g, N);
    a := M[1][1]; c := M[2][1];
    ret`gamma := M;
    ret`r := (c eq 0) select Infinity() else a/c;
    return ret;
end intrinsic;

intrinsic Parent(BB::Basepoint) -> BasicBasepoint
{Parent of BB}
    return BB`B;
end intrinsic;

intrinsic Print(BB::Basepoint)
{Print Basepoint}
    printf "BASEPOINT:\n%oLevel structure given by matrix\n%o\n", Parent(BB), BB`g;
end intrinsic;

intrinsic Print(BB::CuspBasepoint)
{Print CuspBasepoint}
    printf "CUSP BASEPOINT:\nMatrix given by \n%o\nwith tau = %o\n", BB`g, BB`r;
end intrinsic;

intrinsic GetRamification(BB::CuspBasepoint) -> RngIntElt
{Get ramification of the cusp}
    return GetWidth(BB`H, BB`N, BB`g);
end intrinsic;

intrinsic GetWidth(H::GrpMat, N::RngIntElt, g::GrpMatElt) -> RngIntElt 
{Gets the width of the cusp g*i\infty}
    gconj := g*GL(2,Integers(N))![1,1,0,1]*g^(-1);
    a := gconj;
    ret := 1;
    while not a in H do 
        a := a*gconj;
        ret := ret + 1;
    end while;
    return ret;
end intrinsic;

intrinsic GetWidth(H::GrpMat, N::RngIntElt) -> RngIntElt 
{Gets the width of the infinite cusp}
    return GetWidth(H,N,GL(2,Integers(N))![1,0,0,1]);
end intrinsic;

intrinsic GetRamification(BB::Basepoint) -> RngIntElt
{Get ramification of the point}
    B := Parent(BB);
    N := BB`N;
    if (B`j eq 0) and not (BB`g * GL(2,Integers(N))![1,1,-1,0] * BB`g^(-1) in BB`H) then return 3; end if;
    if (B`j eq 1728) and not (BB`g * GL(2,Integers(N))![0,-1,1,0] * BB`g^(-1) in BB`H) then return 2; end if;
    return 1;
end intrinsic;

function upper_half_conversion(z)
    return (Im(z) gt 0) select z else -z;
end function;

// Given an extension L/K, and infinite places v_L and v_K (with c_L and c_K being either the identity or complex conjugation), return an embedding K->L such that v_L extends v_K.
function embed_based_on_places(L, K, vv_L, vv_K) 
    aK := K.1;
    _, f := IsSubfield(K, L);
    aK_conjugates := [x[1] : x in Roots(PolynomialRing(K)!DefiningPolynomial(K))];
    for c in aK_conjugates do
        aa := Evaluate(f(c), vv_L);
        bb := Evaluate(aK, vv_K);
        if Abs(aa - bb) lt 1e-20 then 
            return hom<K -> K | c> * f; 
        end if;  
    end for;
    error Error("You did not find an embedding for some reason.");
end function;

// Given an embedding of fields f: K -> L, and a prime ppL of L, return the prime of K below ppL.
function restrict(OK, OL, ppL, f)
    p := Min(ppL);
    for x in Factorization(p*MaximalOrder(OK)) do 
        qK := x[1];
        a,b := TwoElement(qK);
        qKinL := ideal<MaximalOrder(OL)|f(a),f(b)>;
        if qKinL subset ppL then 
            return qK;
        end if;
    end for;
    error Error("You did not find a prime below for some reason.");
end function;

// Given a complex number x_approx that is the embedding of the generator of K, find the specified embedding.
function find_embedding(x_approx, K)
    for vv in InfinitePlacesWithConj(K) do 
        if Abs(x_approx - Evaluate(K.1, vv)) lt 1e-20 then
            return vv;
        end if;
    end for;
    error Error("The precision was not strong enough!");
end function;

// Given an embedding of fields f:K->L and an infinite place of K, find an infinite place of L that extends that on K. Using this because Decomposition() is broken...
function extend_infinite_place(K,L,f,vv_K)
    aa := Evaluate(K.1,vv_K);
    for vL in InfinitePlacesWithConj(L) do 
        if Abs(Evaluate(f(K.1), vL) - aa) lt 1e-20 then 
            return vL;
        end if;
    end for;
    error Error("You did not find an infinite place extension for some reason!");
end function;

intrinsic GenerateBasicBasepoints(p::RngIntElt) -> SeqEnum
{Generates a list of non-cuspidal basepoints whose j-invariants cover all residue classes mod p}
    assert(IsPrime(p) and p gt 3);
    R<x> := PolynomialRing(Integers());
    // FF keeps track of the compositum of all fields we encountered. 
    // ppFF and vvFF are infinite places of FF; we will use these to determine the suitable primes to pick for each field we see.
    ret := [* *];
    FF := Rationals();
    ppFF := p;
    found_j_invariants := {*0,(1728 mod p)*};

    // Before we get into the main loop, we must first deal with j = 0,1728.
    require ((p mod 12) eq 1) : "You need a prime that splits in both of the number fields associated to j = 0 and 1728 (i.e. p is 1 mod 12), otherwise we cannot compute the Frobenius efficiently!";
    Kj1728 := NumberField(x^2+1); Kj0 := NumberField(x^2+x+1); // number fields and their compositum
    FF := Compositum(Kj1728, Kj0);
    Oj1728 := MaximalOrder(Kj1728); Oj0 := MaximalOrder(Kj0); // maximal orders
    O_FF := MaximalOrder(FF);
    v1728 := NewPlaceWithConj(InfinitePlaces(Kj1728)[1], false); v0 := NewPlaceWithConj(InfinitePlaces(Kj0)[1], false); vvFF := NewPlaceWithConj(InfinitePlaces(FF)[1], false); // infinite places for each field
    f1728 := embed_based_on_places(FF, Kj1728, vvFF, v1728); f0 := embed_based_on_places(FF, Kj0, vvFF, v0); // embeddings into the compositum that preserve the places
    ppFF := Ideal(Decomposition(FF, p)[1][1]); 
    pp1728 := restrict(Oj1728, O_FF, ppFF, f1728); pp0 := restrict(Oj0, O_FF, ppFF, f0); // primes below the chosen prime of the compositum
    for dat in [*[*v1728, pp1728, Kj1728, 1728, -4*], [*v0, pp0, Kj0, 0, -3*]*] do 
        _, gen := IsPrincipal(dat[2]);
        f := MinimalPolynomial(gen);
        a := -Coefficient(f, 1);
        K<tau_Fr> := NumberField(f);
        r,s := Explode(Eltseq(gen)); if s lt 0 then s := -s; end if;
        isom := hom<K->dat[3] | r+s*dat[3].1>; isom := isom^(-1);
        P<t> := PolynomialRing(K);
        H_O := NumberField(P!(t-dat[4]) : DoLinearExtension := true);
        Append(~ret, MakeBasicBasepoint(H_O!dat[4], H_O!(isom(dat[3].1)), ideal<MaximalOrder(K)|K.1>, dat[1], a, dat[5]));
    end for;

    // Below this line, we have j \neq 0,1728. First, loop through possible traces of Frobenius.
    bd := Floor(2*p^(1/2));
    for ap in Reverse([0..bd]) do // This reverse is not just for style! It actually helps optimize the code - namely, it gives us a higher chance that the computation of new_FF will be quicker since H_O will then be more likely to contain something we haven't seen before.
        printf "ap = %o\n", ap; 
        K<tau_Fr> := NumberField(x^2 - ap*x + p); O_K := MaximalOrder(K); // tau_Fr = (a + sqrt(a^2-4p))/2 = (a + bsqrt(D))/2
        DD := ap*ap-4*p; D, bp := SquarefreeFactorization(DD); f0 := (D mod 4 eq 1) select bp else Integers()!(bp/2);
        // K<alpha> := NumberField(x^2-D);
        O_K := MaximalOrder(K);
        P<t> := PolynomialRing(K);

        // Now, loop through orders containing the lift of Frobenius.
        conductors := Reverse(Divisors(f0));
        for index in [1..#conductors] do 
            f := conductors[index];
            printf "K = %o, f = %o\n", K, f; 
            tau := (tau_Fr + (bp-ap)/2) * f/f0; // (f + f*sqrt(D))/2
            // tau := (D mod 4 eq 1) select f*(1+alpha)/2 else f*alpha; 
            tau_ := Evaluate(tau, InfinitePlaces(K)[1]);
            O := sub<O_K | 1, tau>;
            discrim := D*(Integers()!(f*bp/f0))^2;
            //P_O := PolynomialRing(K)!HilbertClassPolynomial(D*(Integers()!(f*bp/f0))^2);
            P_O := P!HilbertClassPolynomial(discrim);
            printf "The Hilbert class polynomial here is %o\n", P_O;
            H_O<j> := NumberField(P_O : DoLinearExtension := true); 
            O_HO := MaximalOrder(H_O);

            // Bookkeeping: update compatible primes.
            if index eq 1 then // If index isn't 1, then we're getting an order of smaller conductor, so that ring class field will be strictly contained in one that we already computed.
                new_FF, _ := OptimizedRepresentation(Compositum(FF, ((Degree(P_O) eq 1) select K else OptimizedRepresentation(AbsoluteField(H_O)))));
                print(new_FF);
                _, currEmbedFFs := IsSubfield(FF, new_FF); // new compositum and the embedding into that
                vvFF := extend_infinite_place(FF, new_FF, currEmbedFFs, vvFF);
                O_FF := MaximalOrder(new_FF);
                ppFF := Ideal(Decomposition(currEmbedFFs, Place(ppFF))[1][1]);
            end if;
            vH := find_embedding(jInvariant(tau_), H_O); // find embedding of H_O that sends the generator to the complex j-invariant
            fHFF := embed_based_on_places(new_FF, H_O, vvFF, vH); // choose a infinite place of new compositum and embed H_O in there based on that
            ppH := restrict(O_HO, O_FF, ppFF, fHFF); // find the prime of H_O above p and below the prime of the new compositum
            FF := new_FF;
            
            // Match up the tau's in the class group action with the j-invariants in the Galois action.
            j_conjugates_arithmetic := [r[1] : r in Roots(PolynomialRing(H_O)!P_O)];
            j_conjugates_arithmetic_sorted := [];
            Cl, m := PicardGroup(O);
            printf "order of the Picard group is %o\n", #Cl;
            ba := [Basis(m(g)) : g in Cl | not IsIdentity(g)];
            tau_conjugates := [H_O!(b[2]/b[1]): b in ba];
            Append(~tau_conjugates, H_O!tau);
            j_conjugates_from_tau := [jInvariant(upper_half_conversion(Evaluate(ta, vH))) : ta in tau_conjugates];
            for z in j_conjugates_from_tau do 
                for w in j_conjugates_arithmetic do 
                    di := Abs(z - Evaluate(w, vH));
                    if di lt 1e-20 then 
                        // printf "Found a match. The difference is %o\n", di; 
                        Append(~j_conjugates_arithmetic_sorted, w);
                        break;
                    end if;
                end for;
            end for;

            // Finally, if you encounter a j-invariant residue class you did not see before, then add that in.
            _, h := ResidueClassField(ppH);
            for i in [1..#j_conjugates_arithmetic_sorted] do 
                j_c := j_conjugates_arithmetic_sorted[i];
                j_cbar := h(O_HO!j_c);  // the image of j_c mod pp inside F_p 
                if j_cbar in found_j_invariants then
                    continue;
                end if;
                Append(~ret, MakeBasicBasepoint(j_c, tau_conjugates[i], ppH, vH, ap, discrim));
                Include(~found_j_invariants, j_cbar);
            end for;
        end for;
        if #found_j_invariants eq p then return ret; end if;
    end for;
    error Error("You did not find all residue classes for some reason.");
end intrinsic;

intrinsic GenerateAllBasepoints(p::RngIntElt, H::GrpMat, N::RngIntElt) -> SeqEnum
{Generates all possible noncuspidal basepoints, WITH the level structure.}
    x := GenerateBasicBasepoints(p);
    return &cat[FindLevelStructures(N,H,B) : B in x];
end intrinsic;