// Code based in part on Sutherland's code in gl2.m https://github.com/AndrewVSutherland/ell-adic-galois-images/blob/main/groups/gl2.m

// Some utility functions 

// Use Cornacchia's algorithm to solve x^2 + dy^2 = m for (x,y) with x,y > 0
function norm_equation(d,m)
    if not IsSquare(m) then
        c,a,b := NormEquation(d,m);
        if not c then return false,_,_; else return c,a,b;  end if;
    end if;
    t,r1 := IsSquare(Integers(m)!-d);
    if not t then return false,_,_; end if;
    r1 := Integers()!r1;
    if 2*r1 gt m then r1 := m-r1; end if;
    r0 := m;
    while r1^2 ge m do s := r0 mod r1; r0:= r1;  r1:= s; end while;
    t,s := IsSquare((m-r1^2) div d);
    if not t then return false,_,_; end if;
    return t,r1,s;
end function;

function IsHCPRoot(D,j)  // returns true if j is a root of H_D(x), attempts to use Weber polys when possible
    if D mod 8 eq 5 then return Evaluate(HilbertClassPolynomial(D),j) eq 0; end if;
    F := Parent(j);
    H,f := WeberClassPolynomial(D);
    return Degree(GCD(ChangeRing(Denominator(f),F)*j - ChangeRing(Numerator(f),F), ChangeRing(H,F))) gt 0;
end function;

function OnFloor(E,ell)
    if ell eq 2 then return #TwoTorsionSubgroup(E) lt 4; end if;
    return NumberOfRoots(Evaluate(AtkinModularPolynomial(ell),[PolynomialRing(BaseRing(E)).1,jInvariant(E)])) le ell;
end function;

function HeightAboveFloor(E,t,v,D0,ell,h)
    // assumes j(E) != 0,1728 and E is ordinary
    if h eq 0 then return 0; end if;
    s := OnFloor(E,ell) select 0 else 1;
    if h le 1 or s eq 0 then return s; end if;
    j := jInvariant(E);
    R<x> := PolynomialRing(Parent(j));
    R2<X,Y> := PolynomialRing(Parent(j),2);
    phi := Evaluate(ClassicalModularPolynomial(ell),[X,Y]);
    j1 := Roots(Evaluate(phi,[j,x]));
    if #j1 ne ell+1 then return h; end if; // double roots can only happen at the surface
    if #j1 lt 3 then return 0; end if;
    j0 := [j,j,j]; j1 := [j1[i][1]:i in [1..3]];
    h := 1;
    while true do
        for i:=1 to 3 do
            r := Roots(ExactQuotient(Evaluate(phi,[j1[i],x]),x-j0[i]));
            if #r eq 0 then return h; end if;
            j0[i] := j1[i];  j1[i] := r[1][1];
        end for;
        h +:= 1;
    end while;
end function;

// returns j0, d where j0 is j-invariant on surface above j and d is the distance from j to j0
function ClimbToSurface(j,ell,h)
    if h eq 0 then return j, 0; end if;
    if j eq 0 or j eq 1728 then return j,0; end if;
    R<x> := PolynomialRing(Parent(j));
    R2<X,Y> := PolynomialRing(Parent(j),2);
    phi := Evaluate(ClassicalModularPolynomial(ell),[X,Y]);
    jj := Roots(Evaluate(phi,[j,x]));
    if &or[r[2] gt 1 : r in jj] or j in {r[1]:r in jj} then return j, 0; end if; // double roots can only happen at the surface
    if h eq 1 then if #jj eq 1 then return jj[1][1], 1; else return j, 0; end if; end if;
    jj := [r[1] : r in jj]; j0 := [j : r in jj]; j1 := jj;
    e := 0; i := 1;
    while #j1 gt 1 do
        e +:= 1;
        j2 := [[r[1] : r in Roots(ExactQuotient(Evaluate(phi,[j1[i],x]),x-j0[i]))] : i in [1..ell+1]];
        if [] in j2 then
            ii := [n : n in [1..#j2] | j2[n] ne []];
            if #ii eq 0 then return j, 0; end if; // if we hit the floor simultaneously on every path we must have started on the surface
            i := ii[1]; break;
        end if;
        j0 := j1; j1 := [r[1] : r in j2];
    end while;
    if e eq h then return j, 0; end if;
    xj := j; j := jj[i]; d := 1; e +:= 1; // e is height of j above floor
    function walk(phi,nj,xj,n)
        for i:=1 to n do r := Roots(ExactQuotient(Evaluate(phi,[nj,x]),x-xj)); if #r eq 0 then return false; end if; xj:=nj; nj:=r[1][1]; end for;
        return true;
    end function;
    while e lt h do
        assert j ne 0 and j ne 1728;
        nj := [r[1]:r in Roots(ExactQuotient(Evaluate(phi,[j,x]),x-xj))];  assert #nj eq ell;
        i := 1; while i le ell and not walk(phi,nj[i],j,e+1) do i +:= 1; end while;
        xj := j; j := nj[i]; d +:= 1; e +:= 1;
    end while;
    return j,d;
end function;

// Apply Theorem 2.1 of Duke and Toth, given a,b,D satisfying that 4q=a^2-b^2D, where a is the trace of the Frobenius endomorphism pi,
// D is the discriminant of Rpi := End(E) cap Q[pi], and b is the index of Z[pi] in Rpi unless Z[pi]=Z in which case D=1 and b=0
// see https://arxiv.org/abs/math/0103151
// returns a list of integers representing an element of GL_2(Z) with trace a and determinant q representing action of Frob (up to conj)
intrinsic FrobMat(a::RngIntElt, b::RngIntElt, D::RngIntElt) -> AlgMatElt[RngInt]
{   Apply Theorem 2.1 of Duke and Toth, given a,b,D satisfying that 4q=a^2-b^2D, where a is the trace of the Frobenius endomorphism pi,
    D is the discriminant of Rpi := End(E) cap Q[pi], and b is the index of Z[pi] in Rpi unless Z[pi]=Z in which case D=1 and b=0
    See https://arxiv.org/abs/math/0103151
    returns a list of integers representing an element of GL_2(Z) with trace a and determinant q representing action of Frob (up to conj)
}
    // assert (b gt 0 and D lt 0 and IsDiscriminant(D)) or (b eq 0 an dD eq 1);
    return Matrix([[(a+b*d) div 2, b], [b*(D-d) div 4, (a-b*d) div 2]]) where d := D mod 2;
end intrinsic;

intrinsic j0FM(q::RngIntElt) -> SeqEnum
{   returns a list of quadruples <a,b,D,w> where a,b,D define a FrobeniusMatrix (with a >= 0), and w is a rational weight }
    _,p,e := IsPrimePower(q);
    if p eq 2 then return j1728FM(q); end if;
    if p mod 3 eq 2 then
        if IsOdd(e) then
            return [<0,p^((e-1) div 2),-4*p,1>];
        else
            return [<p^(e div 2),p^(e div 2),-3,2/3>,<2*p^(e div 2),0,1,1/3>];
        end if;
    elif p eq 3 then
        if IsOdd(e) then
            return [<0,3^((e-1) div 2),-12,1/2>, <0,2*3^((e-1) div 2),-3,1/6>, <3^((e+1) div 2),3^((e-1) div 2),-3,1/3>];
        else
            return [<0,3^(e div 2),-4,1/2>, <3^(e div 2),3^(e div 2),-3,1/3>, <2*3^(e div 2),0,1,1/6>];
        end if;
    end if;
    c,a,b := norm_equation(3,4*q);  assert c and a gt 0 and b gt 0;
    if IsOdd(a) then
        if IsEven((a+3*b) div 2) then u := Abs(a+3*b) div 2; v := Abs(a-b) div 2; else u := Abs(a-3*b) div 2; v := Abs(a+b) div 2; end if;
    else
        u := Abs(a);v := Abs(b);
    end if;
    assert u gt 0 and v gt 0 and IsEven(u) and IsEven(v) and 4*q eq u^2+3*v^2;;
    return [<u,v,-3,1/3>, <(u+3*v) div 2,Abs((u-v) div 2),-3,1/3>, <Abs((u-3*v) div 2),(u+v) div 2,-3,1/3>];
end intrinsic;

intrinsic j0FrobeniusMatrices(q::RngIntElt) -> SetEnum[AlgMatElt[RngInt]] 
{   The set of Frobenius matrices of all elliptic curves with j-invariant 0 over a finite field }
    return Set([FrobMat(r[1],r[2],r[3]):r in j0FM(q)] cat [FrobMat(-r[1],r[2],r[3]):r in j0FM(q)|r[1] ne 0]); 
end intrinsic;

intrinsic j1728FM(q::RngIntElt) -> SeqEnum
{   returns a list of quadruples <a,b,D,w> where a,b,D define a FrobeniusMatrix (with a >= 0), and w is a rational weight}
    _,p,e := IsPrimePower(q);
    if p eq 3 then return j0FM(q); end if;
    if p mod 4 eq 3 then
        if e mod 2 eq 1 then
            return [<0,p^((e-1) div 2),-4*p,1/2>,<0,2*p^((e-1) div 2),-p,1/2>];
        else
            return [<0,p^(e div 2),-4,1/2>,<2*p^(e div 2),0,1,1/2>];
        end if;
    elif p eq 2 then
        if IsOdd(e) then
            return [<0,2^((e-1) div 2),-8,1/2>,<2^((e+1) div 2),2^((e-1) div 2),-4,1/2>];
        else
            return [<0,2^(e div 2),-4,1/4>,<2^(e div 2),2^(e div 2),-3,2/3>,<2*2^(e div 2),0,1,1/12>];
        end if;
    end if;
    c,a,b := norm_equation(4,4*q);  assert c and a gt 0 and b gt 0;
    if IsOdd(b) then u := Abs(2*b); v := Abs(a div 2); else u := Abs(a); v := Abs(b); end if;
    assert u gt 0 and v gt 0 and IsEven(u) and IsEven(v) and 4*q eq u^2+4*v^2;
    return [<a,b,b eq 0 select 1 else -4,1/2>,<2*b,a div 2,-4,1/2>];
end intrinsic;

intrinsic j1728FrobeniusMatrices(q) -> SetEnum[AlgMatElt[RngInt]]
{ The set of Frobenius matrices of all elliptic curves with j-invariant 0 over a finite field }
    return Set([FrobMat(r[1],r[2],r[3]):r in j1728FM(q)] cat [FrobMat(-r[1],r[2],r[3]):r in j1728FM(q)|r[1] ne 0]); 
end intrinsic;

intrinsic GL2FrobeniusMatrices(j::FldFinElt) -> SetEnum[AlgMatElt[RngInt]]
{ The set of Frobenius matrices of all elliptic curves with the specified j-invariant over a finite field. }
    if j eq 0 then return j0FrobeniusMatrices(#Parent(j)); end if;
    if j eq 1728 then return j1728FrobeniusMatrices(#Parent(j)); end if;
    a, b, D := EndomorphismRingData(EllipticCurveFromjInvariant(j)); d := D mod 2;
    S := {Matrix([[(a+b*d) div 2, b], [b*(D-d) div 4, (a-b*d) div 2]])};
    return a eq 0 select S else S join {Matrix([[(-a+b*d) div 2, b], [b*(D-d) div 4, (-a-b*d) div 2]])};
end intrinsic;

intrinsic EndomorphismRingData(E::CrvEll[FldFin]) -> RngIntElt, RngIntElt, RngIntElt
{ Given an elliptic curve E/Fq returns integers a, b, D, with 4*q=a^2-b^2*D, where a is the trace of the Frobenius endomorphism pi, D is the discriminant of the ring End(E) cap Q(pi). }
    q := #BaseRing(E);  _,p,e := IsPrimePower(q);
    j := jInvariant(E);
    a := TraceOfFrobenius(E);
    if j eq 0 and p ne 2 then
        D := [-4*p,-4,a^2 eq 4*q select 1 else -3,0,0,1][#AutomorphismGroup(E) div 2];
        b := D eq 1 select 0 else (bb where _,bb := IsSquare((a^2 - 4*q) div D));
        return a, b, D;
    elif j eq 1728 then
        D := [#TwoTorsionSubgroup(E) eq 4 select -p else -4*p,a^2 eq 4*q select 1 else -4,-3,0,0,0,0,0,0,0,0,1][#AutomorphismGroup(E) div 2];
        b := D eq 1 select 0 else (bb where _,bb := IsSquare((a^2 - 4*q) div D));
        return a, b, D;
    elif a mod p eq 0 then
        r2 := #TwoTorsionSubgroup(E) eq 4;
        D := a^2 eq 4*q select 1 else (r2 select -p else -4*p);
        b := D eq 1 select 0 else (r2 select 2 else 1)*p^((e-1) div 2);
        return a, b, D;
    end if;
    // If we get here E is ordinary and j(E) != 0,1728 
    D := a^2 - 4*q;  D0 := FundamentalDiscriminant(D); _,v := IsSquare(D div D0);
    if v eq 1 then return a,1,D; end if;
    if IsPrime(v) then
       if v gt 400 or v*v gt 8*Abs(D0) then
            if IsHCPRoot(D0,j) then return a,v,D0; else return a, 1, D; end if;
        else
            if OnFloor(E,v) then return a, 1, D; else return a, v, D0; end if;
        end if;
    end if;
    L := Factorization(v);
    if &and[ell[2] le 1 : ell in L | ell[1] gt 60] and L[#L][1] lt 400 and (#L eq 1 or L[#L][1] lt 4*Abs(D) div L[#L][1]^2) then
        b := &*[ell[1]^HeightAboveFloor(E,a,v,D0,ell[1],ell[2]) : ell in L];
        return a, b, D div (b*b);
    end if;
    u := 1; w := v;
    for ell in L do if ell[1] lt 60 then j,d := ClimbToSurface(j,ell[1],ell[2]); u *:= ell[1]^d; w div:=ell[1]^ell[2]; end if; end for;
    for uu in Prune(Divisors(w)) do if IsHCPRoot(uu^2*D0,j) then return a, (v div (u*uu)), uu^2*u^2*D0; end if; end for;
    return a, (v div (u*w)), u^2*w^2*D0;
end intrinsic;

