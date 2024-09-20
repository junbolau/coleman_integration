intrinsic InverseJFunction(j::FldComElt) -> FldComElt
{ Returns a \tau such that j(\tau) = j. 
The source is https://math.stackexchange.com/questions/438436/inverting-the-modular-j-function }
    C<i> := ComplexField();
    alpha := (1 + SquareRoot(1-1728/j))/2;
    return i*HypergeometricSeries(1/6,5/6,1,1-alpha)/HypergeometricSeries(1/6,5/6,1,alpha);
end intrinsic;

intrinsic TaylorExpansion(f::RngSerLaurElt, q0::FldComElt : prec := 100) -> RngSerLaurElt
{Computes the Taylor expansion of f(q) at q0.}
    R<qmq0> := LaurentSeriesRing(ComplexField(prec): Global := false);
    return &+ [Evaluate(Derivative(f, i), q0)/Factorial(i) * qmq0^i : i in [0..prec]] + O(qmq0^(prec + 1));
end intrinsic;

intrinsic Q(tau::FldComElt : prec := 100) -> FldComElt 
{Returns Q(tau) = e^(2 pi i tau).}
    C<i> := ComplexField(prec);
    return Exp(2*Pi(C)*i*tau);
end intrinsic;

intrinsic GetUniformizer(BB::Basepoint : prec := 100) -> RngSerLaurElt, RngUPolElt, RngIntElt
{Returns a local uniformizer around the residue disk of the basepoint as a power series in q, NOT necessarily at the basepoint itself. The uniformizer is:
    (1) j(q)^(1/3) if j \equiv 0 and g[1,1,-1,0]g^(-1) does not lie in \Gamma_H.
    (2) (j(q)-1728)^(1/2) if j \equiv 1728 and g[0,-1,1,0]g^(-1) does not lie in \Gamma_H.
    (3) Hilbert class polynomial of j otherwise.
}
    B := Parent(BB);
    R<q> := LaurentSeriesRing(Rationals(): Global:=false);
    g := BB`g; H := BB`H;
    N := BB`N;
    h := GetWidth(H,N);
    j := jInvariant(q^h);
    C<i> := ComplexField(prec);
    Z<x> := PolynomialRing(Integers());
    
    if GetRamification(BB) eq 3 then 
        f := TaylorExpansion(j, Q(Exp(2*Pi(C)*i/3)/h : prec := prec) : prec := prec);
        qmq0 := Parent(f).1;
        return (f-Coefficient(f,0)-Coefficient(f,1)*qmq0-Coefficient(f,2)*qmq0^2)^(1/3), x^3, 1;
    elif GetRamification(BB) eq 2 then
        f := TaylorExpansion(j, Q(i/h: prec := prec): prec := prec);
        qmq0 := Parent(f).1;
        return SquareRoot(f-Coefficient(f,0)-Coefficient(f,1)*qmq0), x^2+1728, 1;
    else 
        P_O := HilbertClassPolynomial(B`discrim);
        f := hom<Z->R|j>(P_O);
        tau := Evaluate(BB`tau_new, InfinitePlaces(Parent(B`tau))[1]);
        return TaylorExpansion(f, Q(tau/h: prec := prec): prec := prec), P_O, -1;
    end if;
end intrinsic;

// /*TODO: Figure out what happens when r = \infty.*/
// intrinsic GetUniformizer(BB:CuspBasepoint) -> RngSerLaurElt, Map
// {See above}
//     x := g*(GL(2,Integers(N))![1,1,0,1])*g^(-1);
//     y := x;
//     h := 1;
//     while not (y in BB`H) do 
//         h := h+1;
//         y := y*x;
//     end while;
//     C<i> := ComplexField();
//     R<q> := LaurentSeriesRing(C: Global:=false);
//     return (q-Exp(2*Pi(C)*i*BB`r))^(1/h);
// end intrinsic;

function change_uniformizer_raw(a, b, prec)
// a := [a1 a2 ... a_prec] taylor series of the uniformizer t at q0
// b := [b0 b1 ... b_prec] (NOTE it starts from 0) taylor series of f(q) at q0
// return c := [c0 ... c_prec] taylor series of f(q) dq in terms of the uniformizer t
    C<i> := ComplexField(prec);
    M := ZeroMatrix(C,prec,prec);
    c := [*0 : j in [1..prec]*];
    
    for ell in [0..prec-1] do M[ell+1,1] := (ell+1)*a[ell+1]; end for;

    for j in [1..prec-1] do
        for ell in [j..prec-1] do 
            M[ell+1,j+1] := &+[a[k]*M[ell-k+1,j] : k in [1..ell-j+1]];
        end for;
    end for;
    
    c[1] := M[1,1]^(-1)*b[1];
    for k in [2..prec] do
        c[k] := M[k,k]^(-1) * (b[k] - &+[M[k,j]*c[j] : j in [1..k-1]]);
    end for;
    return c;
end function;


intrinsic ChangeUniformizer(f::RngSerPowElt, BB::Basepoint : prec := 100) -> RngSerPowElt
{Changes the uniformizer of f from q to that of the basepoint.}
    B := Parent(BB);  H := BB`H;
    N := BB`N;
    h := GetWidth(H,N);

    f := LaurentSeriesRing(Rationals(): Global := false)!f;
    tau := Evaluate(BB`tau_new, InfinitePlaces(Parent(B`tau))[1]);
    ff := TaylorExpansion(f, Q(tau/h: prec := prec) : prec := prec);
    r := GetUniformizer(BB : prec := prec);

    a := [Coefficient(r,i) : i in [1..prec-1]];
    b := [Coefficient(ff,i) : i in [0..prec-1]];
    return change_uniformizer_raw(a,b,prec-1);
end intrinsic;