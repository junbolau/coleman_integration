intrinsic InverseJFunction(j:FldComElt) -> FldComElt
{ Returns a \tau such that j(\tau) = j. 
The source is https://math.stackexchange.com/questions/438436/inverting-the-modular-j-function }
    C<i> := ComplexField();
    alpha := (1 + SquareRoot(1-1728/j))/2;
    return i*HypergeometricSeries(1/6,5/6,1,1-alpha)/HypergeometricSeries(1/6,5/6,1,alpha);
end intrinsic;

intrinsic TaylorExpansion(f::RngSerLaurElt, q0::FldComElt : prec := 100) -> RngSerLaurElt
{Computes the Taylor expansion of f(q) at q0.}
    R<qmq0> := LaurentSeriesRing(ComplexField(): Global := false);
    return &+ [Evaluate(Derivative(f, i), q0)/Factorial(i) * qmq0^i : i in [0..prec]] + O(qmq0^(prec + 1));
end intrinsic;




// intrinsic GetUniformizer(BB:Basepoint) -> RngSerLaurElt, Map
// {Returns a local uniformizer around the residue disk of the basepoint as a power series in q, NOT necessarily at the basepoint itself. The uniformizer is:
//     (1) j(q) - (j mod p) if not in the below cases
//     (2) j(q)^(1/3) if j \equiv 0 and g[1,1,-1,0]g^(-1) does not lie in \Gamma_H.
//     (3) (j(q)-1728)^(1/2) if j \equiv 1728 and g[0,-1,1,0]g^(-1) does not lie in \Gamma_H.
//     (4) (q-r)^(1/h) if cuspidal, where h is the smallest positive integer such that g[1,h,0,1]g^(-1) lies in \Gamma_H.
// }
//     B := Parent(BB);
//     j := B`j_modp; g := BB`g; H := BB`H;
//     R<q> := LaurentSeriesRing(Rationals(): Global:=false);
//     R2<q2> := LaurentSeriesRing(Rationals(): Global:=false);
//     R3<q3> := LaurentSeriesRing(Rationals(): Global:=false);
//     f2 := hom<R->R2|q2^2>;
//     f3 := hom<R->R3|q3^3>;
//     if (j eq 0) and (not g*GL(2,Integers(N))![1,1,-1,0]*g^(-1) in H) then 
//         return CubeRoot(f3(jInvariant(q)));
//     elif (j eq (1728 mod p)) and (not g*GL(2,Integers(N))![0,1,-1,0]*g^(-1) in H) then
//         return SquareRoot(f(jInvariant(q))-1728);
//     else 
//         return jInvariant(q) - j;
//     end if;
// end intrinsic;

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
