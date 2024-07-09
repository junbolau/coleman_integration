tay_derivative_list := function(f, s, prec)
    return [Evaluate(Derivative(f, i), s)/Factorial(i) : i in [0..prec]];
end function;

asdf := function(a, b, prec)
// a := [a1 a2 ... a_prec] taylor series of the uniformizer t at q0
// b := [b0 b1 ... b_prec] (NOTE it starts from 0) taylor series of f(q) at q0
// return c := [c0 ... c_prec] taylor series of f(q) dq in terms of the uniformizer t
    F := [[0 : i in [0..prec]] : k in [0..prec]];
    c := [0 : i in [0..prec]];
    for i in [0..prec] do 
        for ell in [i..prec] do 
            if i eq 0 then  
                F[1][ell+1] := a[ell+1];
            else 
                F[i+1][ell+1] := &+[a[k]*F[i][ell-k+1] : k in [1..ell-i+1]];
            end if;
        end for;
    end for;

    for ell in [0..prec] do 
        if ell eq 0 then 
            sum := 0;
        else 
            sum := &+ [c[k+1]*F[k+1][ell+1] : k in [0..ell-1]];
        end if;
        c[ell+1] := a[1]^{-ell-1}*(b[ell+1] - sum);
    end for;
    return c;
end function;

choose_uniformizer := function(j, g, Gamma_H, p)
// not working yet
    assert p > 3;
    if Valuation(j) < 0 then 
        return 0;
    elif (j mod p) eq 0 and not (g*(Gamma_H![1,1,-1,0])*g^(-1) in Gamma_H) then 
        return 0;
    elif (j mod p) eq (1728 mod p) and not (g*(Gamma_H![0,1,-1,0])*g^(-1) in Gamma_H) then 
        return 0;
    else 
        return jInvariant(q) - j;
    end if;
end function;