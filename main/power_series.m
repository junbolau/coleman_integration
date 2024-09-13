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
