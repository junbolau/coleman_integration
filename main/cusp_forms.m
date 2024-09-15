// Computes a basis of weight 2 cusp forms for a congruence subgroup Gamma using Zywina's 
// Magma implementation of algorithms in the paper "Computing actions on cusp forms" 
// https://arxiv.org/pdf/2001.07270 


intrinsic CuspFormsBasis(N::RngIntElt, gens::SeqEnum, q_prec::RngIntElt) -> ModTupRngElt
{
    INPUTS: 
        * "p" -- a prime number
        * "gens" -- a set of generators for a subgroup G of GL(2, Z/NZ)
        * "q_prec" -- a positive integer, number of coefficients in the q-expansion desired 

    OUTPUT: 
        A basis for the space of weight 2 cusp forms of the congruence subgroup specified by gens. 
}
    K<zetaN> := CyclotomicField(N);
    //g,B,M,phi := SL2ActionOnCuspForms(N, 2, q_prec: HNF := true);

    G := sub<GL(2,Integers(N))|gens>;
    Gamma_G := PSL2Subgroup(G);

    // If G is of real type use Assaf-Box's algorithm, else use Zywina's algorithm 
    if Conjugate(G,GL(2,Integers(N))![-1, 0, 0, 1]) eq G then
        M := ModularSymbols(Gamma_G, 2, Rationals(), 0);
        S := CuspidalSubspace(M);
        D := Decomposition(S, HeckeBound(S));
        Coefficients := [[0: j in [1..q_prec]] : i in [1..#D]];
        for i in [1..#D] do
            q_form := qEigenform(D[i], q_prec+1);
            for j in [1..q_prec] do
                Coefficients[i,j] := Coefficient(q_form, j);
            end for;
        end for;
        CuspForms := Matrix(#D, q_prec, Coefficients);
    else
        basis := ComputeModularFormsForXG(G, 2, q_prec);

        G_basis := Matrix(#basis, q_prec, [Coefficients(i): i in basis]);
        //B := ChangeRing(B, K);

        CuspForms := G_basis;
    end if;  


    return CuspForms;

    /* FOR PRINTING 
    OutputFileName := "./qexps.txt";
    
    for i in [1..Nrows(CuspForms)] do
        f := CuspForms[i];
        fprintf OutputFileName, "[";
        for j in [1..Ncols(CuspForms)] do 
            if j ne Ncols(CuspForms) then
                fprintf OutputFileName, "%o,", Eltseq(f[j]);
            else 
                fprintf OutputFileName, "%o", Eltseq(f[j]);
            end if;
        end for;
        fprintf OutputFileName, "]\n";
    end for;
    */
    
end intrinsic;

