// Computes a basis of weight 2 cusp forms for a congruence subgroup Gamma using Zywina's 
// Magma implementation of algorithms in the paper "Computing actions on cusp forms" 
// https://arxiv.org/pdf/2001.07270 


intrinsic CuspFormsBasis(N::RngIntElt, gens::SeqEnum, q_prec::RngIntElt) -> ModTupRngElt
{
    INPUTS: 
        * "p" -- a prime number
        * "gens" -- a set of generators for a subgroup G of GL(2, Z/NZ)
        * "q_prec" -- a positive integer (default 5000), number of coefficients in the q-expansion desired 

    OUTPUT: 
        A basis for the space of weight 2 cusp forms of the congruence subgroup specified by gens. 
}
    K<zetaN> := CyclotomicField(N);
    //g,B,M,phi := SL2ActionOnCuspForms(N, 2, q_prec: HNF := true);

    G := sub<GL(2,Integers(N))|gens>;
    basis := ComputeModularFormsForXG(G, 2, q_prec);

    G_basis := Matrix(#basis, q_prec, [Coefficients(i): i in basis]);
    //B := ChangeRing(B, K);

    CuspForms := G_basis;
    //CuspForms := Solution(B, G_basis);

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

    return CuspForms;
end intrinsic;

