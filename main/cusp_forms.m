// Computes a basis of weight 2 cusp forms for a congruence subgroup Gamma using Zywina's 
// Magma implementation of algorithms in the paper "Computing actions on cusp forms" 
// https://arxiv.org/pdf/2001.07270 


intrinsic CuspFormsBasis(N::RngIntElt, gens::SeqEnum: q_prec := 5000) -> ModTupRngElt
{
    INPUTS: 
        * "p" -- a prime number
        * "gens" -- a set of generators for a subgroup G of GL(2, Z/NZ)
        * "q_prec" -- a positive integer (default 5000), number of coefficients in the q-expansion desired 

    OUTPUT: 
        A basis for the space of weight 2 cusp forms of the congruence subgroup specified by gens. 
}
    K<zetaN> := CyclotomicField(N);
    g,B,M,phi := SL2ActionOnCuspForms(N, 2, q_prec: HNF := true);

    G := sub<GL(2,Integers(N))|gens>;
    basis := ComputeModularFormsForXG(G, 2, q_prec);

    G_basis := Matrix(#basis, q_prec, [Coefficients(i): i in basis]);
    B := ChangeRing(B, K);

    return Solution(B, G_basis)[1];
end intrinsic;

