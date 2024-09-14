/* Main file for computing the Chabauty-Coleman set of a modular curve of genus 2 without using 
its plane model
*/

intrinsic ModelFreeChabautyColeman(p::RngIntElt, N::RngIntElt, gens::SeqEnum : prec:=10) -> Set
{
    INPUTS: 
        * "p" -- prime number 
        * "N" -- positive integer, the level of the modular curve
        * "gens" -- a set of generators for a subgroup G of GL(2, Z/NZ)

    OUTPUT: 
        * the Chabauty-Coleman set X(Q_p)_1 for the modular curve X defined by gens 
}
    // Step 1: Load the basepoints.

    // IntegralPowerSeries = BigColemanIntegral + TinyIntegralPowerSeries

    return {};
end intrinsic;

// intrinsic IntegralPowerSeries()
// {}
// end intrinsic;

// intrinsic BigIntegral(basis::SeqEnum, BBx::Basepoint, BBy::Basepoint) -> SeqEnum
// {}
//     A := HeckeOperator();
//     return [TinyHeckeIntegral(f, BBy) - TinyHeckeIntegral(f, BBx) : f in basis] * ((p+1)*IdentityMatrix(g) - A)^(-1); 
// end intrinsic;

// intrinsic TinyHeckeIntegral(p::RngIntElt, f::RngSerElt, BB::Basepoint) -> FldPadElt
// {
//     INPUTS: 
//         * "f" -- Power series element 
//         * "BB" -- Basepoint (call this x)
//     OUTPUT:
//         * \sum \int_(x_i)^x f, where each x_i corresponds to an elliptic curve p-isogenous to f
// }
//     blah := 0; // replace it with the Hecke points
//     return &+ [TinyIntegral(f,ui,u) : ui in blah];
// end intrinsic;

// intrinsic TinyIntegralPowerSeries(f::RngSerElt, BB::Basepoint) -> RngSerElt
// {}
    
// end intrinsic;

// intrinsic TinyIntegral(f::RngSerElt, BBx::Basepoint, BBy::Basepoint) -> FldPadElt
// {}
// end intrinsic;

// intrinsic Antiderivative(f::RngSerElt) -> RngSerElt
// {
//     INPUTS: 
//         * "f" -- Power series element
//     OUTPUT:
//         * An antiderivative of f, as a power series.
// }
//     t := Parent(f).1;
//     prec := Precision(Parent(f));
//     return &+[ Coefficient(f,n) * t^(n+1)/(n+1) : n in [0..prec-1]];
// end intrinsic;
// R