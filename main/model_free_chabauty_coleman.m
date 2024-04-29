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

    return {};
end intrinsic;
