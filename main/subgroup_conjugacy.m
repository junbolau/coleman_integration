// Given subgroups H1, H2 of G = GL2(N), check if H1 is conjugate to a subgroup of H2.
conjugate_to := function(H1,H2,G)
    N1 := Normalizer(G, H1);
    N2 := Normalizer(G, H2);
    DoubleCosets(G,N1,N2);
    
end

