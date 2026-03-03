% types
tff(species_type, type, species: $tType).
tff(foodlink_type, type, foodlink: $tType).
tff(foodchain_type, type, foodchain: $tType).
tff(complete_foodchain_type, type, complete_foodchain: $tType).

tff(eats_type, type, eats: (species * species) > $o).
tff(primary_producer_type, type, primary_producer: species > $o).
tff(apex_predator_type, type, apex_predator: species > $o).
tff(depends_type, type, depends: (species * species) > $o).
tff(eater_type, type, eater: foodlink > species).
tff(eaten_type, type, eaten: foodlink > species).
tff(start_of_fc_type, type, start_of: foodchain > species).
tff(end_of_fc_type, type, end_of: foodchain > species).
tff(start_of_cfc_type, type, start_of_complete: complete_foodchain > species).
tff(end_of_cfc_type, type, end_of_complete: complete_foodchain > species).
tff(chain_from_to_type, type, chain_from_to: (foodchain * species * species) > $o).

% axioms
%The eater of a food link eats the eaten of the link.
tff(eats_axiom, axiom, ![L: foodlink]: eats(eater(L), eaten(L))).

%The eaten and eater of a food link are not the same (no cannibalism).
tff(no_cannibalism_axiom, axiom, ![L: foodlink]: ~ (eater(L) = eaten(L))).

%Every species eats something or is eaten by something (or both).
tff(eat_or_eaten_axiom, axiom, ![S: species]: 
            (?[T: species]: eats(S, T) | ?[U: species]: eats(U, S))).

%Something is a primary producer iff it eats no other species.
tff(primary_producer_axiom, axiom, ![S: species]: 
            (primary_producer(S) <=> ![T: species]: ~ eats(S, T))).

%If something is a primary producer then there is no food link such that the primary producer is the eater of the food link.
tff(primary_producer_no_eater_conj, conjecture, ![S: species]: 
            (primary_producer(S) => ![L: foodlink]: (eater(L) != S))).

%Every primary producer is eaten by some other species.
tff(primary_producer_eaten_conj, conjecture, ![S: species]: (primary_producer(S) => 
            ?[T: species]: eats(T, S))).
            
%If a species is not a primary producer then there is another species that it eats.
tff(not_primary_producer_conj, conjecture, ![S: species]:
            (~primary_producer(S) => ?[T: species]: eats(S, T))).

%Something is an apex predator iff there is no species that eats it.
tff(apex_predator_axiom, axiom, ![S: species]: (apex_predator(S) <=> ![T: species]: ~ eats(T, S))).

%If something is an apex predator then there is no food link such that the apex predator is the eaten of the food link.
tff(apex_predator_no_foodlink_conj, conjecture, ![S: species]: (apex_predator(S) => ![L: foodlink]: (eaten(L) != S))).

%Every apex predator eats some other species.
tff(apex_predator_eats_conj, conjecture, ![S: species]: (apex_predator(S) => ?[T: species]: eats(S, T))).

% If a species is not a apex predator then there is another species that eats it.
tff(not_apex_predator_conj, conjecture, ![S: species]: (~apex_predator(S) => ?[T: species]: eats(T, S))).

%For every food chain, the start of the chain is the eaten of some food link, and one of the following holds: (i) the eater of the food link is the end of the food chain, xor (ii) there is a shorter food chain (shorter by one food link) from the eater of the food link to the end of the whole food chain.

tff(foodchain_axiom, axiom,
    ![FC: foodchain] :
      ?[L: foodlink] :
        ( eaten(L) = start_of(FC)
        & ( eater(L) = end_of(FC)
          | ?[FC2: foodchain] :
              ( start_of(FC2) = eater(L)
              & end_of(FC2) = end_of(FC) ) ) )
).
tff(chain_from_to_axiom, axiom,
    ![FC: foodchain, X: species, Y: species] :
      (chain_from_to(FC, X, Y) <=> (start_of(FC) = X & end_of(FC) = Y))
).
%There is no food chain from a species back to itself (no death spirals).
tff(no_death_spirals_axiom, axiom, ![FC: foodchain]: ~(start_of(FC) = end_of(FC))).

%A complete food chain starts at a primary producer, and ends at an apex predator.
tff(complete_foodchain_axiom, axiom, ![CFC: complete_foodchain]: 
            (primary_producer(start_of_complete(CFC)) & apex_predator(end_of_complete(CFC)))).

%Every species is in some complete food chain, i.e., (i) the species is the primary producer start of the complete food chain, or (ii) the species is the apex predator at the end of the complete food chain, or (iii) there is a non-complete food chain from the start of the complete food chain to the species, and another non-complete food chain from the species to the end of the complete food chain.

tff(all_species_in_some_complete_foodchain_axiom, axiom,
    ![S: species] :
      ?[CFC: complete_foodchain] :
        ( S = start_of_complete(CFC)
        | S = end_of_complete(CFC)
        | ?[FC1: foodchain, FC2: foodchain] :
            ( chain_from_to(FC1, start_of_complete(CFC), S)
            & chain_from_to(FC2, S, end_of_complete(CFC)) ) )
).

%The start species of a complete food chain does not eat the end species.
tff(start_does_not_eat_end_conj, conjecture, ![CFC: complete_foodchain]: ~ eats(start_of_complete(CFC), end_of_complete(CFC))).

%If a species is neither a primary producer nor an apex predator, then there is a food chain from a primary producer to that species, and another food chain from that species to an apex predator.
tff(not_primary_nor_apex_conj, conjecture,
    ![S: species] :
      ( (~primary_producer(S) & ~apex_predator(S)) =>
        ?[CFC: complete_foodchain] :
          ?[FC1: foodchain, FC2: foodchain] :
            ( chain_from_to(FC1, start_of_complete(CFC), S)
            & chain_from_to(FC2, S, end_of_complete(CFC) ) ) )
).


% Given two species, the first depends on the second iff there is a food chain from the second to the first.
tff(depends_axiom, axiom, ![S1: species, S2: species]: (depends(S1, S2) <=> ?[FC: foodchain]: chain_from_to(FC, S2, S1))).



% If a species is not an apex predator then there is an apex predator that depends on the species.
tff(not_apex_depends_conj, conjecture, ![S: species]: (~apex_predator(S) => ?[A: species]: (apex_predator(A) & depends(A, S)))).



% An apex predator depends on all primary producers of all complete food chains that end at the apex predator.
tff(apex_depends_on_primary_producers_conj, conjecture,
    ![A: species] :
      ( apex_predator(A)
     => ![CFC: complete_foodchain] :
          ( end_of_complete(CFC) = A
         => depends(A, start_of_complete(CFC)) ) )
).