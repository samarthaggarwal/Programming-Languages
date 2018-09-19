append([],A,A).
append([X|Xs],A,[X|L]) :- append(Xs,A,L).
