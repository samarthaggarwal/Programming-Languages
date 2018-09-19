hastype(Gamma,N,intT) :- integer(N).
hastype(Gamma,true,boolT).
hastype(Gamma,false,boolT).

%% lookup([],variable(X),W) :- fail.
lookup([],variable(X),typeVar(X)).

lookup([(variable(X),W)|Xs],variable(X),W) :- !.
lookup([(variable(Y),W1)|Xs],variable(X),W2) :- lookup(Xs,variable(X),W2).

hastype(Gamma,variable(X),W) :- lookup(Gamma,variable(X),W).

hastype(Gamma,plus(E1,E2),intT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,minus(E1,E2),intT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,mul(E1,E2),intT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,div(E1,E2),intT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,mod(E1,E2),intT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,exp(E1,E2),intT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,absolute(E1),intT) :- hastype(Gamma,E1,intT).

hastype(Gamma,lt(E1,E2),boolT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,gt(E1,E2),boolT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,lte(E1,E2),boolT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).
hastype(Gamma,gte(E1,E2),boolT) :- hastype(Gamma,E1,intT),hastype(Gamma,E2,intT).

hastype(Gamma,eq(E1,E2),boolT) :- hastype(Gamma,E1,W),hastype(Gamma,E2,W).

hastype(Gamma,and(E1,E2),boolT) :- hastype(Gamma,E1,boolT),hastype(Gamma,E2,boolT).
hastype(Gamma,or(E1,E2),boolT) :- hastype(Gamma,E1,boolT),hastype(Gamma,E2,boolT).
hastype(Gamma,xor(E1,E2),boolT) :- hastype(Gamma,E1,boolT),hastype(Gamma,E2,boolT).
hastype(Gamma,implies(E1,E2),boolT) :- hastype(Gamma,E1,boolT),hastype(Gamma,E2,boolT).
hastype(Gamma,not(E1),boolT) :- hastype(Gamma,E1,boolT).

hastype(Gamma,ite(E1,E2,E3),W) :- hastype(Gamma,E1,boolT),hastype(Gamma,E2,W),hastype(Gamma,E3,W).

hastype(Gamma,tuple([]),tupleT([])).
hastype(Gamma,tuple([X|Xs]),tupleT([T1|L])) :- hastype(Gamma,X,T1),hastype(Gamma,tuple(Xs),tupleT(L)).

hastype(Gamma,proj(N,tuple([])),W) :- fail.
hastype(Gamma,proj(0,tuple([X|Xs])),T1) :- hastype(Gamma,tuple([X]),tupleT([T1])),!.
hastype(Gamma,proj(N,tuple([X|Xs])),W) :- integer(N), M is N-1,hastype(Gamma,proj(M,tuple(Xs)),W).

hastype(Gamma,lambda(variable(X),E1),arrowT(T1,T2)) :- hastype([(variable(X),T1)|Gamma],E1,T2),!.
hastype(Gamma,call(E1,E2),T2) :- hastype(Gamma,E2,T1), hastype(Gamma,E1,arrowT(T1,T2)).

append([],A,A).
append([X|Xs],A,[X|B]) :- append(Xs,A,B).

typeElaborates(Gamma,(variable(X),E1),[(variable(X),T1)]) :- hastype(Gamma,E1,T1).
typeElaborates(Gamma,seq(D1,D2),Gamma22) :- typeElaborates(Gamma,D1,Gamma1), append(Gamma1,Gamma,Gamma11), typeElaborates(Gamma11,D2,Gamma2), append(Gamma2,Gamma1,Gamma22).
typeElaborates(Gamma,par(D1,D2),Gamma22) :- typeElaborates(Gamma,D1,Gamma1), typeElaborates(Gamma,D2,Gamma2), append(Gamma2,Gamma1,Gamma22).
typeElaborates(Gamma,local(D1,D2),Gamma2) :- typeElaborates(Gamma,D1,Gamma1), append(Gamma1,Gamma,Gamma11), typeElaborates(Gamma11,D2,Gamma2).

hastype(Gamma,let(D,E1),T1) :- typeElaborates(Gamma,D,Gamma1),append(Gamma1,Gamma,Gamma11), hastype(Gamma11,E1,T1).


%% test cases

%% hastype(t,234,W).
%% hastype(t,true,W).
%% hastype(t,false,W).

%% lookup([],variable(x),W).
%% lookup([(variable(x),intT)],variable(x),W).
%% lookup([(variable(y),boolT),(variable(x),intT)],variable(x),W).

%% hastype( [(variable(y),boolT),(variable(x),intT)],variable(x),W).

%% hastype([(variable(y),boolT),(variable(x),intT)],plus(-14,variable(x)),W).

%% hastype([(variable(y),boolT),(variable(x),intT)],absolute(variable(x)),W).

%% hastype([(variable(y),boolT),(variable(x),intT)],lt(variable(x),23),W).
%% hastype([(variable(y),boolT),(variable(x),intT)],eq(variable(x),23),W).
%% hastype([(variable(y),boolT),(variable(x),intT)],eq(true,false),W).

%% hastype([],eq(variable(x),variable(x)),W).

%% hastype([(variable(y),boolT),(variable(x),intT)],and(true,false),W).
%% hastype([(variable(y),boolT),(variable(x),intT)],ite(true,23,variable(y)),W).
%%		%% returns false as this case is type incorrect

%% hastype([(variable(y),boolT),(variable(x),intT)],tuple([true,false,23,variable(y),variable(x)]),W).

%% hastype([(variable(y),boolT),(variable(x),intT)],proj(0,tuple([true,false,23,variable(y),variable(x)])),W).

%% hastype([(variable(y),boolT),(variable(x),intT)],lambda(variable(x),plus(variable(x),32)),W).
%% hastype([(variable(y),boolT),(variable(x),intT)],call( lambda(variable(x),plus(variable(x),32)) ,23),W).
%% hastype([(variable(y),boolT),(variable(x),intT)],call( lambda(variable(y),and(variable(y),false)) ,23),W).

%% typeElaborates([(variable(y),boolT),(variable(x),intT)],(variable(y),true),W).
%% typeElaborates([(variable(y),boolT),(variable(x),intT)],seq((variable(y),23),(variable(y),true)),W).
%% typeElaborates([(variable(y),boolT),(variable(x),intT)],par((variable(y),23),(variable(x),true)),W).
%% typeElaborates([(variable(y),boolT),(variable(x),intT)],local( (variable(z),23) , (variable(x),lte(variable(z),45) ) ),W).

%% hastype([(variable(y),boolT),(variable(x),intT)],let((variable(y),true),and(variable(y),false)),W).
%% hastype([],let((variable(y),true),and(variable(y),false)),W).
%% hastype([],let( seq( (variable(y),true),(variable(x),false) ),and(variable(y),variable(x))),W).
%% hastype([],let( par( (variable(y),true),(variable(x),false) ),and(variable(y),variable(x))),W).
%% hastype([],let( local( (variable(y),true),(variable(x),xor(variable(y),false)) ),and(variable(x),variable(x))),W).
%% hastype([],let( local( (variable(y),34),(variable(x),exp(variable(y),plus(1,2))) ),mod(variable(x),21) ),W).