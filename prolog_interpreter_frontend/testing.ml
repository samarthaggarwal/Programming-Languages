Main.token_list_of_string_prog "g(1).g(2).f(X):-g(X).";;

Main.token_list_of_string_prog "g(1).g(2).f(X):-g(X),!.";;

Main.token_list_of_string_prog "edge(a,b).
edge(a,c).
edge(b,d).
edge(b,e).
edge(c,e).
edge(c,f).
edge(e,g).
edge(f,h).
edge(i,c).
path(X,X).
path(X,Y) :- edge(X,Z) , path(Z,Y).";;

Main.token_list_of_string_prog "edge(a,b).
edge(a,c).
path(X,X).
path(X,Y) :- edge(X,Z) , path(Z,Y).";;

Main.parse_program "g(1).g(2).f(X):-g(X).";;

Main.parse_program "g(1).g(2).f(X):-g(X),!.";;

Main.parse_program "edge(a,b).edge(a,c).path(X,X).path(X,Y) :- edge(X,Z) , path(Z,Y).";;

Main.parse_program "edge(a,b).
edge(a,c).
path(X,X).
path(X,Y) :- edge(X,Z) , path(Z,Y).";;

Main.token_list_of_string_prog "member(X) :- fail.";;
Main.parse_program "member(X) :- fail.";;

Main.token_list_of_string_prog "edge(a,b),path(X,Y).";;
Main.parse_program "edge(a,b),path(X,Y).";;

Main.token_list_of_string_queries "edge(a,b),edge(b,c),path(a,X).";;

Main.parse_query_list "edge(a,b),edge(b,c),path(a,X).";;

Main.parse_query_list "edge(a,b),edge(b,c),path(a,X),!,fail.";;


let rec format t = match t with
| Ast.Atom(s,l) -> Atom(s,map format l)
| Ast.Fun(s,l) -> Fun(s,map format l)
| Ast.V(x) -> V(x)
| Ast.Clause(Ast.H(h),Ast.B(b)) -> Clause(H(format h),B(map format b))
| _ -> t
;;


Ast.execute (Main.parse_query_list "edge(a,b).") (Main.parse_program "edge(a,b).edge(a,c).path(X,X).path(X,Y) :- edge(X,Z) , path(Z,Y).");;

Ast.execute (Main.parse_query_list "edge(Y,X).") (Main.parse_program "edge(a,b).edge(a,c).path(X,X).path(X,Y) :- edge(X,Z) , path(Z,Y).");;

let ql = Main.parse_query_list "edge(Y,X).";;
let pl = Main.parse_program "edge(a,b).
edge(a,c).
edge(b,d).
edge(b,e).
edge(c,e).
edge(c,f).
edge(e,g).
edge(f,h).
edge(i,c).
path(X,X).
path(X,Y) :- edge(X,Z) , path(Z,Y).";;
Ast.execute ql pl;;

let ql = Main.parse_query_list "path(X,Y).";;
let pl = Main.parse_program "edge(a,b).
edge(a,c).
edge(b,d).
edge(b,e).
edge(c,e).
edge(c,f).
edge(e,g).
edge(f,h).
edge(i,c).
path(X,X).
path(X,Y) :- edge(X,Z) , path(Z,Y).";;
Ast.execute ql pl;;


let ql = Main.parse_query_list "f(X),g(X).";;
let pl = Main.parse_program "g(1).
g(2).
f(X):- g(X),!.";;
Ast.execute ql pl;;