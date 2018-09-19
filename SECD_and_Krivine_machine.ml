type var = V of string ;;
type exp = E of var 
		| Lambda of var* exp
		| Call of exp * exp
		| T
		| F
		| Nat of int
		| Hole
		| Plus of exp*exp
		| Minus of exp*exp  
		| Mul of exp*exp
		| Div of exp*exp
		| Mod of exp*exp 
		| Exponent of exp*exp 
		| Abs of exp		
		| Eq of exp*exp
		| Lt of exp*exp
		| Gt of exp*exp
		| Lte of exp*exp 
		| Gte of exp*exp
		| And of exp*exp 
		| Or of exp*exp 
		| Not of exp
		| Xor of exp*exp
		| Implies of exp*exp
		| Tup of (exp list)
		| Tupev of ((exp list)*(exp list)) 
		| Proj of exp*exp
		| Ite of exp*exp*exp
		| Local of var*exp*exp
		;;

type opcode =
| LOOKUP of var
| RET
| CLOS of var*(opcode list)
| APP
| TRUE
| FALSE
| CONST of int
| PLUS
| MINUS
| MUL
| DIV 
| MOD 
| EXPONENT 
| ABS 
| EQ
| LT
| GT
| LTE 
| GTE 
| AND 
| OR 
| NOT 
| XOR 
| IMPLIES 
| TUP of (opcode list)
| TUPOVER
| PROJ
| COND of (opcode list)*(opcode list)
| BIND of var
| UNBIND of var
;;

let rec compile e = match e with
| E(v) -> [LOOKUP(v)]
| Lambda(v,e) -> [CLOS(v,compile(e)@[RET])]
| Call(e1,e2) -> compile(e1)@compile(e2)@[APP]
| T -> [TRUE]
| F -> [FALSE]
| Nat(n) -> [CONST(n)]
| Plus(e1,e2) -> compile(e1)@compile(e2)@[PLUS]
| Minus(e1,e2) -> compile(e1)@compile(e2)@[MINUS]
| Mul(e1,e2) -> compile(e1)@compile(e2)@[MUL]
| Div(e1,e2) -> compile(e1)@compile(e2)@[DIV]
| Mod(e1,e2) -> compile(e1)@compile(e2)@[MOD]
| Exponent(e1,e2) -> compile(e1)@compile(e2)@[EXPONENT]
| Abs(e1) -> compile(e1)@[ABS]
| Eq(e1,e2) -> compile(e1)@compile(e2)@[EQ]
| Lt(e1,e2) -> compile(e1)@compile(e2)@[LT]
| Gt(e1,e2) -> compile(e1)@compile(e2)@[GT]
| Lte(e1,e2) -> compile(e1)@compile(e2)@[LTE]
| Gte(e1,e2) -> compile(e1)@compile(e2)@[GTE]
| And(e1,e2) -> compile(e1)@compile(e2)@[AND]
| Or(e1,e2) -> compile(e1)@compile(e2)@[OR]
| Not(e1) -> compile(e1)@[NOT]
| Xor(e1,e2) -> compile(e1)@compile(e2)@[XOR]
| Implies(e1,e2) -> compile(e1)@compile(e2)@[IMPLIES]
| Tup(l) -> let rec f l = match l with [] -> [] | x::xs -> compile(x)@(f xs) in [TUP(f l)]
| Proj(n,e) -> compile(n)@compile(e)@[PROJ]
| Ite(e1,e2,e3) -> compile(e1)@[COND(compile(e2),compile(e3))]
| Local(x,e1,e2) -> compile(e1)@[BIND(x)]@compile(e2)@[UNBIND(x)]
;;

type table = (var * answer) list 
and vclosure = table * exp
and answer = Tr | Fl | N of int | Tuple of (answer list) | A of vclosure | AVcomp of table * var * (opcode list) | Abstact of exp;;


let t1 = [(V("a"),T)];;
let a = (t1,T);;

exception NotInTable;;

let rec look v t = match t with
| [] -> raise NotInTable
| (v1,a1)::t1 -> if (v1 = v) then a1 else (look v t1)
;;

let rec reverse l = match l with
| [] -> []
| x::xs -> (reverse xs)@[x]
;;

(* O(log b) exponent function *)
let rec expon a b = match b with
| 0 -> 1
| 1 -> a
| b -> if (b mod 2 = 0) then (expon (a*a) (b/2)) else a*(expon (a*a) ((b-1)/2) )
;;

let rec unbind l v = match l with []->[] | (v1,a1)::zs -> if(v=v1) then zs else (v1,a1)::(unbind zs v);;

let rec execute s e c d = match (s,e,c,d) with
| (a::s1,e,[],d) -> a
| (s,e,LOOKUP(v)::c1,d) -> execute ((look v e)::s) e c1 d
| (s,e,TRUE::c1,d) -> execute (Tr::s) e c1 d
| (s,e,FALSE::c1,d) -> execute (Fl::s) e c1 d
| (s,e,CONST(n)::c1,d) -> execute (N(n)::s) e c1 d
| (N(n2)::N(n1)::s,e,PLUS::c1,d) -> execute (N(n1+n2)::s) e c1 d
| (N(n2)::N(n1)::s,e,MINUS::c1,d) -> execute (N(n1-n2)::s) e c1 d
| (N(n2)::N(n1)::s,e,MUL::c1,d) -> execute (N(n1*n2)::s) e c1 d
| (N(n2)::N(n1)::s,e,DIV::c1,d) -> execute (N(n1/n2)::s) e c1 d
| (N(n2)::N(n1)::s,e,MOD::c1,d) -> execute (N(n1 mod n2)::s) e c1 d
| (N(n2)::N(n1)::s,e,EXPONENT::c1,d) -> execute (N(expon n1 n2)::s) e c1 d
| (N(n1)::s,e,ABS::c1,d) -> execute (N(if n1<0 then (-1)*n1 else n1)::s) e c1 d
| (a2::a1::s,e,EQ::c1,d) -> if (a1=a2) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (N(n2)::N(n1)::s,e,LT::c1,d) -> if (n1<n2) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (N(n2)::N(n1)::s,e,GT::c1,d) -> if (n1>n2) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (N(n2)::N(n1)::s,e,LTE::c1,d) -> if (n1<=n2) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (N(n2)::N(n1)::s,e,GTE::c1,d) -> if (n1>=n2) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (b2::b1::s,e,AND::c1,d) -> if (b1=Tr && b2=Tr) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (b2::b1::s,e,OR::c1,d) -> if (b1=Tr || b2=Tr) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (b1::s,e,NOT::c1,d) -> if (b1=Fl) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (b2::b1::s,e,XOR::c1,d) -> if (b1<>b2) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (b2::b1::s,e,IMPLIES::c1,d) -> if (b1=Fl || b2=Tr) then execute (Tr::s) e c1 d else execute (Fl::s) e c1 d
| (s,e,TUP(c2)::c1,d) -> execute [] e (c2@[TUPOVER]) ((s,e,c1)::d)
| (s1,e1,TUPOVER::c1,(s2,e2,c2)::d) -> execute (Tuple(reverse s1)::s2) e2 c2 d
| (Tuple(l)::N(n1)::s,e,PROJ::c1,d) -> execute ((List.nth l n1)::s) e c1 d
| (Tr::s,e,COND(c2,c3)::c1,d) -> execute s e (c2@c1) d
| (Fl::s,e,COND(c2,c3)::c1,d) -> execute s e (c3@c1) d
| (a::s,e,BIND(x)::c1,d) -> execute s ((x,a)::e) c1 d
| (s,e,UNBIND(x)::c1,d) -> execute s (unbind e x) c1 d
| (s,e,CLOS(v,c2)::c1,d) -> execute ((AVcomp(e,v,c2))::s) e c1 d
| (a2::(AVcomp(e,v,c2))::s ,e1,APP::c1,d) -> execute [] ((v,a2)::e) c2 ((s,e1,c1)::d)
| (a2::s1,e1,RET::c1,(s2,e2,c2)::d) -> execute (a2::s2) e2 c2 d
;;


exception InvalidFormat;;

type ktable = (var * closure) list
and closure = CL of (ktable * exp)
;;
(* 
let rec map f l = match l with
| [] -> []
| x::xs -> (f x)::(map f xs)
;; *)


let rec tuple_check l = match l with
| [] -> true
| T::xs -> tuple_check xs
| F::xs -> tuple_check xs
| Nat(n)::xs -> tuple_check xs
| Lambda(v,e)::xs -> tuple_check xs
| Tup(l1)::xs -> ((tuple_check l1) && (tuple_check xs))
| _ -> false
;;


let rec krivine c s = match (c,s) with
| ( CL(t,T) ,[]) -> CL ([],T) 
| ( CL(t,F) ,[]) -> CL ([],F)
| ( CL(t,Nat(n)) ,[]) -> CL ([],Nat(n))
| ( CL(t,E(v)) ,s) -> krivine (look v t) s

| ( CL(t,Lambda(v,e)) ,[]) -> (CL ( t , Lambda(v,e) )) 

| ( CL(t,Call(e1,e2)) ,s) -> krivine (CL (t,e1)) (CL(t,Call(Hole,e2))::s)
| ( CL(t,Lambda(v,e)) ,CL(t1,Call(Hole,e2))::s) -> krivine (CL ( (v, CL (t1,e2) )::t , e )) s 

| ( CL(t, Plus(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Plus(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Plus(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Plus(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Plus(Nat(n1),Hole)))::s ) -> krivine (CL (t,Nat(n1 + n2))) s

| ( CL(t, Minus(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Minus(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Minus(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Minus(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Minus(Nat(n1),Hole)))::s ) -> krivine (CL (t,Nat(n1 - n2))) s

| ( CL(t, Mul(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Mul(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Mul(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Mul(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Mul(Nat(n1),Hole)))::s ) -> krivine (CL (t,Nat(n1 * n2))) s

| ( CL(t, Div(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Div(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Div(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Div(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Div(Nat(n1),Hole)))::s ) -> krivine (CL (t,Nat(n1 / n2))) s

| ( CL(t, Mod(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Mod(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Mod(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Mod(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Mod(Nat(n1),Hole)))::s ) -> krivine (CL (t,Nat(n1 mod n2))) s

| ( CL(t, Exponent(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Exponent(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Exponent(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Exponent(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Exponent(Nat(n1),Hole)))::s ) -> krivine (CL (t,Nat(expon n1 n2))) s

| ( CL(t, Abs(e1) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Abs(Hole)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Abs(Hole)))::s ) -> krivine (CL (t,Nat(if n1<0 then ((-1)*n1) else n1))) s

| ( CL(t, Eq(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Eq(Hole,e2)))::s)
| ( CL(t, T) , (CL (t1,Eq(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Eq(T,Hole)))::s )
| ( CL(t, F) , (CL (t1,Eq(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Eq(F,Hole)))::s )
| ( CL(t, Nat(n)) , (CL (t1,Eq(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Eq(Nat n,Hole)))::s )
| ( CL(t, T) , (CL (t1,Eq(b1,Hole)))::s ) -> krivine (CL (t, (if b1=T then T else F) )) s
| ( CL(t, F) , (CL (t1,Eq(b1,Hole)))::s ) -> krivine (CL (t, (if b1=F then T else F) )) s
| ( CL(t, Nat(n)) , (CL (t1,Eq(b1,Hole)))::s ) -> krivine (CL (t, (if b1=Nat(n) then T else F) )) s

| ( CL(t, Lt(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Lt(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Lt(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Lt(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Lt(Nat(n1),Hole)))::s ) -> krivine (CL (t, (if n1<n2 then T else F) )) s

| ( CL(t, Gt(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Gt(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Gt(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Gt(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Gt(Nat(n1),Hole)))::s ) -> krivine (CL (t, (if n1>n2 then T else F) )) s

| ( CL(t, Lte(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Lte(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Lte(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Lte(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Lte(Nat(n1),Hole)))::s ) -> krivine (CL (t, (if n1<=n2 then T else F) )) s

| ( CL(t, Gte(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Gte(Hole,e2)))::s)
| ( CL(t, Nat(n1)) , (CL (t1,Gte(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Gte(Nat(n1),Hole)))::s )
| ( CL(t, Nat(n2)) , (CL (t1,Gte(Nat(n1),Hole)))::s ) -> krivine (CL (t, (if n1>=n2 then T else F) )) s

| ( CL(t, And(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,And(Hole,e2)))::s)
| ( CL(t, T) , (CL (t1,And(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,And(T,Hole)))::s )
| ( CL(t, F) , (CL (t1,And(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,And(F,Hole)))::s )
| ( CL(t, T) , (CL (t1,And(b1,Hole)))::s ) -> krivine (CL (t, (if (b1=T) then T else F) )) s
| ( CL(t, F) , (CL (t1,And(b1,Hole)))::s ) -> krivine (CL (t, F )) s

| ( CL(t, Or(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Or(Hole,e2)))::s)
| ( CL(t, T) , (CL (t1,Or(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Or(T,Hole)))::s )
| ( CL(t, F) , (CL (t1,Or(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Or(F,Hole)))::s )
| ( CL(t, T) , (CL (t1,Or(b1,Hole)))::s ) -> krivine (CL (t, T )) s
| ( CL(t, F) , (CL (t1,Or(b1,Hole)))::s ) -> krivine (CL (t, (if (b1=T) then T else F) )) s

| ( CL(t, Not(e1) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Not(Hole)))::s)
| ( CL(t, T) , (CL (t1,Not(Hole)))::s ) -> krivine (CL (t, F )) s
| ( CL(t, F) , (CL (t1,Not(Hole)))::s ) -> krivine (CL (t, T )) s

| ( CL(t, Xor(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Xor(Hole,e2)))::s)
| ( CL(t, T) , (CL (t1,Xor(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Xor(T,Hole)))::s )
| ( CL(t, F) , (CL (t1,Xor(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Xor(F,Hole)))::s )
| ( CL(t, T) , (CL (t1,Xor(b1,Hole)))::s ) -> krivine (CL (t, (if (b1=F) then T else F) )) s
| ( CL(t, F) , (CL (t1,Xor(b1,Hole)))::s ) -> krivine (CL (t, (if (b1=T) then T else F) )) s

| ( CL(t, Implies(e1,e2) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Implies(Hole,e2)))::s)
| ( CL(t, T) , (CL (t1,Implies(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Implies(T,Hole)))::s )
| ( CL(t, F) , (CL (t1,Implies(Hole,e2)))::s ) -> krivine (CL (t1,e2)) ( (CL (t,Implies(F,Hole)))::s )
| ( CL(t, T) , (CL (t1,Implies(b1,Hole)))::s ) -> krivine (CL (t, T )) s
| ( CL(t, F) , (CL (t1,Implies(b1,Hole)))::s ) -> krivine (CL (t, (if (b1=F) then F else T) )) s

| ( CL(t, Ite(e1,e2,e3) ) ,s) -> krivine (CL (t,e1)) ((CL (t,Ite(Hole,e2,e3)))::s)
| ( CL(t1, T) , (CL (t,Ite(Hole,e2,e3)))::s ) -> krivine (CL (t,e2)) s
| ( CL(t1, F) , (CL (t,Ite(Hole,e2,e3)))::s ) -> krivine (CL (t,e3)) s

| ( CL(t, Local(v,e1,e2) ) ,s) -> krivine (CL ((v,CL(t,e1))::t,e2) ) ((CL (t,Local(v,Hole,Hole)))::s)
| ( CL(t1, ee2 ) ,(CL (t,Local(v,Hole,Hole)))::s) -> krivine (CL (t,ee2)) s

| ( CL(t,Proj(p,e)) ,s) -> krivine (CL (t,p)) ((CL (t,Proj(Hole,e)))::s)
| ( CL(t1,Nat(n)) ,(CL (t,Proj(Hole,e)))::s) -> krivine (CL (t,e)) ((CL (t,Proj(Nat(n),Hole)))::s)
| ( CL(t1,Tup(l)) ,(CL (t,Proj(Nat(n),Hole)))::s) -> krivine (CL (t, List.nth l n )) s


| ( CL(t,Tup(l)) ,s) -> if (tuple_check l) then ( match s with [] -> (CL (t,Tup(l))) | (CL (t1,Tupev( l1,[Hole] )  ))::s1 -> krivine (CL (t1, Tup(l1@[Tup(l)]) )) s1 
						| ( CL ( t1,Tupev( l1, Hole::e2::l2 ) ) )::s1 -> krivine (CL (t1,e2)) ( (CL (t1,Tupev( l1@[Tup(l)], Hole::l2 )   ))::s1 ) 
					) else
					(
						match l with e1::l1 -> krivine (CL (t,e1)) ( (CL (t, Tupev([],Hole::l1)  ))::s)
					)
| ( CL(t1,ee1) , (CL (t,Tupev( l1,[Hole] )  ))::s ) -> krivine (CL (t, Tup(l1@[ee1]) )) s
| ( CL(t1,ee1) , ( CL ( t,Tupev( l1, Hole::e2::l2 ) ) )::s ) -> krivine (CL (t,e2)) ( (CL (t,Tupev( l1@[ee1], Hole::l2 )   ))::s )

| _ -> raise InvalidFormat
;;

let rec conv l = match l with
| [] -> []
| T::xs -> Tr::(conv xs)
| F::xs -> Fl::(conv xs)
| (Nat(n))::xs -> (N(n))::(conv xs)
| (Tup(l1))::xs -> (Tuple(conv l1))::(conv xs)
;;

let rec unpack c = match c with
| CL(t,T) -> Tr
| CL(t,F) -> Fl
| CL(t,Nat(n) ) -> N n
| CL(t,Tup(l) ) -> Tuple (conv l)
| CL(t,Lambda(v,e)) -> Abstact (Lambda(v,e))
;;


(* testing SECD machine *)

let x = V("a");;
let y = V("b");;
let z = V("c");;
let e1 = E(x);;
let e2 = Lambda(x,e1);;
let e3 = Lambda(y,Plus(E(y),Nat(3)));;
let e4 = Lambda(z,Minus(E(z),Nat(4)));;
let e5 = Lambda(z,Eq(E(z),Nat(4)));;
let e6 = Lambda(z,Tup([Nat(1);Nat(2)]));;
let e7 = Ite(T,e1,e2);;
let e8 = Ite(F,e1,e2);;
let e9 = Call(e4,e7);;
let e10 = Lambda(x,Nat(34));;
let e11 = Tup([Nat(23);Nat(36);e7]);; 
let e12 = Proj(Nat 2,e11);;
let e13 = Local(V("a"),e7,e1);;

let a1 = Plus(Nat 5, Nat (-1));;
let a2 = Minus(Nat 5, Nat 2);;
let a3 = Mul(Nat 4, Nat 2);;
let a4 = Div(Nat 4, Nat 2);;
let a5 = Mod(Nat 4, Nat 2);;
let a6 = Abs(Minus(a1, a2));;
let a7 = Exponent(a1, a4);;
let a8 = Div(a7, a1);;
let a9 = Mul(a1, a2);;
let a10 = Plus(a1, a9);;
let b1 = And(T, F);;
let b2 = Or(T, F);;
let b3 = Xor(b1, b2);;
let b4 = Implies(b2, b3);;
let b5 = Implies(b3, b2);;
let b6 = And(Not(b5), b2);;
let b7 = Not(Or(And(b6, Implies(b3, b2)), T));;
let b8 = Eq(b5, b7);;
let b9 = Gt(a1, a4);;
let b10 = Lt(a4, a8);;
let b11 = Gte(a1, a4);;
let d1 = Lambda(V("x"), Plus(E(V("x")), a1));;
let d2 = Call(d1, a2);;
let f = execute [] [] (compile d2) [];;


let c1 = compile(e1);;
let c2 = compile(e2);;
let c3 = compile(e3);;
let c4 = compile(e4);;
let c5 = compile(e5);;
let c6 = compile(e6);;
let c7 = compile(e7);;
let c8 = compile(e8);;
let c9 = compile(e9);;
let c10 = compile(e10);;
let c11 = compile(e11);;
let c12 = compile(e12);;
let c13 = compile(e13);;


let ca1 = compile(a1);;
let ca2 = compile(a2);;
let ca3 = compile(a3);;
let ca4 = compile(a4);;
let ca5 = compile(a5);;
let ca6 = compile(a6);;
let ca7 = compile(a7);;
let ca8 = compile(a8);;
let ca9 = compile(a9);;
let ca10 = compile(a10);;
let cb1 = compile(b1);;
let cb2 = compile(b2);;
let cb3 = compile(b3);;
let cb4 = compile(b4);;
let cb5 = compile(b5);;
let cb6 = compile(b6);;
let cb7 = compile(b7);;
let cb8 = compile(b8);;
let cb9 = compile(b9);;
let cb10 = compile(b10);;
let cb11 = compile(b11);;
let cd1 = compile(d1);;
let cd2 = compile(d2);;



let z1 = execute [] [(V("a"),N(2))] c1 [];;
let z2 = execute [] [] c2 [];;
let z3 = execute [] [] c3 [];;
let z4 = execute [] [] c4 [];;
let z5 = execute [] [] c5 [];;
let z6 = execute [] [] c6 [];;
let z7 = execute [] [(V("a"),N(2))] c7 [];;
let z8 = execute [] [(V("a"),N(2))] c8 [];;
let z9 = execute [] [(V("a"),N(2))] c9 [];;

let z10 = execute [] [(V("a"),N(2))] c10 [];;
let z11 = execute [] [(V("a"),N(2))] c11 [];;
let z12 = execute [] [(V("a"),N(2))] c12 [];;
let z13 = execute [] [(V("a"),N(2))] c13 [];;


let za1 = execute [] [] ca1 [];;
let za2 = execute [] [] ca2 [];;
let za3 = execute [] [] ca3 [];;
let za4 = execute [] [] ca4 [];;
let za5 = execute [] [] ca5 [];;
let za6 = execute [] [] ca6 [];;
let za7 = execute [] [] ca7 [];;
let za8 = execute [] [] ca8 [];;
let za9 = execute [] [] ca9 [];;
let za10 = execute [] [] ca10 [];;
let zb1 = execute [] [] cb1 [];;
let zb2 = execute [] [] cb2 [];;
let zb3 = execute [] [] cb3 [];;
let zb4 = execute [] [] cb4 [];;
let zb5 = execute [] [] cb5 [];;
let zb6 = execute [] [] cb6 [];;
let zb7 = execute [] [] cb7 [];;
let zb8 = execute [] [] cb8 [];;
let zb9 = execute [] [] cb9 [];;
let zb10 = execute [] [] cb10 [];;
let zb11 = execute [] [] cb11 [];;
let zd1 = execute [] [] cd1 [];;
let zd2 = execute [] [] cd2 [];;



(* testing krivine machine *)

let k1 = krivine (CL ([V("a"),CL([],Nat(2))],e1)) [];;
let k2 = krivine (CL ([],T)) [];;
let k3 = krivine (CL ([],F)) [];;
let k4 = krivine (CL ([],Nat(23))) [];;
let k5 = krivine (CL ([],Plus(Nat(3),Nat(5) ))) [];;
let k6 = krivine (CL ([],Minus(Nat(4),Nat(5) ))) [];;
let k7 = krivine (CL ([],Mul(Nat(3),Nat(7) ))) [];;
let k71 = krivine (CL ([],Div(Nat(30),Nat(7) ))) [];;
let k8 = krivine (CL ([],Eq(Nat(3),Nat(5) ))) [];;
let k9 = krivine (CL ([],Lt(Nat(3),Nat(5) ))) [];;
let k10 = krivine (CL ([],Gt(Nat(3),Nat(5) ))) [];;
let k11 = krivine (CL ([],Ite(Gt(Nat(3),Nat(5) ),Nat(3),Nat(5) ))) [];;

let k12 = krivine (CL ([V("a"),CL ([],Ite(Gt(Nat(3),Nat(5) ),Nat(3),Nat(5) ))],e1)) [];;

let k13 = krivine (CL ([],e2)) [CL([],Call(Hole,Nat 2))];;
let k13a = krivine (CL ([],Call(e2,Nat 2))) [];;


let k14 = krivine (CL ([V("a"),CL([],Nat(2))],e9)) [];;

let k15 = krivine (CL ([V("a"),CL([],Nat(2))],E(V("a")) )) [];;

let k16 = krivine (CL ([V("a"),CL([],E(V("a")) )],Nat(34) )) [];;
let k17 = krivine (CL ([], Tup([Nat(1);Nat(2);Nat(3)]))) [];;

(* let k18b = krivine (CL ([],e10)) [CL([],Minus(E(x),Nat(1)) )];; *)
let k18a = krivine (CL ([],e10)) [];;

(* lazy case - cannot be evaluated by eager evaluation *)
let k18 = krivine (CL ([],Call(e10,Minus(E(x),Nat(1))))) [];;


(* testing for Tup *)

let t1 = Tup([Nat 1;Nat 2;Nat 3;E(V("ab"))]) ;;
let t4 = Tup([E(V("ab"))]);;
let t2 = Tup([Nat 1;Nat 2;Plus(Minus(Nat 1,Nat 3),Nat 10);E(V("ab"));t1]) ;;
let t3 = Tup([t4]);;

let k19 = krivine (CL ([V("ab"),CL([],Nat(2))], t1)) [];;

let k20 = krivine (CL ([V("ab"),CL([],Nat(2))], t3)) [];;


let k21 = krivine (CL ([V("ab"),CL([],Nat(2))], Tup([Nat(10);Nat(20);Nat(30);t1]))) [];;
let k22 = krivine (CL ([V("ab"),CL([],Nat(2))], t2)) [];;

let k23 = krivine (CL ([],Tup([Nat 1;Tup([Nat 2;Nat 3;Tup([Nat 4])])]))) [];;

let t3 = Tup([Nat 1; E(V("a"))]);;
let t4 = Tup([Nat 2; t3]);;

let k24 = krivine (CL ([V("a"),CL([],Nat(5))],t3)) [];;
let k25 = krivine (CL ([V("a"),CL([],Nat(5))],t4)) [];;


 let e = E(V("ab"));;
 krivine (CL ([V("ab"),CL([],Nat(5))], e)) [(CL ([V("ab"),CL([],Nat(5))], Tupev([],[Hole])));(CL ([V("ab"),CL([],Nat(5))], Tupev([],[Hole])))];;
 krivine (CL ([V("ab"),CL([],Nat(5))], e)) [];;

 krivine (CL([],Nat(5))) [(CL ([V("ab"),CL([],Nat(5))], Tupev([],[Hole])));(CL ([V("ab"),CL([],Nat(5))], Tupev([],[Hole])))];;

let k26 = krivine (CL ([V("ab"),CL([],Nat(2))], Proj( Nat 4,t2) )) [];;

let k27 = krivine (CL ([V("ab"),CL([],Nat(2))], Local(V("ab"),Nat 3, E(V("ab"))) )) [];;

let k28 = krivine (CL ([], Lambda(V "x", Plus(E(V "x"),Nat 1) )) ) [];;


let uu1 = unpack k1;;
let uu2 = unpack k2;;
let uu3 = unpack k3;;
let uu4 = unpack k4;;
let uu5 = unpack k5;;
let uu6 = unpack k6;;
let uu7 = unpack k7;;
let uu8 = unpack k8;;
let uu9 = unpack k9;;
let uu10 = unpack k10;;
let uu11 = unpack k11;;
let uu12 = unpack k12;;
let uu13 = unpack k13;;
let uu14 = unpack k14;;
let uu15 = unpack k15;;
let uu16 = unpack k16;;
let uu17 = unpack k17;;
let uu18 = unpack k18;;
let uu19 = unpack k19;;
let uu20 = unpack k20;;
let uu21 = unpack k21;;
let uu22 = unpack k22;;
let uu23 = unpack k23;;
let uu24 = unpack k24;;
let uu25 = unpack k25;;
let uu26 = unpack k26;;
let uu27 = unpack k27;;



let tab1 = [((V "x"),N 2);((V "y"),N 3);((V "a"),Tr);((V "b"),Fl);((V "z"),N 6)];;
let tab2 = [((V "x"),CL ([],Nat 2));((V "y"),CL ([],Nat 3));((V "a"),CL ([],T));((V "b"),CL ([],F));((V "z"),CL ([],Nat 6))];;

let t1 = Abs(Minus(Plus(Nat 1,Div(Nat 2,Nat 1)),Mul(Exponent(Nat 2,E(V "x")),Mod(E(V "y"),Nat 5))));;
let c1 = compile t1;;
let ex1 = execute [] tab1 c1 [];;
let kk1 = krivine (CL (tab2,t1)) [];;
let up1 = unpack kk1;;

let t2 = Not(And(Xor(E(V "a"),E(V "b")),Implies(T,Not(Or(F,F)))));;
let c2 = compile t2;;
let ex2 = execute [] tab1 c2 [];;
let kk2 = krivine (CL (tab2,t2)) [];;
let up2 = unpack kk2;;

let t3 = Eq(Gt(Nat 5,E(V "z")),Lt(Nat 5,E(V "x")));;
let c3 = compile t3;;
let ex3 = execute [] tab1 c3 [];;
let kk3 = krivine (CL (tab2,t3)) [];;
let up3 = unpack kk3;;

let t4 = Eq(Gt(E(V "z"),E(V "x")),Lt(E(V "y"),E(V "y")));;
let c4 = compile t4;;
let ex4 = execute [] tab1 c4 [];;
let kk4 = krivine (CL (tab2,t4)) [];;
let up4 = unpack kk4;;

let t5 = Eq(t1,Nat 13);;
let c5 = compile t5;;
let ex5 = execute [] tab1 c5 [];;
let kk5 = krivine (CL (tab2,t5)) [];;
let up5 = unpack kk5;;

let t6 = Local(V "x",Plus(Nat 2,E(V "x")),E(V "x"));;
let c6 = compile t6;;
let ex6 = execute [] tab1 c6 [];;
let kk6 = krivine (CL (tab2,t6)) [];;
let up6 = unpack kk6;;

let t7 = Ite(t4,t5,t6);;
let c7 = compile t7;;
let ex7 = execute [] tab1 c7 [];;
let kk7 = krivine (CL (tab2,t7)) [];;
let up7 = unpack kk7;;

let t8 = Ite(Not(t4),t5,t6);;
let c8 = compile t8;;
let ex8 = execute [] tab1 c8 [];;
let kk8 = krivine (CL (tab2,t8)) [];;
let up8 = unpack kk8;;

let t9 = Call(Lambda(V "x",Plus(E(V "x"),E(V "y"))),Minus(Nat 10,E(V "x")));;
let c9 = compile t9;;
let ex9 = execute [] tab1 c9 [];;
let kk9 = krivine (CL (tab2,t9)) [];;
let up9 = unpack kk9;;

let t10 = Proj(Nat 1,Tup([Nat 2;Tup([E(V "x");t9;Proj(Nat 0,Tup[t8])])]));;
let c10 = compile t10;;
let ex10 = execute [] tab1 c10 [];;
let kk10 = krivine (CL (tab2,t10)) [];;
let up10 = unpack kk10;;

let t11 = Tup([Nat 2;Tup([E(V "x");t9;Proj(Nat 0,Tup[t8])])]);;
let c11 = compile t11;;
let ex11 = execute [] tab1 c11 [];;
let kk11 = krivine (CL (tab2,t11)) [];;
let up11 = unpack kk11;;

let e111 = Lambda(x,Nat(34));;
execute [] [] (compile (Call(e111,Minus(E(V "a"),Nat(1))))) [];;


let e111 = Lambda(x,Nat(34));;
execute [] [] (compile (Div(Nat(1),Nat(0)))) [];;
let k111 = krivine (CL ([],Call(e111,Div(Nat(1),Nat(0))))) [];;
