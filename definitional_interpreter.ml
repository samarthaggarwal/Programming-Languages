type exp =
	  Const of int
	| Var of string
	| Abs of exp
	| Neg of exp
	| Plus of exp * exp
	| Minus of exp * exp
	| Mul of exp * exp
	| Div of exp * exp
	| Mod of exp * exp
	| Exponent of exp * exp
	| T
	| F
	| Not of exp
	| And of exp * exp
	| Or of exp * exp
	| Implies of exp * exp
	| Eq of exp * exp
	| Lt of exp * exp
	| Gt of exp * exp
	| Lte of exp * exp
	| Gte of exp * exp
	| Tuple of exp list
	| Proj of exp * exp
;;

type answer =
	  Val of int
	| D of bool
	| Tup of answer list
;;

exception Error;;

let rho x = match x with
	  "x" -> Val(2)
	| "z" -> D(true)
	| _-> Val(5)
;;

let e1 = Var("x");;

let plus a b = match (a,b) with (Val(n1),Val(n2)) -> Val(n1+n2);;
let minus a b = match (a,b) with (Val(n1),Val(n2)) -> Val(n1-n2);;
let mul a b = match (a,b) with (Val(n1),Val(n2)) -> Val(n1*n2);;
let div a b = match (a,b) with (Val(n1),Val(n2)) -> Val(n1/n2);;
let rem a b = match (a,b) with (Val(n1),Val(n2)) -> Val(n1 mod n2);;
let rec power a b ans = match b with
	| 0 -> ans
	| _-> power a (b-1) (ans*a)
;;
let exponent a b = match (a,b) with (Val(n1),Val(n2)) -> Val(power n1 n2 1);;

let neg a = match a with Val(n) -> Val(-1*n);;
let abs a = match a with Val(n) -> if n>=0 then Val(n) else Val(-1*n);;

let notb a = match a with D(b) -> D(not b);;
let andb a b = match (a,b) with (D(b1),D(b2)) -> D(b1 && b2);;
let orb a b = match (a,b) with (D(b1),D(b2)) -> D(b1 || b2);;
let impliesb a b = match (a,b) with (D(b1),D(b2)) -> D((not b1) || b2);;

let eq a b = match (a,b) with (Val(n1),Val(n2)) -> D(n1==n2);; (*comparison operators are defined only for integer expressions*)
let lt a b = match (a,b) with (Val(n1),Val(n2)) -> D(n1<n2);;
let gt a b = match (a,b) with (Val(n1),Val(n2)) -> D(n1>n2);;
let lte a b = match (a,b) with (Val(n1),Val(n2)) -> D(n1<=n2);;
let gte a b = match (a,b) with (Val(n1),Val(n2)) -> D(n1>=n2);;

let rec proj i l = match (i,l) with
		(Val(1),x::xs) -> x
	| (Val(n),x::xs) -> proj (Val (n-1)) xs
;;

let rec map f l = match l with
		[]->[]
	| x::xs -> (f x)::(map f xs)
;;

let rec eval rho e = match e with
	  Const(n) -> Val(n)
	| Var(x) -> rho x
	| Plus(e1,e2) -> plus (eval rho e1) (eval rho e2)
	| Minus(e1,e2) -> minus (eval rho e1) (eval rho e2)
	| Mul(e1,e2) -> mul (eval rho e1) (eval rho e2)
	| Div(e1,e2) -> div (eval rho e1) (eval rho e2)
	| Mod(e1,e2) -> rem (eval rho e1) (eval rho e2)
	| Exponent(e1,e2) -> exponent (eval rho e1) (eval rho e2)
	| Neg(e) ->  neg (eval rho e)
	| Abs(e) -> abs (eval rho e)
	| T -> D(true)
	| F -> D(false)
	| Not(e) -> notb (eval rho e)
	| And(e1,e2) -> andb (eval rho e1) (eval rho e2)
	| Or(e1,e2) -> orb (eval rho e1) (eval rho e2)
	| Implies(e1,e2) -> impliesb (eval rho e1) (eval rho e2)
	| Eq(e1,e2) -> eq (eval rho e1) (eval rho e2)
	| Lt(e1,e2) -> lt (eval rho e1) (eval rho e2)
	| Gt(e1,e2) -> gt (eval rho e1) (eval rho e2)
	| Lte(e1,e2) -> lte (eval rho e1) (eval rho e2)
	| Gte(e1,e2) -> gte (eval rho e1) (eval rho e2)
	| Tuple(l) -> Tup(map (eval rho) l)
	| Proj(i,l) -> match l with Tuple(l1) -> eval rho (proj (eval rho i) l1)
	| _->raise Error
;;

type opcode =
		CONST of int
	| 	LOOKUP of string
	| 	PLUS
	| 	MINUS
	| 	MUL
	| 	DIV
	| 	MOD
	| 	EXPONENT
	| 	NEG
	| 	ABS
	| 	TRUE
	| 	FALSE
	| 	NOT
	| 	AND
	| 	OR
	| 	IMPLIES
	| 	EQ
	| 	LT
	| 	GT
	| 	LTE
	| 	GTE
	| 	CT of opcode list list
	| 	PROJ
;;

let rec compile e = match e with
 		Const(n) -> [CONST(n)]
 	|	Var(x) -> [LOOKUP(x)]
 	|	Plus(e1,e2) -> (compile e1)@(compile e2)@[PLUS]
 	| 	Minus(e1,e2) -> (compile e1)@(compile e2)@[MINUS]
 	| 	Mul(e1,e2) -> (compile e1)@(compile e2)@[MUL]
 	| 	Div(e1,e2) -> (compile e1)@(compile e2)@[DIV]
 	| 	Mod(e1,e2) -> (compile e1)@(compile e2)@[MOD]
 	| 	Exponent(e1,e2) -> (compile e1)@(compile e2)@[EXPONENT]
 	| 	Neg(e1) -> (compile e1)@[NEG]
 	| 	Abs(e1) -> (compile e1)@[ABS]
 	| 	T -> [TRUE]
 	| 	F -> [FALSE]
 	| 	Not(e1) -> (compile e1)@[NOT]
 	| 	And(e1,e2) -> (compile e1)@(compile e2)@[AND]
 	| 	Or(e1,e2) -> (compile e1)@(compile e2)@[OR]
 	| 	Implies(e1,e2) -> (compile e1)@(compile e2)@[IMPLIES]
 	| 	Eq(e1,e2) -> (compile e1)@(compile e2)@[EQ]
 	| 	Lt(e1,e2) -> (compile e1)@(compile e2)@[LT]
 	| 	Gt(e1,e2) -> (compile e1)@(compile e2)@[GT]
 	| 	Lte(e1,e2) -> (compile e1)@(compile e2)@[LTE]
 	| 	Gte(e1,e2) -> (compile e1)@(compile e2)@[GTE]
 	| 	Tuple(l) -> [CT(map compile l)]
 	| 	Proj(i,l) -> (compile i)@(compile l)@[PROJ]
;;

let rec execute (s,t,l) = match (s,t,l) with
		(x::xs,t,[]) -> x
	| 	(s,t,CONST(n)::l1) -> execute (Val(n)::s,t,l1)
	| 	(s,t,LOOKUP(n)::l1) -> execute ((t n)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,PLUS::l1) -> execute (Val(n1+n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,MINUS::l1) -> execute (Val(n1-n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,MUL::l1) -> execute (Val(n1*n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,DIV::l1) -> execute (Val(n1/n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,MOD::l1) -> execute (Val(n1 mod n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,EXPONENT::l1) -> execute (Val(power n1 n2 1)::s,t,l1)	
	| 	(Val(n)::s,t,NEG::l1) -> execute (Val(-1*n)::s,t,l1)
	| 	(Val(n)::s,t,ABS::l1) -> execute (Val(if n>=0 then n else -1*n)::s,t,l1)	
	| 	(s,t,TRUE::l1) -> execute (D(true)::s,t,l1)
	| 	(s,t,FALSE::l1) -> execute (D(false)::s,t,l1)
	| 	(D(b)::s,t,NOT::l1) -> execute (D(not b)::s,t,l1)
	| 	(D(b2)::D(b1)::s,t,AND::l1) -> execute (D(b1 && b2)::s,t,l1)
	| 	(D(b2)::D(b1)::s,t,OR::l1) -> execute (D(b1 || b2)::s,t,l1)
	| 	(D(b2)::D(b1)::s,t,IMPLIES::l1) -> execute (D((not b1) || b2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,EQ::l1) -> execute (D(n1=n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,LT::l1) -> execute (D(n1<n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,GT::l1) -> execute (D(n1>n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,LTE::l1) -> execute (D(n1<=n2)::s,t,l1)
	| 	(Val(n2)::Val(n1)::s,t,GTE::l1) -> execute (D(n1>=n2)::s,t,l1)
	| 	(s,t,CT(l)::l1) -> let rec texec (t,l) = match l with []->[] | x::xs -> [execute ([],t,x)]@(texec (t,xs)) in execute ((Tup (texec (t,l)))::s,t,l1)
	| 	(ll::i::s,t,PROJ::l1) -> match ll with Tup(ll1) -> execute ((proj i ll1)::s,t,l1)
;;


(* EXAMLPLES AND TEST CASES *)

let x1 = Const 4;;
let x2 = Plus(Const 5, Var "y");;
let x3 = Minus(Plus(Var "x",Var "y"),Const 8);;
let x4 = Abs(Const (-12));;
let x5 = Mul(Var "x",Const 50);;
let x6 = Div(Const 12, Var "y");;
let x7 = Mod(Var "x", Var "y");;
let x8 = Exponent(Var "y",Const 4);;
let x9 = Not(Var "z");;
let x10 = Implies(And(Not(T),T),Or(F,F));;
let x11 = Eq(Minus(Var "x",Var "y"),Const 2);;
let x12 = Gt(Const 5, Var "y");;
let x13 = Lt(Const 5, Var "y");;
let x14 = Lte(Const 5, Var "x");;
let x15 = Gte(Const 5, Var "x");;
let x16 = Tuple([Var "x";Const 10; Var "z"; T]);;
let x17 = Proj(Var "x",x16);;
let x18 = Tuple([Const 10;Plus(Const 2,Const 3);Div(Const 9,Const 4)]);;
let x19 = Tuple([x18;x18;x18]);;
let y1 = compile x1;;
let y2 = compile x2;;
let y3 = compile x3;;
let y4 = compile x4;;
let y5 = compile x5;;
let y6 = compile x6;;
let y7 = compile x7;;
let y8 = compile x8;;
let y9 = compile x9;;
let y10 = compile x10;;
let y11 = compile x11;;
let y12 = compile x12;;
let y13 = compile x13;;
let y14 = compile x14;;
let y15 = compile x15;;
let y16 = compile x16;;
let y17 = compile x17;;
let y18 = compile x18;;
let y19 = compile x19;;
let w1 = eval rho x1;;
let z1 = execute([],rho,y1);;
let w2 = eval rho x2;;
let z2 = execute([],rho,y2);;
let w3 = eval rho x3;;
let z3 = execute([],rho,y3);;
let w4 = eval rho x4;;
let z4 = execute([],rho,y4);;
let w5 = eval rho x5;;
let z5 = execute([],rho,y5);;
let w6 = eval rho x6;;
let z6 = execute([],rho,y6);;
let w7 = eval rho x7;;
let z7 = execute([],rho,y7);;
let w8 = eval rho x8;;
let z8 = execute([],rho,y8);;
let w9 = eval rho x9;;
let z9 = execute([],rho,y9);;
let w10 = eval rho x10;;
let z10 = execute([],rho,y10);;
let w11 = eval rho x11;;
let z11 = execute([],rho,y11);;
let w12 = eval rho x12;;
let z12 = execute([],rho,y12);;
let w13 = eval rho x13;;
let z13 = execute([],rho,y13);;
let w14 = eval rho x14;;
let z14 = execute([],rho,y14);;
let w15 = eval rho x15;;
let z15 = execute([],rho,y15);;
let w16 = eval rho x16;;
let z16 = execute([],rho,y16);;
let w17 = eval rho x17;;
let z17 = execute([],rho,y17);;
let w18 = eval rho x18;;
let z18 = execute([],rho,y18);;
let w19 = eval rho x19;;
let z19 = execute([],rho,y19);;
