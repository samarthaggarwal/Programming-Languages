type variable = Var of string;;
type symbol = Sym of string;;

type term = V of variable | Node of symbol * (term list);;

type signature = (symbol * int) list;;

let rec map f l = match l with
| []->[]
| x::xs -> (f x)::(map f xs)
;;

let rec foldl f l e = match l with
| [] -> e
| x::xs -> foldl f xs (f x e)
;;

(*find returns true if x is present in list l else false *)
let rec find x l = match l with
 []->false
| y::xs -> if y=x then true else find x xs
;;	

(* check_rep returns true if there is no repitition in the list l1. l2 is a helper list that contains the element seen so far.*)
let rec check_rep l1 l2 = match l1 with
| [] -> true
| (x,a)::xs -> if (find x l2) then false else (check_rep xs (x::l2))
;;

(* check_ar returns true if there is negative arity symbol in the list l*)
let rec check_ar l = match l with
| [] -> true
| (x,y)::xs -> if (y<0) then false else check_ar xs
;;

let rec check_sig l = if ((check_rep l []) && (check_ar l)) then true else false;;

exception NotFound;;

(*Given signature l, it returns the arity of symbol x in it*)
let rec arity x l = match l with 
| [] -> raise NotFound
| (y,z)::xs -> if (x=y) then z else (arity x xs)
;;

(*helper function for counting number of elements in a list l*)
let rec count1 l ans = match l with
| [] -> ans
| x::xs -> count1 xs (1+ans)
;;

(*returns the number of elements in list l*)
let count l = count1 l 0;;

let andt a b = a && b;;

let rec wfterm l t = match t with
| V(x) -> true
| Node(s,l1) -> if ( (count l1)!=(arity s l) ) then false else (foldl andt (map (wfterm l) l1) true)
;;

let rec ht t = match t with
| V(x) -> 0
| Node(s,[]) -> 0
| Node(s,l) -> 1+(foldl max (map ht l) 0)
;;

let sum a b = a+b;;

let rec size t = match t with
| V(x) -> 1
| Node(s,[]) -> 1
| Node(s,l) -> 1+(foldl sum (map size l) 0)
;;

(*returns the union of two lists a and b*)
let rec concat a b = match a with
| [] -> b
| x::xs -> if (find x b) then (concat xs b) else (concat xs (x::b));;

(*helper function for listing all the variables in a term t*)
let rec tvars l t = match t with
| V(x) -> if not(find x l) then (x::l) else l
| Node(s,l1) -> foldl concat (map (tvars []) l1) []
;;

(*lists all the variables occuring in term t*)
let vars t = tvars [] t;;

(*helper function for composing two substitutions. It updates substitution s1 by a single element of s2*)
let rec ext s1 (x,y) = match s1 with
| [] -> [(x,y)]
| (p,q)::xs -> if (p=x) then s1 else (if (q=V(x)) then ( if (y=V(p)) then (ext xs (x,y)) else ( (p,y)::(ext xs (x,y)) ) ) else (p,q)::(ext xs (x,y)) )
;;

(*return the composition of two substitutions s1 and s2. First apply s1 then s2*)
let rec compose s1 s2 = match s2 with
| [] -> s1
| (x,y)::xs -> compose (ext s1 (x,y)) xs
;;

(*applies substitution to a single variable x*)
let rec sub x s = match s with
| [] -> V x
| (p,q)::qs -> if (p=x) then q else (sub x qs)
;;

(*Applies substitution s to term t*)
let rec subst s t = match t with
| V(x) -> sub x s
| Node(Sym x,l) -> Node(Sym x,map (subst s) l)
;;


exception NOT_UNIFIABLE;;

(*returns mgu of terms t1 and t2 as a substitution when they are unifiable else raises the exception NOT_UNIFIABLE*)
let rec mgu t1 t2 = match (t1,t2) with
| (V(x),V(y)) -> if (x<>y) then [(x,V y)] else []
| (V(x),t2) -> if (find x (vars t2)) then raise NOT_UNIFIABLE else [(x,t2)]
| (t1,V(x))-> mgu t2 t1
| (Node(s1,[]),Node(s2,[])) -> if (s1<>s2) then raise NOT_UNIFIABLE else []
| (Node(s1,l1::ls1),Node(s2,l2::ls2)) -> if (s1<>s2) then raise NOT_UNIFIABLE else compose (mgu l1 l2) (mgu (subst (mgu l1 l2) (Node (s1,ls1))) (subst (mgu l1 l2) (Node (s2,ls2))))
| _->raise NOT_UNIFIABLE
;;



(* TEST CASES *)

let l = [1;2;3;4;5;6;7;8;9];;
let f x = 2*x;;

map f l;;
find 2 l;;
find 12 l;;

let sign = [(Sym "one",0);(Sym "two",0);(Sym "three",0);(Sym "pl",2);(Sym "neg",1)];;
let sign1 = [(Sym "one",0);(Sym "two",0);(Sym "three",0);(Sym "pl",2);(Sym "neg",-1)];;
let sign2 = [(Sym "one",0);(Sym "two",0);(Sym "three",0);(Sym "pl",2);(Sym "one",3)];;
check_sig sign;;
check_sig sign1;;
check_sig sign2;;
let sign3 = [(Sym "as",2)];;
check_sig sign3;;

let t1 = Node(Sym "pl",[V (Var "as");V (Var "asw")]);;
wfterm sign t1;;
let t2 = Node(Sym "pl",[V (Var "as");Node(Sym "one",[])]);;
wfterm sign t2;;
let t3 = Node(Sym "pl",[V (Var "as");Node(Sym "one",[V (Var "23")])]);;
wfterm sign t3;;
	
size (Node (Sym "one",[]));;
size (V (Var "as"));;
size t1;;
size t2;;
size t3;;

ht t1;;
ht t2;;
ht t3;;
ht (Node (Sym "one",[]));;

vars t1;;
vars t2;;
vars t3;;
vars (Node (Sym "one",[]));;


let sigma1 = [(Var "x",V(Var "y"));(Var "a",V(Var "b"))];;
let sigma2 = [(Var "y",V(Var "z"))];;
let sigma3 = [(Var "z",V(Var "y"))];;
let sigma4 = [(Var "y", Node (Sym "three", []))];;
let sigma5 = [(Var "x", V (Var "y")); (Var "b", V (Var "a"))];;
compose sigma1 sigma2;;
compose sigma2 sigma1;;
compose sigma2 sigma3;;
compose sigma3 sigma2;;
compose sigma5 sigma4;;

let t4 = Node(Sym "pl",[V(Var "x"); Node(Sym "one",[])  ]);;
subst sigma1 t4;;

let t5 = Node(Sym "pl",[V(Var "x"); Node(Sym "pl",[ V(Var "y");V (Var "a")  ])  ]);;
subst sigma1 t5;;
subst sigma4 t5;;
subst (compose sigma5 sigma4) t5;;
subst (compose sigma4 sigma5) t5;;

mgu t1 t2;;
mgu t1 t3;;
mgu t1 t4;;
mgu t2 t4;;
