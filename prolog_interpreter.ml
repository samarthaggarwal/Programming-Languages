type term =
| V of string
(* | Const of string *)
| Fun of string*(term list)
;;

type at_formula = Atom of (string * (term list));;

(* type goal = G of (at_formula list);; *)

type head = H of at_formula;;
type body = B of (at_formula list);;
type clause = Clause of head * body;;

(* type program = P of (clause list);; *)


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

(*returns the union of two lists a and b*)
let rec concat a b = match a with
| [] -> b
| x::xs -> if (find x b) then (concat xs b) else (concat xs (x::b));;

(*helper function for listing all the variables in a term t*)
let rec tvars l t = match t with
| V(x) -> if not(find x l) then (x::l) else l
| Fun(s,l1) -> foldl concat (map (tvars []) l1) []
;;

(*lists all the variables occuring in term t*)
let vars t = tvars [] t;;

(*lists all the variables occuring in at_formula t*)
let at_vars t = match t with Atom(s,l1) -> vars (Fun(s,l1));;

let rec at_vars_list lt = match lt with
| []-> []
| Atom(s,l1)::ls -> concat (vars (Fun(s,l1))) (at_vars_list ls)
;;

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
| Fun(str,l) -> Fun(str,map (subst s) l)
(* | Atom(str,l) -> Atom(str,map (subst s) l) *)
;;

(*Applies substitution s to at_formula t*)
let at_subst s t = match t with Atom(str,l) -> Atom(str,map (subst s) l)
;;


(* no need to add Const(n) -> Const(n) in subst *)

exception NOT_UNIFIABLE;;

(*returns mgu of terms t1 and t2 as a substitution when they are unifiable else raises the exception NOT_UNIFIABLE*)
let rec mgu t1 t2 = match (t1,t2) with
| (V(x),V(y)) -> if (x<>y) then [(x,V y)] else []
(* | (V(x),Const(n)) -> [(x,Const n)] *)
| (V(x),t2) -> if (find x (vars t2)) then raise NOT_UNIFIABLE else [(x,t2)]
| (t1,V(x))-> mgu t2 t1

| (Fun(s1,[]),Fun(s2,[])) -> if (s1<>s2) then raise NOT_UNIFIABLE else []
| (Fun(s1,l1::ls1),Fun(s2,l2::ls2)) -> if (s1<>s2) then raise NOT_UNIFIABLE else compose (mgu l1 l2) (mgu (subst (mgu l1 l2) (Fun (s1,ls1))) (subst (mgu l1 l2) (Fun (s2,ls2))))
| _->raise NOT_UNIFIABLE
;;



(* let rec lmgu l1 l2 = match (l1,l2) with
| ([],[]) -> []
| (t1::ts1,t2::ts2) -> compose (mgu t1 t2) (mgu (subst (mgu t1 t2) (Fun (s1,ls1))) (subst (mgu l1 l2) (Fun (s2,ls2))))
| _ -> raise NOT_UNIFIABLE
;;
 *)

(* returns mgu of at_formulae a1 and a2 as a substitution when they are unifiable else raises the exception NOT_UNIFIABLE *)
let rec unif a1 a2 = match (a1,a2) with
| ( Atom(s1,[]),Atom(s2,[]) ) -> if (s1<>s2) then raise NOT_UNIFIABLE else []
| ( Atom(s1,(l1::ls1)),Atom(s2,(l2::ls2)) ) -> if (s1<>s2) then raise NOT_UNIFIABLE else compose (mgu l1 l2) (unif (at_subst (mgu l1 l2) (Atom(s1,ls1))) (at_subst (mgu l1 l2) (Atom(s2,ls2))))
| _ -> raise NOT_UNIFIABLE
;;

(*
let a1 = Atom("path", [Fun("a",[]);Fun("h",[])] );;
let a2 = Atom("edge", [Fun("a",[]);Fun("b",[])] );;
let a3 = Atom("path", [V("x");V("Y")] );;

unif a1 a3;;

unif (Atom ("path", [V("x");V("Y")] )) (Atom ("path", [Fun("a",[]);Fun("h",[])] ));;
unif (Atom ("path", [V("x")] )) (Atom ("path", [Fun("a",[])] ));;
*)

let rec reverse l = match l with
| [] -> []
| x::xs -> (reverse xs)@[x]
;;

let rec compress l = match l with
| [] -> []
| [x] -> x
| x::y::xs -> compress ((compose x y)::xs)
;;


type ans = True | False | Ans of ( ( (string * term) list ) list );;

(* applies list of substitutions t to at_formula a *)
let rec at_subst_list t a = match t with
| [] -> a
| x::xs -> at_subst_list xs (at_subst x a)
;;

(* returns list of only those variables that are present in vl *)
let rec clean t vl = match t with
| [] -> []
| (v,m)::xs -> if (find v vl) then ((v,m)::(clean xs vl)) else (clean xs vl)
;;

(* helper function for norep. l2 is l1 without any repetitions. initialise l2 as [] *)
let rec tnorep l1 l2 = match l1 with
| [] -> l2
| x::xs -> if not(find x l2) then (tnorep xs (x::l2)) else (tnorep xs l2)
;;

(* removes all repitions from l *)
let norep l = tnorep l [];;

(* helper function for reporder. l2 is l1 without any repetitions. initialise l2 as [] *)
let rec treporder l1 l2 = match l1 with
| [] -> l2
| x::xs -> if not(find x l2) then (treporder xs (l2@[x])) else (treporder xs l2)
;;

(* removes all repitions from l preserving the order*)
let reporder l = treporder l [];;

let rec cutdump d = match d with
| [] -> []
| ([Atom("Mark",[])],[],[])::ds -> ds
| d1::ds -> cutdump ds
;;

let rec exec g t d ls lp p v = match (g,t,d,ls,lp,p,v) with
| (g1::gs,[],[],ls,[],p,v) -> ( match ls with ([])::xs -> True | [] -> False | _ -> Ans(norep ls) )
| (g1::gs,t,(gs1,t1,ps1)::d,ls,[],p,v) -> exec gs1 t1 d ls ps1 p v
| ([],t,(gs1,t1,ps1)::d,ls,ps,p,v) -> exec gs1 t1 d ((compress (reverse t))::ls) ps1 p v
| ([],t,[],ls,lp,p,v) -> (let w=((compress (reverse t))::ls) in (match w with ([])::xs -> True | [] -> False | _ -> Ans(norep w) )  )

| ((Atom( "Cut" ,[]))::gs,t,d,ls,p1::ps,p,v) -> (exec gs t (cutdump d) ls p p v)
| ((Atom( "Fail" ,[]))::gs,t,(gs1,t1,ps1)::d,ls,lp,p,v) -> exec gs1 t1 d ls ps1 p v

| (g1::gs,t,d,ls,p1::ps,p,v) -> ( try
                                    (match p1 with
                                    | Clause(H(h),B(b)) -> let t1 = ( ( unif (h) (g1) ) ) in ( if (find (Atom("Cut",[])) b) then
                                                                                  (exec (reporder (map (at_subst t1) (b@gs))) ((clean t1 v)::t) ((g,t,ps)::([Atom("Mark",[])],[],[])::d) ls p p v)
                                                                                  else
                                                                                  (exec (reporder (map (at_subst t1) (b@gs))) ((clean t1 v)::t) ((g,t,ps)::d) ls p p v)
                                                                                )
                            )
                    with NOT_UNIFIABLE -> exec g t d ls ps p v
            )
;;

(* main function to be given list of goals and list of program clauses *)
let execute g p = exec g [] [] [] p p (at_vars_list g);;


(* TEST CASES *)
(* 
let p1 = Clause(H(Atom("edge", [Fun("a",[]);Fun("b",[])] )), B([]));;
let p2 = Clause(H(Atom("edge", [Fun("a",[]);Fun("c",[])] )), B([]));;
let p3 = Clause(H(Atom("edge", [Fun("b",[]);Fun("d",[])] )), B([]));;
let p4 = Clause(H(Atom("edge", [Fun("b",[]);Fun("e",[])] )), B([]));;
let p5 = Clause(H(Atom("edge", [Fun("c",[]);Fun("e",[])] )), B([]));;
let p6 = Clause(H(Atom("edge", [Fun("c",[]);Fun("f",[])] )), B([]));;
let p7 = Clause(H(Atom("edge", [Fun("e",[]);Fun("g",[])] )), B([]));;
let p8 = Clause(H(Atom("edge", [Fun("f",[]);Fun("h",[])] )), B([]));;
let p9 = Clause(H(Atom("edge", [Fun("i",[]);Fun("c",[])] )), B([]));;
let p10 = Clause(H(Atom("path", [V "X";V "X"] )), B([]));;
let p11 = Clause(H(Atom("path", [V("X");V("Y")] )), B([  Atom("edge", [V("X");V("Z")] )  ;  Atom("path", [V("Z");V("Y")] )  ]));;

let prog = [p1;p2;p3;p4;p5;p6;p7;p8;p9;p10;p11];;


let e3 = exec [Atom("path", [Fun("a",[]);Fun("h",[])] )] [] [] [] prog prog (at_vars (Atom("path", [Fun("a",[]);Fun("h",[])] )));;
let e3 = execute [Atom("path", [Fun("a",[]);Fun("h",[])] )] prog;;


let x = Atom("edge", [Fun("a",[]);Fun("b",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("edge", [Fun("a",[]);Fun("c",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("edge", [Fun("b",[]);Fun("c",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("edge", [Fun("b",[]);Fun("d",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("edge", [Fun("c",[]);Fun("i",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("edge", [Fun("b",[]);Fun("g",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("edge", [Fun("a",[]);Fun("h",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("a",[]);Fun("b",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("a",[]);Fun("c",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("b",[]);Fun("c",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("b",[]);Fun("d",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("c",[]);Fun("i",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("b",[]);Fun("g",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("a",[]);Fun("h",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("e",[]);Fun("h",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("i",[]);Fun("g",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("b",[]);Fun("h",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("i",[]);Fun("e",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("edge", [Fun("c",[]);V "S"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("edge", [V "S";Fun("c",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("e",[]);V "S"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("f",[]);V "S"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("c",[]);V "S"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("b",[]);V "S"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("a",[]);V "S"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [Fun("i",[]);V "S"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [V "S";Fun("e",[])] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;


let x = Atom("edge", [V "S";V "R"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [V "S";V "R"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;

let x = Atom("path", [V "X";V "Y"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;


let c1 = Clause(H(Atom("g", [Fun("1",[])] )), B([]));;
let c2 = Clause(H(Atom("g", [Fun("2",[])] )), B([]));;
let c3 = Clause(H(Atom("f", [V "X"] )), B([Atom("g", [V "X"] ) ; Atom("Cut", [])]));;

let progc = [c1;c2;c3];;

let x = Atom("g", [Fun("1",[])] );;
let e31 = exec [x] [] [] [] progc progc (at_vars x);;
let e31 = execute [x] progc;;

let x = Atom("g", [Fun("2",[])] );;
let e31 = exec [x] [] [] [] progc progc (at_vars x);;
let e31 = execute [x] progc;;

let x = Atom("g", [Fun("3",[])] );;
let e31 = exec [x] [] [] [] progc progc (at_vars x);;
let e31 = execute [x] progc;;

let x = Atom("f", [Fun("1",[])] );;
let e31 = exec [x] [] [] [] progc progc (at_vars x);;
let e31 = execute [x] progc;;

let x = Atom("f", [Fun("2",[])] );;
let e31 = exec [x] [] [] [] progc progc (at_vars x);;
let e31 = execute [x] progc;;

let x = Atom("f", [Fun("3",[])] );;
let e31 = exec [x] [] [] [] progc progc (at_vars x);;
let e31 = execute [x] progc;;

let x = Atom("g", [V "X"] );;
let e31 = exec [x] [] [] [] progc progc (at_vars x);;
let e31 = execute [x] progc;;

let x = Atom("f", [V "X"] );;
let e31 = exec [x] [] [] [] progc progc (at_vars x);;
let e31 = execute [x] progc;;

let x = Atom("g", [V "X"] );;
let y = Atom("f", [V "X"] );;
let e31 = exec [x;y] [] [] [] progc progc (at_vars x);;
let e31 = execute [x;y] progc;;

let x = Atom("f", [V "X"] );;
let y = Atom("g", [V "X"] );;
(* #trace exec;; *)
let e31 = exec [x;y] [] [] [] progc progc (at_vars x);;
let e31 = execute [x;y] progc;;


let p1 = Clause(H(Atom("edge", [Fun("a",[]);Fun("b",[])] )), B([]));;
let p2 = Clause(H(Atom("edge", [Fun("b",[]);Fun("c",[])] )), B([]));;
let p3 = Clause(H(Atom("edge", [Fun("c",[]);Fun("d",[])] )), B([]));;
let p4 = Clause(H(Atom("edge", [Fun("c",[]);Fun("e",[])] )), B([]));;
let p10 = Clause(H(Atom("path", [V "x";V "x"] )), B([]));;
let p11 = Clause(H(Atom("path", [V("X");V("Y")] )), B([  Atom("edge", [V("X");V("Z")] )  ;  Atom("path", [V("Z");V("Y")] ) ; Atom("Cut", [] ) ]));;

let prog = [p1;p2;p3;p4;p10;p11];;
let x = Atom("path", [V "S";V "R"] );;
let e31 = exec [x] [] [] [] prog prog (at_vars x);;
let e31 = execute [x] prog;;
 *)
(* 
let p1 = Clause(H(Atom("edge", [Fun("a",[]);Fun("b",[])] )), B([]));;
let p2 = Clause(H(Atom("edge", [Fun("a",[]);Fun("c",[])] )), B([]));;
let p3 = Clause(H(Atom("edge", [Fun("b",[]);Fun("d",[])] )), B([]));;
let p4 = Clause(H(Atom("edge", [Fun("b",[]);Fun("e",[])] )), B([]));;
let p5 = Clause(H(Atom("edge", [Fun("c",[]);Fun("e",[])] )), B([]));;
let p6 = Clause(H(Atom("edge", [Fun("c",[]);Fun("f",[])] )), B([]));;
let p7 = Clause(H(Atom("edge", [Fun("e",[]);Fun("g",[])] )), B([]));;
let p8 = Clause(H(Atom("edge", [Fun("f",[]);Fun("h",[])] )), B([]));;
let p9 = Clause(H(Atom("edge", [Fun("i",[]);Fun("c",[])] )), B([]));;
let p10 = Clause(H(Atom("path", [V "X";V "X"] )), B([]));;
let p11 = Clause(H(Atom("path", [V("X");V("Y")] )), B([  Atom("edge", [V("X");V("Z")] )  ;  Atom("path", [V("Z");V("Y")] )  ]));;

let prog = [p1;p2;p3;p4;p5;p6;p7;p8;p9;p10;p11];;

let e = execute [Atom("Cut",[])] prog;; *)