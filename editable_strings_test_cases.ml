exception Empty;;
exception AtFirst;;
exception AtLast;;
exception TooShort;;

(* let x = ([],[],[],[],[]);;
let y = (['a'],['e'],['b';'a'],['c'],['d';'e']);;
let z = (['p'],['r'],['p'],['q'],['r']);; *)

let rec len l = match l with []->0 | x::xs -> 1 + (len xs);;
let rec lgh (f,l,l1,m,l2) = len (l1@m@l2) ;;

let nonempty (f,e,l,m,r) = match m with []->false | _->true;;

let rec concat (s1,e1,l1,m1,r1) (s2,e2,l2,m2,r2) = match m1 with
| [] -> (s2,e2,l2,m2,r2)
| _ -> (match m2 with
		| [] -> (s1,e1,l1,m1,r1)
		| _ -> (match l2 with
				| [] -> (s1,e2,l1,m1,r1@m2@r2)
				| x::xs -> concat (s1,e1,l1,m1,r1) (s2,e2,xs,[x],m2@r2) ) );;
(*concat is O(1) if one of the string is null and O(n) in the worst case where n=sum of lengths of s1 and s2.
lgh(concat s1 s2) = lgh(l1@m1@r1@l2@m2@r2) = lgh(l1@m1@r1) + lgh(l2@m2@r2) = lgh(s1) + lgh(s2) *)

let reverse (s,e,l,m,r) = (e,s,r,m,l);;
(*complexity is O(1) which is O(n) indeed.
lgh(l@m@r) = lgh(r@m@l) so lgh(reverse s) = lgh(s) *)

let first (s,e,l,m,r) = match s with
| [] -> raise Empty
| [x] -> x;;
(*Complexity = O(1)*)

let last (s,e,l,m,r) = match e with
| [] -> raise Empty
| [x]-> x;;
(*Complexity = O(1)*)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let rec last_element l = match l with
| [x] -> [x]
| x::xs-> last_element xs;;

let create s = match (explode s) with
| []->([],[],[],[],[])
| [x] -> ([x],[x],[],[x],[])
| x::xs -> ([x],(last_element xs),[],[x],xs);;

let forward (s,e,l,m,r) = match r with
| [] -> raise AtLast
| x::xs -> (s,e,m@l,[x],xs);;
(*Complexity = O(1) as the complexity of a@b is O(length of a) and here length of a(=m) is 1*)

let back (s,e,l,m,r) = match l with
| [] -> raise AtFirst
|  x::xs -> (s,e,xs,[x],m@r);;
(*Complexity = O(1) as the complexity of a@b is O(length of a) and here length of a(=m) is 1*)


let rec move n (s,e,l,m,r) = if n=0 then (s,e,l,m,r) else
if n>0 then (match r with
| [] -> raise TooShort
| x::xs -> move (n-1) (s,e,m@l,[x],xs) )
else (match l with
| [] -> raise TooShort
| x::xs -> move (n+1) (s,e,xs,[x],m@r) );;

let moveTo n (s,e,l,m,r) = match m with
| [] -> raise TooShort
| _ -> move (n - (len l)) (s,e,l,m,r);;

(*since l is contained in s so len(l)<=s so len l takes O(n) time. Also the recursive function move is called atmost n times
 with O(1) time for each calling. So it also takes O(n) time. Total time complexity therefore is O(n). *)


let replace (s,e,l,m,r) w = match (l,r) with
| ([],[]) -> ([w],[w],[],[w],[])
| ([],r) -> ([w],e,l,[w],r)
| (l,[]) -> (s,[w],l,[w],r)
| _	->	(s,e,l,[w],r);;
(*Since no element is added or deleted hence the length remains the same.
Since len(m) = len([w]) = 1 so lgh(reverse s) =1 + len(l) + len(r) = lgh(s) *)

let alphabet=["1"; "2"; "a"; "b"; "c"; "A"];;

lgh ([],[],[],[],[]);;
lgh (["a"],["a"],[],["a"],[]);;
lgh (["a"],["c"],[],["a"],["b";"c"]);;
lgh (["1"],["2"],[],["1"],["2"]);;

nonempty ([],[],[],[],[]);;
nonempty (["a"],["a"],[],["a"],[]);;
nonempty (["1"],["2"],[],["1"],["2"]);;

concat ([],[],[],[],[]) ([],[],[],[],[]);;
concat ([],[],[],[],[]) (["a"],["a"],[],["a"],[]);;
concat (["1"],["1"],[],["1"],[]) ([],[],[],[],[]);;
concat (["1"],["A"],[],["1"],["A"]) (["a"],["c"],[],["a"],["b";"c"]);;

reverse ([],[],[],[],[]);;
reverse (["a"],["c"],[],["a"],["b";"c"]);;
reverse (["1"],["2"],[],["1"],["2"]);;

first ([],[],[],[],[]);;
first (["a"],["a"],[],["a"],[]);;
first (["a"],["c"],[],["a"],["b";"c"]);;

last ([],[],[],[],[]);;
last (["a"],["a"],[],["a"],[]);;
last (["a"],["c"],[],["a"],["b";"c"]);;

let editable = create "abac12a2aAac211";;

lgh editable;;
forward editable;;
back editable;;
moveTo 10 editable;;
replace editable 'b';;
