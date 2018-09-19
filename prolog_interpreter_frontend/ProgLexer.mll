{
open ProgParser
}

rule token = parse 
	| [' ' '\t' '\n']	{ token lexbuf }
	| "."				{ DOT }
	| ","				{ COMMA }
	| "("               { LPAREN }
  	| ")"               { RPAREN }
	| [':']['-']		{ HEND }
	| "!"				{ CUT }
	| ['A'-'Z' '_' ]['A'-'Z' 'a'-'z' '0'-'9' '_']*		as var		{ V(var) }
	| ['a'-'z' '0'-'9']['A'-'Z' 'a'-'z' '0'-'9' '_']* as str	{ Const(str) }
	| eof				{ EOF }