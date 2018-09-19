%{
open Ast
%}

%token <string> V
%token <string> Const

%token DOT COMMA HEND EOF
%token LPAREN RPAREN
%token CUT

%start clst
%type <(Ast.clause) list> clst

%%

clst: cl DOT clst	{ ($1)::($3) }
	| cl DOT		{ [$1] }

cl 	: hd HEND bd	{ Clause($1,B($3)) }
	| hd 			{ Clause($1,B([]))}

hd: Const LPAREN args RPAREN	{ H(Atom($1,$3)) }

bd	: Const LPAREN args RPAREN COMMA bd		{ ( ( Atom($1,$3) )::($6) ) }
	| Const LPAREN args RPAREN				{ ( [Atom($1,$3)] ) }
	| Const COMMA bd						{ ( ( Atom("Fail",[]) )::($3) ) }
	| Const									{ ( [Atom("Fail",[])] ) }
	| CUT COMMA bd							{ ( ( Atom("Cut",[]) )::($3) ) }
	| CUT 									{ ( [Atom("Cut",[])] ) }


args: args1 COMMA args 	{ ($1)::($3) }
	| args1 			{ [$1] }

args1: Const	{ Fun($1,[]) }
	| V 		{ V($1) }