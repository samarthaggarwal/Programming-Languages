%{
open Ast
%}

%token <string> V
%token <string> Const

%token DOT COMMA HEND EOF
%token LPAREN RPAREN
%token CUT

%start alst
%type <(Ast.at_formula) list> alst

%%

alst: atom COMMA alst 	{ ($1)::($3) }	
	| atom DOT			{ [$1] }

atom: Const LPAREN args RPAREN	{ Atom($1,$3) }
	| Const						{ Atom("Fail",[]) }
	| CUT 						{ Atom("Cut",[]) }


args: args1 COMMA args 	{ ($1)::($3) }
	| args1 			{ [$1] }

args1: Const	{ Fun($1,[]) }
	| V 		{ V($1) }