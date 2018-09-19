let parse_program str =
	let lb = Lexing.from_string str
	in
		ProgParser.clst ProgLexer.token lb

let parse_query_list str =
	let lb = Lexing.from_string str
	in
		QueryParser.alst QueryLexer.token lb
		
let token_list_of_string_prog s =
	let lb = Lexing.from_string s in
	let rec helper l =
		try
			let t = ProgLexer.token lb in
			if t = ProgParser.EOF then List.rev l else helper (t::l)
		with _ -> List.rev l
	in 
		helper []

let token_list_of_string_queries s =
	let lb = Lexing.from_string s in
	let rec helper l =
		try
			let t = QueryLexer.token lb in
			if t = QueryParser.EOF then List.rev l else helper (t::l)
		with _ -> List.rev l
	in 
		helper []
