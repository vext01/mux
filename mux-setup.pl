main :- consult(setup),
	current_prolog_flag(argv, Argv),
	append(_, [--|[Input]], Argv),
	process_file(Input),	
	halt(1).
