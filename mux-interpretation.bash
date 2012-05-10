#!/usr/bin/swipl -q -g main -f 


main :- consult(setup),	
	consult( interpretation),	
	current_prolog_flag(argv, Argv),
	append(_, [--|[Input]], Argv),
	interpret_result(Input),	
	halt.
