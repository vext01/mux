use_module( library(lists)).
use_module( library(gensym)).
% ======== MAIN =========== %
% ------------------------- %

process_file( InFile) :-
    see(InFile),
% Andys analyser puts two newlines at the beginning of all files, hence the commented line below
%    skip_past('\n'),  skip_past('\n'),
    get_all_clauses( Cs),
    seen,
    sort_clauses_into_preds( Cs, Ps),
    process_all(Ps).


process_all( []).
process_all( [P | Ps]) :-
    write_pred_file(P),
    process_all(Ps).


write_pred_file( P) :-
    P = [C | _],
    get_head( C, H),
    extract_pred_id( H, PI), 
    atom_codes( X, PI),
    gensym( X, Out),
% creating .ine file
    atom_concat( Out, '.ine', IneFile),
    process_predicate( P, Mout, Bout, D1, D2),
    build_output( X, D1, D2, String),
    NoVs is (D1 - 1),
    build_non_neg_lines( NoVs, Nnl),
    tell(IneFile),
    put_list(String),
    put_matrix( Mout),
    put_matrix( Bout),
    put_matrix( Nnl),
    put_list("end"),
    told,
% creating .constraints file
	atom_concat( Out, '.constraints', ConsFile),
	get_constraint_list(P, Cl),
	get_lengths( Cl, Lengths),
	append( Cl, Constraints),
	flatten( Cl, FlatConstraints),
	extract_vars( FlatConstraints, Varsl),
	list_to_set( Varsl, Vars),
	tell( ConsFile), 
	put_constraint_line( Constraints),
	put('\n'),	
	put_constraint_line( Lengths),
	put('\n'),
	put_list( Vars),
	told.
    
% get_lengths( Cl, Ls) 
% takes a list of lists (#1), returns a 
% list of their lengths
get_lengths( [], []).
get_lengths( [C | Cs], [L | Ls]) :-
	length(C, Ltemp),
	number_codes( Ltemp, L), 
	get_lengths( Cs, Ls).



% get_constraint_list(P, Cs)
% constructs a list of the constraints in the clauses of #1
% in the order that they are encountered
% needed to calculate tuples of gris later...
get_constraint_list( [], []).
get_constraint_list( [C1 | Cs], [L1 | Ls]) :-
	get_body( C1, B),
	split_body( B, Ltemp),
	substitute_eq_by_leq( Ltemp, L1), 
	get_constraint_list( Cs, Ls).
	

% substitute_eq_by_leq( Cs, Csnew)
% substitutes '='-constraints by two '=<'-constraints 
% in the list of constraints #1, preserving the order !
substitute_eq_by_leq( [], []).
substitute_eq_by_leq( [C | Cs], Csnew) :-
    	substitute_eq_by_leq( Cs, Cstemp),
	nth1( P, C, '='),
    	!,    % because 'nth1'\3 is used in non-det mode...
    	Pl is (P - 1),
    	Pr is (P + 1),
(  	nth1( Pr, C, '<'),
	Csnew = [C | Cstemp]
;
	\+ nth1(Pr, C, '<'),
    	take(Pl, C, Left),
    	drop(P, C, Right),
	flatten( [Left, ['=','<'], Right], C1),
	flatten( [Right, ['=','<'], Left], C2),
	Csnew = [C1, C2 | Cstemp]	
).




build_output( X, D1, D2, String) :-
    atom_codes( X, Name),
    append( Name, "\n * automatically written .ine file \n H-representation \n begin \n", S1),
    atom_codes( D1, E1),
    atom_codes( D2, E2),
    append( E2, [' '|E1], S2),
    append( S2, " rational\n", S3),
    append( S1, S3, String).


process_predicate( P, Mout, Bout, D1, D2) :-
    build_matrices_from_pred( P, M, B),
% processing and writing out P
    matrix_codes_to_atoms( M, Matoms),
    transpose( Matoms, Mtrans),
% getting dimension in between
    Mtrans = [ X | _],
    length( X, L1),
    D1 is ( L1 + 1),
    length( Mtrans, L2),
    D2 is ( L2 + D1),
    matrix_atoms_to_codes( Mtrans, Malmost),
    add_to_all_lines(  Malmost, ['0', ' ', ' '], Mout),
% processing and writing out B
    matrix_codes_to_atoms( B, Batoms),
    transpose( Batoms, Btrans),
    matrix_atoms_to_codes( Btrans, Btemp),
% next line commented because 'get_constant'\3 flips the constant sign as needed
%    matrix_flip_signs( Btemp, Balmost),
    add_to_all_lines( Btemp,  ['-', '1', ' ', ' '], Bout).




build_matrices_from_pred( [], [], []).
build_matrices_from_pred( [C | Cs],  M,  B) :-
    process_clause( C, M1, B1), 
    build_matrices_from_pred( Cs, Ms, Bs),
    append( M1, Ms, M),
    append( B1, Bs, B).


process_clause( C, Mmatrix, Bmatrix) :-
    get_head(C, H),
    extract_head_vars(H, HVs),
    get_body( C, B),
    split_body( B, Ls),
    process_constraints( Ls, HVs, Mmatrix, Bmatrix).
    
    

% process_constraints( Cs, Vs, M, B)
% sets #3 and #4 to the results of appending 
% the results of process_constraint for each element of #1
process_constraints( [], _, [], []).
process_constraints( [C | Cs], Vs, Mm, Bm ) :-
    process_constraint( Vs, C, M, B),
    process_constraints( Cs, Vs, Ms, Bs),
% need to calls to append here, because if the current constraint is an "="-constraint, we get two lines in the final matrix...  
    append( M, Ms, Mm),
    append( B, Bs, Bm).


% process_constraint( Vs, C, M, B)
% returns in #3 and #4 the matrices resulting from #2 
% over the sorted list of variables #1
process_constraint( Vs, C, M, B ) :-
    nth1( P, C, '='),
    !,    % because 'nth1'\3 is used in non-det mode...
    Pl is (P - 1),
    Pr is (P + 1),
(  nth1( Pr, C, '<'),
    take( Pl, C, Left),
    drop( Pr, C, Right),
    process_leq_constraint( Vs, Left, Right, M, B)
;
   \+ nth1(Pr, C, '<'),
    take(Pl, C, Left),
    drop(P, C, Right),
    process_eq_constraint( Vs, Left, Right, M, B)
).

% processes an "=<"-constraint,
% returns a singleton list, because process_constraints combines lists using 'append'\3
process_leq_constraint(Vs, Left, Right, [M], [Const]) :-
    get_coefficients( Vs, Left, Right, Coeffs),
    coefficients_to_codes( Coeffs, M),
    get_constant( Left, Right, Const).


% processes an "="-constraint by calling 
% process_leq_constraint twice, switching Left and Right the second time
process_eq_constraint(Vs, Left, Right, M, B) :-
	process_leq_constraint(Vs, Left, Right, M1, B1),
	process_leq_constraint(Vs, Right, Left, M2, B2),
% need 'append'\3 here, because 'process_leq_constraint'\4 returns two singleton lists...
	append( M1, M2, M),
	append( B1, B2, B).


transpose( [], []).
transpose( [L | M], Mnew) :-
    length(L, I),
    transpose( I, [L | M], M1),
    reverse( M1, Mnew).

% transpose( I, M, Mnew)
% sets #3 to the result of transposing the matrix in #2
% where a matrix is represented as a list of lists of length #1
transpose( 0, _, []) :-
    !.
transpose( I, M, [L1 | Ls]) :-
    take_nth( I, M, L1),
    Inew is (I - 1),
    transpose( Inew, M, Ls).



 

% ======== READ IN ======== %
% ------------------------- %

% get_line(L),
% gets characters until and excluding the next '\n'
get_line( []) :-
	peek_char(end_of_file),
	!.
get_line( []) :-
    peek_char('\n'),
    !,
    get_char(_).
get_line( [C | L]) :-
    get_char(C),
    get_line(L).

% get_chars( int, list)
% gets #1 chars or less than that if end_of_file encountered, from the current input streem, 
% returns in #2, 
get_chars( I, X) :-
    get_chars( I, [], X).

get_chars( 0, X, X) :-
    !.
get_chars( _, X, X) :-
    peek_char(end_of_file),
    !.
get_chars( I, X, [C | Y]) :-
    get_char(C),
    Inew is (I - 1),
    get_chars( Inew, X, Y).

% peek_chars( int, list)
% peeks #1 chars or less than that if end_of_file encountered, from the current input streem, 
% returns the input stream to the same position it received it at...
% returns in #2, 
peek_chars( I, X) :-
    peek_chars( I, [], X).

peek_chars( I, X, Y) :-
    peek_chars( I, I, X, Y).

peek_chars( 0, Iold, X, X) :-
    !,
    seeing(IS),
    SeekTo is (0 - Iold),
    seek(IS, SeekTo, current, _).   
peek_chars( I, Iold, X, X) :-
    peek_char(end_of_file),
    !,
    seeing(IS),
    SeekTo is (0 - (Iold - I)),
    seek(IS, SeekTo, current, _).   
peek_chars( I, Iold, X, [C | Y]) :-
    get_char(C),
    Inew is (I - 1),
    peek_chars( Inew, Iold, X, Y).


% get_clause( Clause)
% returns a list of chars from current position until next '.',
% then skips forward past the next '\n'
get_clause(C) :-
    get_clause( [], X),
    delete(X, ' ', X1),
    delete(X1, '\n', C).

get_clause( X, X) :-
    peek_char('.'),
    !,
    get_char(_),
    skip_past('\n').
get_clause( X, [C | Y]) :-
    get_char(C),
    get_clause(X, Y).


% skip_past(char)
% skips forward past the next occurence of #1
skip_past( C) :-
    peek_char(C),
    !,
    get_char(_).
skip_past( C) :-
    get_char(_),
    skip_past(C).


% get_predicate( P)
% sets #1 to a list of clauses who share the same head
get_predicate([C| P]) :-
    get_clause( C),
    get_head( C, H),
    extract_pred_id( H, PI),
    length( PI, I),
    get_predicate( PI, I, [], P).

get_predicate( PI, I, L, P) :-
%    Isafe is (I + 10),
    peek_chars( I, Cs),
%    remove_leading_nl( Cs, Cs1),
%    take( I, Cs1, CsHead),
    (
     Cs = PI,
     !,
     get_clause( C),
     get_predicate( PI, I, L, Ptemp),
     P = [C | Ptemp]
    ;
     L = P
    ).


get_all_clauses( []) :-
    peek_char(end_of_file),
    !.
get_all_clauses( [C | Cs]) :-
    get_clause( C),
    get_all_clauses( Cs).


get_pred_ids( [], []).
get_pred_ids( [C | Cs], [PI | PIs]) :-
    get_head( C, H),
    extract_pred_id( H, PI),
    get_pred_ids( Cs, PIs).


get_pred( [], _, []).
get_pred( [C | Cs], PI, [C | P]) :-
    get_head( C, H),
    extract_pred_id( H, PI),
    !,
    get_pred( Cs, PI, P).
get_pred( [_ | Cs], PI,  P) :-
    get_pred( Cs, PI, P).


get_preds( [], _, []).
get_preds( [PI | PIs], Cs, [P | Ps]) :-
    get_pred( Cs, PI, P),
    get_preds( PIs, Cs, Ps).


sort_clauses_into_preds( Cs, Ps) :-
    get_pred_ids( Cs, PIs),
    sort( PIs, P),
    get_preds( P, Cs, Ps).

% ========= OUTPUT UTILS ================ %
% --------------------------------------- %
put_matrix( []).
put_matrix( [L|Ls]) :-
    put_list(L),
    put('\n'),
    put_matrix(Ls).

put_list( []).
put_list( [C|Cs]) :-
    put(C),
    put_list(Cs).

% put_constraint_line(L),
% prints the list of lists (#1), seperating them by ','
put_constraint_line( [L]) :-
	!,
	put_list(L).
put_constraint_line( [L | Ls]) :-
	put_list(L),
	put_char(','),
	put_constraint_line( Ls).	


% put_constraint_lines(L)
% calls put_constraint_line on each element of #1
% seperating output by '\n'
put_constraint_lines( []).
put_constraint_lines( [L | Ls]) :-
	put_constraint_line( L),
	put('\n'),
	put_constraint_lines( Ls).


% ========== SYNTAX MANIPULATION ======== %
% --------------------------------------- %

% get_head( Clause, Head),
% #1 is a list of characters representing a clause read in from file, 
% #2 is set to the beginning of the list until the neck-symbol (without trailing ' ')
% det
get_head( C, H) :-
    nth1( P, C, ':'),
    !,     % because nth1\3 is used in non-det mode... 
    Pnew is (P - 1),
    take( Pnew, C, C1),
    remove_trailing_ws( C1, H).


% get_body( Clause, Body),
% #1 is a list of characters representing a clause read in from file, 
% #2 is set to the tail of the list starting from the neck-symbol, with all ' ' removed
% det
get_body( C, B) :-
    nth1( P, C, ':'),
    !,     % because nth1\3 is used in non-det mode... 
    Pnew is (P + 1),
    drop( Pnew, C, B).
    

% extract_pred_id( Head, Id) 
% sets #2 to the first part of #1,
% which should be the predicate identifier, without the added index
extract_pred_id( H, PI) :-
    nth1( P, H, '('),
    !,     % because nth1\3 is used in non-det mode... 
    P1 is (P - 1),
    take( P1, H, T),
    check_index( T, PI).

check_index( T, PI) :-
    length( T, L),
    L1 is (L - 3),
    drop( L1, T, T1),
    ( T1 = ['_', '_', _],
      !,
      take( L1, T, PI)
    ;
      PI = T
    ).



 
%drop_index( L, R) :-
%    last( L, '_'), 
%    !,
%    length( L, Len),
%    Len1 is (Len - 1),
%    take( Len1, L, R).
%drop_index( L, R) :-
%    length( L, Len),
%    Len1 is (Len - 1),
%    take( Len1, L, T),
%    drop_index( T, R).


% atomise_vars( L, R)
% sets #2 to the result of replacing all variables in #1 with 
% atoms formed from their names
% assumes #1 does not contain ' '
% therefore variable are separated by either one of:
% ',', '=', '<', '>', ... ??
atomise_vars( [], []).
atomise_vars( [','| L], [',' | R]) :-
    !,
    atomise_vars( L, R).
atomise_vars( ['='| L], ['=' | R]) :-
    !,
    atomise_vars( L, R).
atomise_vars( ['>'| L], ['>' | R]) :-
    !,
    atomise_vars( L, R).
atomise_vars( ['<'| L], ['<' | R]) :-
    !,
    atomise_vars( L, R).
atomise_vars( [A | As], [Var | R]) :-
    char_code( A, C),
    C >= 65,
    C =< 90,
    !,
    (nth1( P1, As, ',') ; P1 = 999),
    (nth1( P2, As, '=') ; P2 = 999),
    (nth1( P3, As, '<') ; P3 = 999),
    (nth1( P4, As, '>') ; P4 = 999),
    min_list( [P1, P2, P3, P4], P),
    (P >= 999, 
     !, 
     string_to_atom( [A|As], Var),
     R = []
    ;
     take( P, [A | As], V),
     string_to_atom( V, Var),
     drop( P, [A | As], L),
     atomise_vars( L, R),
     !
    ).
    


% extract_head_vars( Head, Vars)
% given a string represeting a head in #1, 
% sets #2 to a list of variables occuring in #1
extract_head_vars( H, Vs) :-
    nth1( P1, H, '('), 
    drop( P1, H, Hnew),
    nth1( P2, Hnew, ')'),
    !,     % because nth1\3 is used in non-det mode...
    P3 is (P2 - 1),
    take( P3, Hnew, V1),
    delete( V1, ',', V2),
    delete( V2, ' ', Vs).



% extract_vars( Body, Vars)
    % sets #2 to a list of all the variables occuring in #1
% does so, by 
extract_vars( B, V) :-
    delete( B, '=', B1),
    delete( B1,',', B2),
    delete( B2,'>', B3),
    delete( B3,'<', B4),
    del_numbers( B4, V).

del_numbers( [], []).
del_numbers( [C | L], [C | R]) :-
    char_code( C, C1),
    C1 >= 65,
    C1 =< 90,
    !,
    del_numbers( L, R).
del_numbers( [_ | L],  R) :-
    del_numbers( L, R).

del_non_nums( [], []).
del_non_nums( [C | L], [C| R]) :-
    char_code( C, C1),
    C1 >= 48,
    C1 =< 57,
    !,
    del_non_nums( L, R).
del_non_nums( [_ | L],  R) :-
    del_non_nums( L, R).


% count_vars( B, S)
% sets #2 to the number of variables in #1
count_vars( B, S) :-
    extract_vars( B, Vs), 
    sort( Vs, V1),
    length( V1, S).


% split_body( B, Cs) 
% sets #2 to the list of lists resulting from splitting #1 at 
% the','s
split_body( [], []) :-
    !.
split_body( B, [C | Cs]) :-
    (
     nth1( P, B, ','),
     !,     % because nth1\3 is used in non-det mode...
     P1 is (P - 1),
     take( P1, B, C),
     drop( P, B, B1),
     split_body( B1, Cs)
    ;
     C = B,
     Cs = []
    ).
    
     
    


% ======== NORMALISATION ========== %
% --------------------------------- %


% calls get_coefficient for every member of #1, 
% returning a list of results
get_coefficients( [], _, _, []) :-
    !.
get_coefficients( [V | Vs], L, R, [C | Cs]) :-
    get_coefficient( V, L, R, C),
    get_coefficients( Vs, L, R, Cs).



% get_coefficient( A, L, R, N)
% sets #4 to the coefficient of #1 in #2 and #3
% by getting the coefficient on either side 
% and then subtracting one from the other
% !! ASSUMPTION: Every variable occurs no more than once 
% on each side of an equation ! 
get_coefficient( V, L, R, N) :-
    get_coefficient( V, L, Nl),
    get_coefficient( V, R, Nr),
    N is (Nl - Nr).


% get_coefficient( V, C, N)
% sets #3 to the coefficient of #1 in #2
% !! ASSUMPTION: V occurs at most once in C
get_coefficient( V, C, N) :-
	nth1( P, C, V), 
	!,   % because 'nth1'\3 is used in non-det mode, assumption introduced here...
	find_sign( P, C, S, Sp),
	Pnew is (P - 1),
	take( Pnew, C, C1),
	drop( Sp, C1, C2),
	construct_coefficient( S, C2, N).
% V doesn not occur in C
get_coefficient( _, _, 0). 

% find_sign( P, C, S, Sp) 
% sets #3 to the first '-'/ '+' encountered
% left of #1 in #2, and #3 to the index of the sign
% if there is no sign, the index is 0 and the sign '+'		  

% no sign means positive sign!  
find_sign( 0, _, '+', 0) :-
	!.
find_sign( P, C, '+', Pnew) :-
	Pnew is (P - 1),
	nth1( Pnew, C, '+'), 
	!.
find_sign( P, C, '-', Pnew) :-
	Pnew is (P - 1),
	nth1( Pnew, C, '-'),
	!.
find_sign( P, C, S, Sp) :-
	Pnew is (P - 1), 	
	find_sign( Pnew, C, S, Sp).


% construct_coefficient( S, C, Coeff)
% turns a list of characters representing a number (#2)
% into an integer (#3), the sign of which depends on #1
% very inefficient, because I am too lazy to do this properly,
% so am simply using list-utils below that are not quite made for this...
construct_coefficient( _, [], 1) :- !.
construct_coefficient( '+', C, Coeff) :-
	list_atoms_to_codes(C, X),
	delete(X, ' ', Y),
	number_codes(Coeff, Y).
construct_coefficient( '-', C, Coeff) :-
	list_atoms_to_codes(C, X),
	delete(X, ' ', Y),
	number_codes( Z, Y),
	Coeff is (0 - Z).
	


coefficients_to_codes( [], []).
coefficients_to_codes( [C | Cs], P) :-
    atom_codes( C, L),
    coefficients_to_codes( Cs, Ls),
    append( L, [' ', ' '], L1),
    append( L1, Ls, P).


% get_constant( L, R, N) 
% calculates the constant (that is non-variable-coefficient)
% component of a constraint by subtracting
% the constant on the right from the constant on the left
% !! ASSUMPTION: each side of the constraint has no more than 
% one constant addend, which is the last addend of the sum
% !! ASSUMPTION: if there is no constant on a side, then 
% the last characer on that side is not a numberical one
get_constant( L, R, N) :-
	get_constant( L, Cl),
	get_constant( R, Cr),
	Num is (Cl - Cr),
	number_codes(Num, N).

get_constant( C, 0) :-
	last( C, X),
	atom_codes( X, [Y]),
	( Y < 48 ; Y > 57), 
	!. % 2nd assumption: last character not numerical
		
get_constant( C, N) :-
	length( C, P),
	find_sign( P, C, S, Sp),
	take( P, C, C1),
	drop( Sp, C1, C2),
	construct_coefficient( S, C2, N).




% ======== LIST UTILS ========= %
% ----------------------------- %

% take( int, list, list)
% sets #3 to first #1 elemenst of #2
% det
take( 0, _, []) :-
    !.
take( _, [], []) :-
    !.
take( I, [H | T], [H | R]) :-
    Inew is (I - 1),
    take( Inew, T, R).

% drop( int, list, list)
% sets #3 to the result of deleting the first #1 elemenst from #2
% det
drop( 0, L, L) :-
    !.
drop( _, [], []) :-
    !.
drop( I, [_ | T],  R) :-
    Inew is (I - 1),
    drop( Inew, T, R).


% remove_trailing_ws( L, R)
% sets #2 to the result of removing all ' ' at the end of #1
% det
remove_trailing_ws( Cs, R) :-
    last(Cs, ' '),
    !,
    length( Cs, L),
    Lnew is (L - 1),
    take( Lnew, Cs, Csnew),
    remove_trailing_ws( Csnew, R).
remove_trailing_ws( Cs, Cs).
    
% remove_leading_nl( L, R)
% sets #2 to the result of removing all '\n' at the head of #1
remove_leading_nl( ['\n' | L], R) :-
    !,
    remove_leading_nl( L, R).
remove_leading_nl( L, L).



% replace_list( As, Bs, L, R)
% sets #4 to the result of replaceing all occurences of 
% the nth element of #1 in #3 with the nth element of #2 
% assumes that #1 and #2 are disjoined
replace_list( [], [], _, _) :-
    !.
replace_list( [A], [B], L, R) :-
    !,
    replace( A, B, L, R).
replace_list( [A | As], [B | Bs], L, R) :-
    replace( A, B, L, L1),
    replace_list( As, Bs, L1, R).
    

% replace( A, B, L, R)
% sets #4 to the reuslt of replacing all occurences of #1 in #3 with #2
replace( _, _, [], []) :-
    !.
replace( A, B, [A | L], [B | R] ) :-
    !,
    replace( A, B, L, R).
replace( A, B, [C | L], [C | R]) :-
    replace( A, B, L, R).


% chars_to_nums( L, R)
% sets #2 to the result of changing eac element of #1 
% to its character code
chars_to_nums( [], []).
chars_to_nums( [L | Ls], [R | Rs]) :-
	char_code( L, C),
	R is (C - 48),
	chars_to_nums( Ls, Rs).

% take_nth( I, Ls, R)
% sets #3 to the list containing the #1th elements of 
% the lists contained in #2
take_nth( _, [], []) :-
    !.
take_nth( I, [L | Ls], [R | Rs]) :-
    nth1( I, L, R),
    take_nth( I, Ls, Rs).


% matrix_codes_to_atoms( M, Mnew)
% sets #2 to the result of converting all the codes 
% back to atoms in #1
matrix_codes_to_atoms( [], []).
matrix_codes_to_atoms( [L | Ls], [R | Rs]) :-
    list_codes_to_atoms( L, R),
    matrix_codes_to_atoms( Ls, Rs).


list_codes_to_atoms( [], []) :-
    !.
list_codes_to_atoms( L,  Res) :-
    ( nth1( P, L, ' '),
      !,   % nth1 used in non-det mode...
      P1 is (P - 1),
      P2 is (P + 1),
      take( P1, L, Cs),
      atom_codes( A, Cs),
      drop( P2, L, L1),
      list_codes_to_atoms( L1, R),
      Res = [A | R]
    ;
      atom_codes( A, L),
      Res = [A]
    ).


% matrix_atoms_to_codes( M, Mnew)
% reverse of matrix_codes_to_atoms
matrix_atoms_to_codes( [], []).
matrix_atoms_to_codes( [L | Ls], [R | Rs]) :-
    list_atoms_to_codes( L, R),
    matrix_atoms_to_codes( Ls, Rs).


list_atoms_to_codes( [], []) :-
    !.
list_atoms_to_codes([A | L],  R) :-
    atom_codes( A, Cs),
    append(Cs, [' ', ' '], R1),
    list_atoms_to_codes( L, R2),
    append( R1, R2, R).


matrix_flip_signs( [], []).
matrix_flip_signs( [L | Ls], [R | Rs]) :-
    list_flip_signs( L, R),
    !,
    matrix_flip_signs( Ls, Rs).

list_flip_signs( [], []).
list_flip_signs( L, R) :-
    ( nth1( P, L, ' '),
      !,   % nth1 used in non-det mode...
      P1 is (P - 1),
      P2 is (P + 1),
      take( P1, L, N),
      flip_sign( N, Nnew),
      drop( P2, L, Ls),     
      list_flip_signs( Ls, R1),
      append( Nnew, [' ', ' '], N1),
      append( N1, R1, R)
    ;
      flip_sign( L, R)
    ).


flip_sign( [48], [48]) :-
    !.
flip_sign( [45 | L], L) :-
    !.
flip_sign( L, [45 | L]).


add_to_all_lines( [], _, []).
add_to_all_lines( [L | Ls], A, [R | Rs]) :-
    append(A, L, R),
    add_to_all_lines( Ls, A, Rs).


build_non_neg_lines( N, Ls) :-
    build_non_neg_lines( N, N, Ls).

build_non_neg_lines( 0, _, []) :-
    !.
build_non_neg_lines( Cur, N, [L | Ls]) :-
    build_non_neg_line( Cur, N, L),
    NewCur is (Cur - 1),
    build_non_neg_lines( NewCur, N, Ls).

build_non_neg_line( Cur, N, L) :-
    zeros( Cur, L1),
    N1 is (N - Cur),
    zeros( N1, L2),
    append( L1, ['1', ' ', ' ' | L2], L). 


zeros( 0, []) :-
    !.
zeros( N, ['0', ' ', ' ' | Zs]) :-
    Nnew is (N - 1),
    zeros( Nnew, Zs).
