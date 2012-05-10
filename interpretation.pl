use_module( library(lists)).
use_module( library(gensym)).


% ======== MAIN =========== %
% ------------------------- %
% There must be a better way of doing the linear arithmetic... !!!


interpret_result( FilePrefix) :-
	get_vertices( FilePrefix, Vertices),
	get_constraint_clauses( FilePrefix, Constraints, Lengths, Variables),
	construct_preGRIs( Vertices, Constraints, Lengths, PreGRIs),
	construct_GRIs( PreGRIs, Variables, GRIs),
	!, % this is needed, because 'scale_constraints'\3 is not deterministic, which is undesirable and being worked on... 
	write_mux_file( FilePrefix, GRIs, Variables).



% ======== write final output

write_mux_file( FilePrefix, GRIs, Vars) :-
	atom_concat( FilePrefix, '.mux', File),
	tell( File),
	put_gris( GRIs, Vars, Gs, M1),
	construct_binary_mux( M1, Gs, [], Mux),
	put('\n'),
	put_list([ 'm','u','x',':',' ',' ']),
	put('\n'),
	put_binary_mux( Mux),
	told.


% put_binary_mux( Mux)
% writes a list of mux-conditions between pairs of clauses, 
% of the form constructed by 'construct_binary_mux'\4 
put_binary_mux( []).
put_binary_mux( [ ( (C1,C2), B) | Mux]) :-
	write( 'clauses '),
	write( C1), write('-'), write(C2), 
	write( ':  '),
	list_to_set( B, B1),
	sort( B1, B2),
	simplify( B2, [], B3),
	put_dnf( B3),
	put('\n'),
	put_binary_mux( Mux). 


% construct_binary_mux( Variables, GRIs, Accumulator, Muxs)
% given a list of lists of variables (#1) and a list of assembled tuples
% of gris (#2), constructs a list of binary mux-conditions (#4), 
% i.e. a list of elements of the form ( (C1, C2), Mux)), where C1/2 are 
% indexes of clauses and Mux is the mux-condition between these two clauses in dnf
% assumes #1 and #2 to be ordered in parallel, i.e. each element of #1 should contain exactly the variables of the parallel element of #2
construct_binary_mux( [], [], Acc, Acc).
construct_binary_mux( [_ | Vars], [G | Gs], Acc, Mux) :-
	delete( G, [t,r,u,e], Gt),
	length( Gt, L),
	(L \= 2), % the current tuple of gris does not encode a mux-condition between exactly two clauses - at this point i'm ignoring inconsistent clauses  
	!, 
	construct_binary_mux( Vars, Gs, Acc, Mux).
% since the last clause failed, G encodes a binary mux, we have only to find out between which two clauses and add V as a clause to the appropriate element of Acc
construct_binary_mux( [V | Vars], [G | Gs], Acc, Mux) :-
	nth1( P1, G, D1), D1 \= [t,r,u,e],
	nth1( P2, G, D2), D2 \= [t,r,u,e],
	P1 < P2,
	% a 'cut' here ought not to have any effect !	
(	memberchk( ((P1, P2), F), Acc),
	!,
	delete( Acc, ((P1, P2), F), Acc_temp),
	construct_binary_mux( Vars, Gs, [ ((P1,P2), [V|F]) | Acc_temp], Mux)
;
	construct_binary_mux( Vars, Gs, [ ((P1,P2), [V]) | Acc], Mux)	
).


% simplify( Formula, Accumulator, Formula)
% sorts out unneccessary disjuncts in a dnf 
% assumes the input to be a sorted set
simplify( [], B, B).
simplify( [A | As], C, B) :-
	memberchk( Ci, C),
	\+ Ci = [],	
	prefix( Ci, A),
	!,
	simplify( As, C, B).
simplify( [A | As], C, B) :-
	simplify( As, [A | C], B).



% again, this should be in library(lists), but its undefined...
prefix( A, B) :- append( A, _, B).


% put_dnf( Gris, Mux)
% prints a formula in dnf
put_dnf( [D]) :-
	put_disjunct(D).
put_dnf( [D | Ds]) :-
	put_disjunct( D ),
	put_list([' ', 'v', ' ']),
	put_dnf( Ds). 

put_disjunct( [C]) :-
	put(C).
put_disjunct( [C | Cs]) :-
	put( C),	
	put( '&'),
	put_disjunct( Cs).


% layout_gris( GRIs, Vars, M)
% calls mcav_all on each element of #1
% prints the results while assembling the list of them
% constructs mux on the way
put_gris( [], _, [], []).
put_gris( [G | Gs], Vars, [M | Ms], [D | Ds]) :-
	mcav_all( G, Vars, M, Dt),
	flatten( Dt, Dt1),
	list_to_set( Dt1, Dt2),
	sort( Dt2, D),	
	put_constraint_line( M),
	put('\n'),	
	put_gris( Gs, Vars, Ms, Ds).


% mcav_all( Cs, Vs, Ms)
% calls 'merge_coeffs_and_vars'\3 on all elements of #1
% and appends ['=','<' | Constant] to each
% constructs raw mux-disjuncts on the way
mcav_all( [], _, [], []).
mcav_all( [ [] | Ccs], Vs, [[t,r,u,e] | Ms], Ds) :-
	!,
	mcav_all( Ccs, Vs, Ms, Ds).
mcav_all( [ [N | Cs] | Ccs], Vs, [M | Ms], [D | Ds]) :-
	number_codes( N, Const),	
	merge_coeffs_and_vars( Cs, Vs, M1, D),
	append( M1, ['=', '<' | Const], M),
	mcav_all( Ccs, Vs, Ms, Ds).



% merge_coeffs_and_vars( Coeffs, Vars, Merge, MuxDisjunct)
% merges the codes representing the elements of #1 with 
% the elements of #2
% constructs a mux-disjunct on the way (#4)
merge_coeffs_and_vars( [], [], [], []).
merge_coeffs_and_vars( [C | Cs], [V | Vs], M, D) :-
( 	C > 0,
	!,
	number_codes( C, Codes),
	append( [43 | Codes], [V], M1),
	merge_coeffs_and_vars( Cs, Vs, M2, D1),
	append( M1, M2, M),
	D = [V | D1]
;
	(C = 0 ; C = 0.0),
	!,
	merge_coeffs_and_vars( Cs, Vs, M, D)
;
	C < 0, % this is not be neccessary, only checking...	
	number_codes( C, Codes),
	append( Codes, [V], M1),
	merge_coeffs_and_vars( Cs, Vs, M2, D1),
	append( M1, M2, M),
	D = [V | D1]
).
	


% ======== read in info from temp-files 
% ---------------------
% get_vertices( FilePrefix, Vertices)
% wrapper for read_vertices from '#1.out' file
get_vertices( FilePrefix, Vertices) :-
	atom_concat( FilePrefix, '.out', File),
	see( File),
% .out files start with a '\n', and 4 lines of info that needs to be skipped:
	skip_past('\n'), skip_past('\n'), skip_past('\n'), skip_past('\n'), skip_past('\n'),
	read_vertices(Vertices),
	seen.


% read_vertices( Vertices)
% reads in only the vertices from current input
read_vertices( []) :-
	get_line( ['e','n','d']), 
	!.	
read_vertices( Vs) :-
	get_line(L),
	split_vertex(L, H),
	delete( H, [], [G | Gs]),
(	G = ['0'],
	!, % G is not a vertex but a ray
	read_vertices( Vs)
;
	make_rationals(Gs, Vt),		
	read_vertices( Vst),
	Vs = [Vt | Vst]	
).


% make_rationals( Rats, Ns)
% calls 'make_rational'\2 on every element of #1
make_rationals( [], []).
make_rationals( [R | Rs], [N | Ns]) :-
	make_rational( R, N),
	make_rationals( Rs, Ns). 


% make_rational( List, N)
% turns a list of characters (including '\') into the represented number
make_rational( R, N) :-
	\+ memberchk( /, R), % the number is not actually a rational, but an integer...
	!,
	chars_to_nums( R, S),
	num_list_to_num( S, N).
make_rational( R, N) :-
     	nth1( P, R, /),
     	!,     % because nth1\3 is used in non-det mode...
     	P1 is (P - 1),
     	take( P1, R, R1),
     	drop( P, R, R2),
	chars_to_nums( R1, T1),
	chars_to_nums( R2, T2), 
	num_list_to_num( T1, S1),
	num_list_to_num( T2, S2),
	N is (S1 / S2).
	


% split_vertex( B, Cs) 
% sets #2 to the list of lists resulting from splitting #1 at 
% the' 's
split_vertex( [], []) :-
    !.
split_vertex( B, [C | Cs]) :-
    (
     nth1( P, B, ' '),
     !,     % because nth1\3 is used in non-det mode...
     P1 is (P - 1),
     take( P1, B, C),
     drop( P, B, B1),
     split_vertex( B1, Cs)
    ;
     C = B,
     Cs = []
    ).




% get_constraint_clauses( FilePrefix, Constraints, Lengths)	
% reads in a list of constraints from the first line of '#1.constraints'
% and the list of the lengths of the clauses specified the second line of'#1.constraints'
get_constraint_clauses( FilePrefix, Constraints, Lengths, Variables) :-
	atom_concat( FilePrefix, '.constraints', File),
	see( File),
	get_line( Cs),
	get_line( Ls),
	get_line( Variables),	
	seen,
	split_body( Cs, Constraints),
	split_body( Ls, Ltemp),
	chars_lists_to_nums( Ltemp, Lengths).
	


% chars_lists_to_nums( Ll, Nl)
% calls 'chars_list_to_num'\2 on each element of #1
chars_lists_to_nums( [], []).
chars_lists_to_nums( [L | Ls], [N | Ns]) :-
	chars_to_nums( L, C),
	num_list_to_num( C, N),
	chars_lists_to_nums( Ls, Ns).



% chars_list_to_num( L, N)
% takes a list of numbers as characters and returns the number represented
% again, there must be a better way !!
num_list_to_num( [], 0).
num_list_to_num( [C | Cs], N) :-
	num_list_to_num( Cs, Nnew),	
	length( Cs, P),
	W is (10 ^ P),
	Nc is (W * C),	
	N is (Nc + Nnew).

	



% ======== process things into preGRIs
% a preGRI being a list of pairs of multiplier and constraint
% ------------------------------------

% construct_preGRIs( Vertices, Constraints, Lengths,  PreGRIs)
% calls match_clauses with each element of #1 and #2 and #3
construct_preGRIs( [], _, _, []).
construct_preGRIs( [V | Vs], Cs, Ls, [P | Ps]) :-
	match_clauses( V, Cs, Ls, P),
	construct_preGRIs( Vs, Cs, Ls, Ps).



% match_clauses( Vertex, Constraints, Lengths, Clauses)
% constructs a list of pairs of multiplier (element of #1) and 
% constraint (element of #2) and splits these into clauses, 
% as specified by the lengths in #3
% !! ASSUMPTIONS: #1 and #2 have the same lengths 
% 	and sum_list(#3) is equal to that length
match_clauses( V, Cs, Ls, Clauses) :-
	zip( V, Cs, Ps),
	divide_by_lengths( Ls, Ps, Clauses).



% divide_by_lengths( Lengths, List, DividedList)
% divides #1 into several lists of the lengths specified by #2
divide_by_lengths( [], [], []).
divide_by_lengths( [L | Ls], List, [D | Ds]) :-
	take( L, List, D),
	drop( L, List, Listnew),
	divide_by_lengths( Ls, Listnew, Ds).



% zip( L1, L2, Lp)
% zip predicate
% !! ASSUMPTION: #1 and #2 are the same lengths
zip( [], [], []).
zip( [L1 | Ls1], [L2 | Ls2], [( L1, L2) | Ps]) :-
	zip( Ls1, Ls2, Ps).


% ========== make GRIs out of preGRIs
% ------------------------------------
% there has to be a better way to do the linear arithmetic
% than by the syntactic sillyness below !!


% construct_GRIs( preGRIs, Vars, GRIs)
% calls 'construct_GRI'\2 on each element of #2
construct_GRIs( [], _, []).
construct_GRIs( [P | Ps], Vars, [G | Gs]) :-
	construct_GRI( P, Vars, G),
	construct_GRIs( Ps, Vars, Gs).


% construct_GRI( preGRI, Vars, GRI)
% turns a clause of pairs of multipliers and constraints, 
% i.e. a list of such pairs (#1)
% into a constraint that is the weighted sum of the clause
% ??  Somehow this is non-det ?? Don't know why ? 
construct_GRI( [], _, []).
construct_GRI( [Clause | Clauses], Vars, [RI | RIs]) :-
	scale_constraints( Clause, Vars, T1),
	delete( T1, [], T2),
	transpose( T2, T3),
	sum_lists( T3, RI),
	construct_GRI( Clauses, Vars, RIs).
	

% sum_lists( Lists, Sums)
% calls sum_list on all elements of #1
sum_lists( [], []).
sum_lists( [L | Ls], [S | Sums]) :-
	sum_list( L, S),
	sum_lists( Ls, Sums).

% sum_list( List, Sum)
% bizarly, this seems to be needed, though it should be in the lists-library...
sum_list( [], 0).
sum_list( [N | Ns], S) :-
	sum_list( Ns, St),
	S is (N + St).




% scale_constraints( List_of_Pairs, Vars, Coeffsl )
% calls scale_constraint on all elements of #1
scale_constraints( [], _, []).
scale_constraints( [P | Ps], Vars, [C | Cs]) :-
	scale_constraint( P, Vars, C),
	scale_constraints( Ps, Vars, Cs).




% scale_constraint( (M, C), Vars, Coeffs )
% returns ordered list of coefficients of the elements of #2
% obtained by multiplying the coefficients in snd #1 by fst #1
% the first member of #3 is the scaled constant component of C,
% ?? IMPROVE ?? Somehow this is not deterministic... 
scale_constraint( (0, _), _, []).
scale_constraint( (1, C), Vars, [Const | Coeffs]) :-
	nth1( P, C, '='),
    	!,    % because 'nth1'\3 is used in non-det mode...
    	Pl is (P - 1),
    	Pr is (P + 1),
	nth1( Pr, C, '<'), % it better be, so this is unneccessary, but I'm using it for checking things just now...
	take( Pl, C, Left),
    	drop( Pr, C, Right),
	get_coefficients( Vars, Left, Right, Coeffs),
	get_constant( Left, Right, N),
	number_codes( Const, N).
scale_constraint( (M, C), Vars, Coeffs) :-
	nth1( P, C, '='),
    	!,    % because 'nth1'\3 is used in non-det mode...
    	Pl is (P - 1),
    	Pr is (P + 1),
	nth1( Pr, C, '<'), % it better be, so this is unneccessary, but I'm using it for checking things just now...
	take( Pl, C, Left),
    	drop( Pr, C, Right),
	get_coefficients( Vars, Left, Right, Cfstemp),
	get_constant( Left, Right, N),	
	number_codes( Const, N),
	multiply_all( [Const | Cfstemp], M, Coeffs).


% multiply_all( L, M, Lnew)
% multiplies all elements of #1 by #2
multiply_all( [], _, []).
multiply_all( [L | Ls], M, [G | Gs]) :-
	G is (L * M),
	multiply_all( Ls, M, Gs).








