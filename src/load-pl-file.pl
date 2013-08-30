load_term(end_of_file) :- !, fail.
load_term(Term) :- assert(Term).
load_pl_file(File) :-
        open(File, read, In),
        repeat,
	read(In, Term),
        \+ load_term(Term),
	!,
	close(In).