:- dynamic assignment/2. % assignment(Preimage, Image).

load_term(end_of_file) :- !, fail.
load_term(Term) :- assert(Term).
load_file(File) :-
        open(File, read, In),
        repeat,
	read(In, Term),
        \+ load_term(Term),
	!,
	close(In).

main :-
	prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_file(F)
        ).

:- main, halt.