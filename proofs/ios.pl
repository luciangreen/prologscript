% Runs the Prolog spec (proofs/spec.pl) on the 200 recorded inputs in io/ios.jsonl, which come from
% running the JavaScript (npm run ios), and checks the spec gives every recorded output. So the
% JavaScript agrees with the spec on all 200 (the pattern is LucianOS's proofs/updates_ios.pl).
%
% Run from the repo folder:  swipl -g check -t halt proofs/ios.pl
:- use_module(library(http/json)).
:- use_module('spec.pl').

check :-
    setup_call_cleanup(open('io/ios.jsonl', read, In, [encoding(utf8)]), read_lines(In, Lines), close(In)),
    length(Lines, N),
    ( N =:= 200 -> true ; format("Expected 200 examples, found ~w~n", [N]), halt(1) ),
    foldl(check_line, Lines, 0, Bad),
    ( Bad =:= 0 -> format("All ~w recorded inputs give the recorded outputs in the Prolog spec.~n", [N])
    ; format("~w of ~w examples differ from the Prolog spec.~n", [Bad, N]), halt(1) ).

read_lines(In, Ls) :-
    read_line_to_string(In, L),
    ( L == end_of_file -> Ls = [] ; L == "" -> read_lines(In, Ls) ; Ls = [L|T], read_lines(In, T) ).

check_line(Line, B0, B) :-
    atom_json_dict(Line, D, [value_string_as(string), null(null), true(true), false(false)]),
    get_dict(n, D, Num), get_dict(name, D, Name0), get_dict(input, D, Args), get_dict(output, D, Want),
    atom_string(Name, Name0),
    (   catch(spec_ok(Name, Args, Want), E, (print_message(error, E), fail))
    ->  B = B0
    ;   ( catch(ps_spec:spec(Name, Args, G2), _, fail) -> true ; G2 = no_answer ),
        format("Example ~w (~w) differs:~n  recorded ~q~n  spec     ~q~n", [Num, Name, Want, G2]),
        B is B0 + 1 ).

% The spec computes each output from the recorded input; it is compared with the recorded one.
spec_ok(Name, Args, Want) :- ps_spec:spec(Name, Args, Got), norm(Got, G), norm(Want, W), G == W.

% Dicts become sorted Key-Value lists; numbers compare to six places, as the JSON has them.
norm(D, N) :- is_dict(D), !, dict_pairs(D, _, Ps0), maplist([K-V, K-V1]>>norm(V, V1), Ps0, Ps), msort(Ps, N).
norm(L, N) :- is_list(L), !, maplist(norm, L, N).
norm(X, N) :- number(X), !, N is round(X * 1000000) / 1000000.0.
norm(X, X).
