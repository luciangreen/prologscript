tute("State and visible code", "Remembering things, and seeing what ran").

lesson(1, "Remembering things",
"A program remembers between events with `nb_setval(Key, Value)` and `nb_getval(Key, Value)`. Set the start values in `on(start)`. (Each event is its own goal, so a variable bound in one isn't there in the next.)").
check(1, "tap three times.", (nb_getval(taps, N), N >= 3)).
:- begin(1).
canvas(600, 360, white).
on(start) :- nb_setval(taps, 0), say("Tap the canvas.").
on(down(X, Y)) :-
    nb_getval(taps, N0), N is N0 + 1, nb_setval(taps, N),
    new_id(tap, Id), shape(Id, text(X, Y, 28, N), [fill(navy)]),
    say(["Taps: ", N]).
:- end(1).

lesson(2, "Seeing what ran",
"On the right, the clause that answered the last event is marked in yellow, and the trace lists each event, the commands it gave (with what they answered) and any error. Here the left half and the right half of the canvas are answered by different clauses: watch the mark move.").
check(2, "tap the left half, then the right half.", (catch(nb_getval(left, yes), _, fail), catch(nb_getval(right, yes), _, fail))).
:- begin(2).
canvas(600, 360, white).
on(start) :- shape(middle, line(300, 0, 300, 360), [stroke(grey), width(2)]).
on(down(X, Y)) :- X < 300, !, nb_setval(left, yes), brush(colour, red), brush(size, 30), paint(dot(X, Y)), say("The left clause ran.").
on(down(X, Y)) :- nb_setval(right, yes), brush(colour, blue), brush(size, 30), paint(dot(X, Y)), say("The right clause ran.").
:- end(2).

lesson(3, "Your own program",
"Change anything in the code and press Run (or Ctrl+Enter). Errors show in the trace, with the command that caused them. Try adding a menu, a shape or a key. When you're ready, the 🧩 My program tab keeps a program of your own.").
check(3, "change the program so it paints or draws something, run it, and use it.", ( painted(N), N > 0 ; shapes([_|_]) )).
:- begin(3).
title("Mine").
canvas(600, 360, white).
menu_bar([menu("Shapes", [item("A circle", add(circle)), item("A square", add(square))])]).
add(circle) :- new_id(c, Id), shape(Id, circle(300, 180, 60), [fill(pink)]).
add(square) :- new_id(s, Id), shape(Id, square(240, 120, 120), [fill(sky)]).
on(start) :- say("Use the Shapes menu, or change the code and press Run.").
:- end(3).
