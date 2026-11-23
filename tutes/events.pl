tute("Events", "on/1: down, drag, up, keys, and say").

lesson(1, "on/1 answers events",
"What you do becomes an event, and PrologScript asks `on(Event)`. A press is `down(X, Y)`, in the canvas's own units. If no clause matches, nothing happens (the trace on the right says so).

Watch the code: the clause that answered is marked in yellow.").
check(1, "tap or click on the canvas.", (painted(N), N > 0)).
:- begin(1).
canvas(600, 360, white).
on(start) :- brush(size, 20), brush(colour, orange), say("Tap the canvas.").
on(down(X, Y)) :- paint(dot(X, Y)).
:- end(1).

lesson(2, "Down, drag, up",
"Moving while pressed gives `drag(X, Y)` events, and letting go gives `up(X, Y)`. To draw a line from the last point, remember it with `nb_setval/2` and read it with `nb_getval/2` (the State tute explains these).").
check(2, "draw a long line.", (painted(N), N > 1500)).
:- begin(2).
canvas(600, 360, white).
on(start) :- brush(size, 8), brush(colour, blue).
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
on(up(X, Y)) :- say(["You let go at ", X, ", ", Y]).
:- end(2).

lesson(3, "Keys, and say",
"A key gives `key(K)`: letters as themselves, and `up`, `down`, `left`, `right`, `enter`, `escape`, `delete`, `backspace`, `space`. `say(Text)` writes in the status line under the canvas; a list of parts is joined.

There's also `start` when the program begins, `right(X, Y)` for a right-click, `drop(Thing, X, Y)` and `hover(X, Y)`.").
check(3, "press x on the keyboard (click the canvas first).", catch(nb_getval(key, x), _, fail)).
:- begin(3).
canvas(600, 360, white).
on(start) :- say("Press a key.").
on(key(K)) :- nb_setval(key, K), say(["You pressed ", K]).
:- end(3).
