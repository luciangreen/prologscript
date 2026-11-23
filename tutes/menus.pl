% Tute: menus. Each step is a PrologScript program between :- begin(N). and :- end(N).
tute("Menus", "A menu bar, menus inside menus, ticks and shortcuts").

lesson(1, "A menu bar",
"A program shows a menu bar by stating one fact: `menu_bar(Menus)`. Each `menu(Label, Items)` is a menu; each `item(Label, Goal)` runs its Goal when you choose it.

Here the goals are host commands: `brush(colour, red)` sets the brush's colour. The painting comes from the `on/1` clauses (the Events tute explains them).").
check(1, "choose Colour › Red, then paint a little.", brush_is(colour, red)).
:- begin(1).
canvas(600, 360, white).
menu_bar([menu("Colour", [item("Red", brush(colour, red)),
                          item("Blue", brush(colour, blue))])]).

on(start) :- say("Choose a colour from the menu, then paint.").
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(1).

lesson(2, "Menus inside menus",
"An item list can hold another `menu(Label, Items)`, to any depth: Colour › Cool › Green. Point at (or tap) an entry with › to open it. With the keyboard, arrows move and Enter chooses.

`separator` draws a line between entries.").
check(2, "choose Colour › Cool › Green.", brush_is(colour, green)).
:- begin(2).
canvas(600, 360, white).
menu_bar([menu("Colour", [menu("Warm", [item("Red", brush(colour, red)),
                                        item("Orange", brush(colour, orange))]),
                          menu("Cool", [item("Blue", brush(colour, blue)),
                                        item("Green", brush(colour, green))]),
                          separator,
                          item("Black", brush(colour, black))])]).

on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(2).

lesson(3, "Ticks, shortcuts and your own goals",
"`item(Label, Goal, Options)` takes options: `key(b)` is a keyboard shortcut, `checked(Goal)` shows a tick when Goal is true, and `enabled(Goal)` greys the item out when it isn't. The conditions are asked each time the menu opens.

A Goal can be any predicate of your own, such as `big` below. Menus are worked out when they open, so `menu_bar` can be a rule.").
check(3, "press b (or choose Brush › Big), then open the Brush menu to see the tick.", brush_is(size, 24)).
:- begin(3).
canvas(600, 360, white).
menu_bar([menu("Brush", [item("Small", small, [key(s), checked(brush_is(size, 4))]),
                         item("Big", big, [key(b), checked(brush_is(size, 24))])])]).

small :- brush(size, 4), say("Small brush").
big :- brush(size, 24), say("Big brush!").

on(start) :- small.
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(3).
