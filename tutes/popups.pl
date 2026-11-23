tute("Pop-up menus", "Right-click or hold a finger down; pop-ups inside pop-ups").

lesson(1, "A pop-up menu",
"`popup_menu(context, Items)` is the menu that opens where you right-click, or where you hold a finger down on a phone or tablet. Its items are written just as the menu bar's are.").
check(1, "right-click (or hold a finger down) and choose Purple.", brush_is(colour, purple)).
:- begin(1).
canvas(600, 360, white).
popup_menu(context, [item("Purple", brush(colour, purple)),
                     item("Teal", brush(colour, teal)),
                     separator,
                     item("Clear", paint(clear))]).

on(start) :- say("Right-click, or hold a finger down, for the menu.").
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(1).

lesson(2, "Pop-ups inside pop-ups",
"A pop-up holds submenus as a menu bar does: Brush › Size › Thick. They open to the side, or to the left when there's no room.").
check(2, "open the pop-up, then Brush › Size › Thick.", brush_is(size, 30)).
:- begin(2).
canvas(600, 360, white).
popup_menu(context, [menu("Brush", [menu("Size", [item("Thin", brush(size, 3)),
                                                  item("Thick", brush(size, 30))]),
                                    menu("Tip", [item("Round", brush(tip, round)),
                                                 item("Square", brush(tip, square))])]),
                     item("Clear", paint(clear))]).

on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(2).

lesson(3, "Opening pop-ups yourself, and menus made by Prolog",
"`popup(Name)` opens a pop-up menu where the pointer is. Here the m key opens it.

`menu(Label, from(Pred))` makes a submenu when it opens: Prolog calls `Pred(Items)`. Below, `sizes/1` builds the items with `findall/3`.").
check(3, "press m, then Size › 40 pixels.", brush_is(size, 40)).
:- begin(3).
canvas(600, 360, white).
popup_menu(sizes, [menu("Size", from(sizes))]).
sizes(Items) :-
    findall(item(Label, brush(size, S), [checked(brush_is(size, S))]),
            ( member(S, [5, 10, 20, 40]), format(string(Label), "~w pixels", [S]) ),
            Items).

on(start) :- say("Press m for the menu.").
on(key(m)) :- popup(sizes).
on(down(X, Y)) :- paint(dot(X, Y)), nb_setval(last, X-Y).
on(drag(X, Y)) :- nb_getval(last, X0-Y0), paint(line(X0, Y0, X, Y)), nb_setval(last, X-Y).
:- end(3).
