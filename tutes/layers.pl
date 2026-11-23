tute("Layers", "Back and front, hide, lock, move between layers").

lesson(1, "Layers",
"Layers are levels: everything on a higher layer is drawn over a lower one. `new_layer(Id, Name)` adds one on top and uses it; `use_layer(Id)` chooses where new shapes go. `panel(layers)` shows the Layers panel, where you can do the same with a tap.").
check(1, "add three circles to the Front layer.", (items_in(front, F), length(F, N), N >= 3)).
:- begin(1).
canvas(600, 360, white).
panel(layers).
on(start) :-
    rename_layer(layer1, "Back"),
    shape(ground, rect(0, 220, 600, 140), [fill(green), stroke(none)]),
    new_layer(front, "Front"),
    say("Tap to add circles to the layer in use. b: Back, f: Front.").
on(key(b)) :- use_layer(layer1), say("Using Back").
on(key(f)) :- use_layer(front), say("Using Front").
on(down(X, Y)) :- new_id(ball, Id), shape(Id, circle(X, Y, 25), [fill(orange), stroke(brown), width(2)]).
:- end(1).

lesson(2, "Hiding and locking",
"`show_layer(Id, false)` hides a layer and `lock_layer(Id, true)` locks it, so its shapes can't be changed or picked. In the Layers panel, 👁 and 🔒 do the same.").
check(2, "hide the Front layer with its eye in the Layers panel.", \+ layer_shown(front)).
:- begin(2).
canvas(600, 360, white).
panel(layers).
on(start) :-
    rename_layer(layer1, "Back"),
    shape(hill, ellipse(300, 400, 380, 160), [fill(green), stroke(none)]),
    new_layer(front, "Front"),
    shape(tree, polygon([100-230, 140-120, 180-230]), [fill(teal)]),
    shape(cloud, ellipse(420, 80, 80, 30), [fill(white), stroke(grey)]),
    say("Use the eye and lock in the Layers panel.").
:- end(2).

lesson(3, "Moving between layers",
"`to_layer(Id, Layer)` moves a shape to the top of another layer. Tap the ball to pick it, then press m to send it to the back, behind the wall.").
check(3, "move the ball to the Back layer.", (items_in(layer1, B), memberchk(ball, B))).
:- begin(3).
canvas(600, 360, white).
panel(layers).
on(start) :-
    rename_layer(layer1, "Back"),
    new_layer(front, "Front"),
    shape(wall, rect(200, 100, 200, 180), [fill(brown), stroke(none)]),
    shape(ball, circle(300, 190, 50), [fill(red)]),
    say("Tap the ball, then press m.").
on(down(X, Y)) :- shape_at(X, Y, Id), select([Id]).
on(key(m)) :- selection([Id]), to_layer(Id, layer1), say(["Moved ", Id, " to the back"]).
:- end(3).
