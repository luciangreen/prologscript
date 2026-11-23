PrologScript {{version}}, the pack
==================================

Prolog in place of JavaScript: a program's commands become menus and pop-ups, painting, vector
shapes with layers and groups, drag and drop and pointers. This pack works on its own, without
LucianOS, with nothing to install and no internet connection.

  prologscript.html   The whole app: the Paint and Draw demos with their code, a tute for each
                      part of PrologScript, and My program, where you write your own.
                      Double-click it, or put it on any web host. Works on iPhone and Android.

  prologscript.js     Put PrologScript programs in your own web pages:
                        <script src="prologscript.js"></script>
                        <script type="text/prolog">
                          canvas(400, 300, white).
                          on(down(X, Y)) :- paint(dot(X, Y)).
                        </script>
                      data-src="file.pl" reads the program from a file (the page must then be
                      served, not opened from a folder); data-code="false" hides the code.
                      From JavaScript: PrologScript.mountProgram(element, source, {code: true}).

  example.html        A page that uses prologscript.js.

  demos/, tutes/      The programs as .pl files, to read or open in My program.

The language reference: https://github.com/luciangreen/prologscript#readme
Licence: BSD-3-Clause (LICENSE). Includes pl2detlog, BSD-3-Clause.
