iterate([_], []).
iterate([h|t]) :- iterate(t).