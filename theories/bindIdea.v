(*
An idea to make the logical predicate proof nicer without going all the way to defining some
kind of general purpose functions:
1) Build a bind that lets you take an (A -> Prop) identifying possible an A, and an (A -> Prop)
   which says a fact about that A, and put them together
2) I have `Type -> (Term -> Prop) -> Prop'. This is actually a function, but maybe that doesn't
   really matter. The point is that for every types Ctx |- t : T, there exists an interpretation
   for T containing t. It doesn't really immediately matter if that interpretation is unique.
*)
