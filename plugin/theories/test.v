(* to be used e.g. in : coqtop -I src -R theories Egg < theories/test.v *)
Require Import egg.Loader.

(* This should print Type. *)
Test3_1.

(* This should print a term that contains an existential variable. *)
(* And then print the same term, where the variable has been correctly
   instantiated. *)
Test3_2.
