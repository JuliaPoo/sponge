Inductive dyn_list: Type :=
| dyn_nil
| dyn_cons{A: Type}(head: A)(tail: dyn_list).
Register dyn_list as egg.dyn_list.
Register dyn_nil as egg.dyn_nil.
Register dyn_cons as egg.dyn_cons.

Declare Custom Entry dyn_list.
Notation "x" := (dyn_cons x dyn_nil)
  (in custom dyn_list at level 0, x constr at level 0).
Notation "h t" := (dyn_cons h t)
  (in custom dyn_list at level 0, h constr at level 0, t custom dyn_list at level 0).

Notation "'dyn_list:(' l ')'" := l
  (l custom dyn_list at level 1, format "dyn_list:( l )").

Goal dyn_list:(true) <> dyn_list:(1 (2 = 2) true). Abort.

Definition with_trigger(t: dyn_list)(P: Prop) := P.
Register with_trigger as egg.with_trigger.

Notation "'trigger!' ( t ) P" := (with_trigger t P)
  (at level 10, t custom dyn_list at level 0, P constr at level 0,
   format "trigger!  ( t )  P").

Goal (forall a b : nat, trigger! ((a * b)) (0 <= a -> 0 <= b -> 0 <= a * b))
   = (forall a b: nat, with_trigger (dyn_cons (a * b) dyn_nil)
                                    (0 <= a -> 0 <= b -> 0 <= a * b)).
Proof. reflexivity. Abort.

Goal (forall a b : nat, trigger! ((a * b) (b * a)) (0 <= a -> 0 <= b -> 0 <= a * b)).
Abort.
