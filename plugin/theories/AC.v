Require Import egg.Loader.
Require Import Coq.ZArith.ZArith. (* TODO make plugin work even if ZArith is not loaded *)

Section WithLemmas.
  Context (U: Type)
          (add: U -> U -> U)
          (neg: U -> U)
          (zero: U)
          (add_0_l : forall x, add zero x = x)
          (add_comm : forall a b, add a b = add b a)
          (add_to_left_assoc : forall a b c, add a (add b c) = add (add a b) c)
          (add_opp : forall a, add a (neg a) = zero).

  Goal forall x1 x2,
      zero = zero ->
      add x2 (neg x1) = add (add x1 (add x2 (neg x1))) (neg x1).
  Proof.
    clear add_opp.
    intros.
    egg_simpl_goal 6. (* max ffn that occurs is 5 *)
    cbv beta.
  Abort.

  Goal forall x1 x2,
      zero = zero ->
      add x2 (neg x1) = add (add x1 (add x2 (neg x1))) (neg x1).
  Proof.
    (* this time, we keep add_opp *)
    intros.
    egg_simpl_goal 6.
    cbv beta.
    reflexivity.
  Qed.

End WithLemmas.
