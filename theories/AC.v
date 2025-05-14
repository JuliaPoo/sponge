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

  (* moving together summands that enable further simplifications might require high ffn: *)
  Goal forall x1 x2 a b c d v res,
      add x1 x2 = v ->
      add (add (add x1 a) b) (add c (add d x2)) = res.
  Proof.
    intros.
    clear dependent neg. clear dependent zero.
    egg_simpl_goal 5; cbv beta.
    (* at least 5 is needed to make v appear in goal *)
  Abort.

  Goal forall x1 x2 a b c d v res,
      add x1 x2 = v ->
      add (add (add x1 a) b) (add c (add d x2)) = res.
  Proof.
    intros.
    clear dependent neg. clear dependent zero.
    clear add_comm.
    assert (join_summands: forall a b m r,
               add a b = r -> add (add a m) b = add r m) by admit.
    assert (add_to_right_assoc : forall a b c, add (add a b) c = add a (add b c)) by admit.

    egg_simpl_goal 4; cbv beta.
    (* at least 4 is needed to make v appear in goal *)
    1: auto.

    (* obtaining all associative reorderings might still require high ffn, but
       high ffn might be more feasible if we don't add commutativity *)
  Abort.

  (* inline precondition of join_summands: *)
  Goal forall x1 x2 a b c d v res,
      add x1 x2 = v ->
      add (add (add x1 a) b) (add c (add d x2)) = res.
  Proof.
    intros.
    clear dependent neg. clear dependent zero.
    clear add_comm.
    (* this one creates the term (add a b), whereas the non-inlined one only triggers
       if (add a b) already is in the egraph *)
    assert (join_summands: forall a b m, add (add a m) b = add (add a b) m) by admit.
    assert (add_to_right_assoc : forall a b c, add (add a b) c = add a (add b c)) by admit.

    egg_simpl_goal 4; cbv beta. (* much slower *)
    (* at least 4 is needed to make v appear in goal *)

  Abort.

  (* inline precondition of join_summands, but add trigger: *)
  Goal forall x1 x2 a b c d v res,
      add x1 x2 = v ->
      add (add (add x1 a) b) (add c (add d x2)) = res.
  Proof.
    intros.
    clear dependent neg. clear dependent zero.
    clear add_comm.
    (* this one creates the term (add a b), whereas the non-inlined one only triggers
       if (add a b) already is in the egraph *)
    assert (join_summands: forall a b m,
               trigger! ((add a b)) (add (add a m) b = add (add a b) m)) by admit.
    assert (add_to_right_assoc : forall a b c, add (add a b) c = add a (add b c)) by admit.

    egg_simpl_goal 4; cbv beta. (* fast *)
    (* at least 4 is needed to make v appear in goal *)

  Abort.

  Goal forall x1 x2 a b c d v res,
      add x2 x1 = v -> (* <-- swapped *)
      add (add (add x1 a) b) (add c (add d x2)) = res.
  Proof.
    intros.
    clear dependent neg. clear dependent zero.
    clear add_comm.

    assert (join_summands: forall a b m, (* bad because b does not appear in conclusion *)
               trigger! ((add a b) (add (add a m) b)) (add a m = add m a)) by admit.
    assert (join_summands_swap: forall a b m,
               trigger! ((add b a)) (add (add a m) b = add (add b a) m)) by admit.

    assert (add_to_right_assoc : forall a b c, add (add a b) c = add a (add b c)) by admit.

    egg_simpl_goal 10; cbv beta. (* fast *)
  Abort.

  Goal forall x1 x2 a b c d v res,
      add x2 x1 = v -> (* <-- swapped *)
      add (add (add x1 a) b) (add c (add d x2)) = res.
  Proof.
    intros.
    clear dependent neg. clear dependent zero.
    clear add_comm.

    assert (join_summands: forall a b m,
               trigger! ((add a b)) (add (add a m) b = add m (add a b))) by admit.
    assert (join_summands_swap: forall a b m,
               trigger! ((add b a)) (add (add a m) b = add (add b a) m)) by admit.

    assert (add_to_right_assoc : forall a b c, add (add a b) c = add a (add b c)) by admit.

    egg_simpl_goal 10; cbv beta. (* fast *)
  Abort.

End WithLemmas.
