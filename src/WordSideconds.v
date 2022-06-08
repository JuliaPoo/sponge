Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.micromega.Lia.

Module Z.
  Lemma mul_le : forall e1 e2 : Z, 0 <= e1 -> 0 <= e2 -> 0 <= e1 * e2.
  Proof. intros. nia. Qed.

  Lemma div_mul_lt: forall x d1 d2,
      0 < x ->
      0 < d1 ->
      d1 < d2 ->
      x / d2 * d1 < x.
  Proof. intros. Z.to_euclidean_division_equations. Lia.nia. Qed.

  Lemma lt_from_le_and_neq: forall x y,
      x <= y -> x <> y -> x < y.
  Proof. intros. Lia.lia. Qed.
End Z.

Lemma neq_sym{A: Type}: forall (x y: A), x <> y -> y <> x. congruence. Qed.

Section WithLib.
  Context (word: Type)
          (ZToWord: Z -> word)
          (unsigned: word -> Z)
          (wsub: word -> word -> word)
          (wadd: word -> word -> word)
          (wslu: word -> word -> word)
          (wsru: word -> word -> word)
          (wopp: word -> word).

  Context (wadd_0_l: forall a, wadd (ZToWord 0) a = a)
          (wadd_0_r: forall a, wadd a (ZToWord 0) = a)
          (wadd_comm: forall a b, wadd a b = wadd b a)
          (wadd_assoc: forall a b c, wadd a (wadd b c) = wadd (wadd a b) c)
          (wadd_opp: forall a, wadd a (wopp a) = ZToWord 0).

  Context (wsub_def: forall a b, wsub a b = wadd a (wopp b)).

  Context (unsigned_of_Z: forall a, 0 <= a < 2 ^ 32 -> unsigned (ZToWord a) = a).

  Context (unsigned_nonneg: forall x : word, 0 <= (unsigned x))
          (unsigned_sru_to_div_pow2: forall (x : word) (a : Z),
              0 <= a < 32 ->
              (unsigned (wsru x (ZToWord a))) = (unsigned x) / 2 ^ a)
          (unsigned_slu_to_mul_pow2: forall (x : word) (a : Z),
              0 <= a < 32 ->
              (unsigned (wslu x (ZToWord a))) = ((unsigned x) * 2 ^ a) mod 2 ^ 32)
          (word_sub_add_l_same_l: forall x y : word, (wsub (wadd x y) x) = y).

  Lemma bsearch_sideconds1: forall (x : list word) (x1 x2 : word),
      unsigned (wsub x2 x1) = 8 * Z.of_nat (length x) ->
      unsigned (wsub x2 x1) <> 0 ->
      unsigned (wsub (wadd x1 (wslu (wsru (wsub x2 x1) (ZToWord 4)) (ZToWord 3))) x1) <
        unsigned (ZToWord 8) * Z.of_nat (length x).
  Proof.
    intros.

    (* sideconditions about consts: *)
    assert (0 <= 8 < 2 ^ 32) as C1 by lia.
    assert (0 <= 3 < 32) as C2 by lia.
    assert (0 <= 4 < 32) as C3 by lia.
    assert (0 <= 2 ^ 3) as C4 by lia.
    assert (0 < 2 ^ 4) as C5 by lia.
    assert (0 < 2 ^ 32) as C6 by lia.
    assert (0 < 2 ^ 3) as C7 by lia.
    assert (2 ^ 3 < 2 ^ 4) as C8 by lia.

    rewrite unsigned_of_Z by exact C1.
    rewrite <- H.
    rewrite word_sub_add_l_same_l.
    rewrite unsigned_slu_to_mul_pow2 by exact C2.
    rewrite unsigned_sru_to_div_pow2 by exact C3.
    (* implication, not <->, so we can't rewrite with equality! *)
    eapply Z.le_lt_trans. 1: eapply Z.mod_le.
    { eapply Z.mul_le. 2: exact C4.
      eapply Z.div_pos. 2: exact C5.
      eapply unsigned_nonneg. }
    { exact C6. }
    eapply Z.div_mul_lt. 2: exact C6. 2: exact C7.
    eapply Z.lt_from_le_and_neq.
    1: apply unsigned_nonneg.
    apply neq_sym.
    apply H0.
  Qed.
End WithLib.
