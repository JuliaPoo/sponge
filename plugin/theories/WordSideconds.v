Require Import egg.Loader.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.PropExtensionality.
Set Default Goal Selector "!".

Lemma invert_eq_False: forall {P: Prop}, P = False -> ~ P.
Proof. intros. intro C. subst. assumption. Qed.
Lemma prove_eq_False: forall {P: Prop}, ~ P -> P = False.
Proof.
  intros. apply propositional_extensionality. split; intuition idtac.
Qed.

Lemma eq_eq_sym: forall {A: Type} (x y: A), (x = y) = (y = x).
Proof.
  intros. apply propositional_extensionality. split; intros; congruence.
Qed.

Module Z.
  Lemma mul_nonneg : forall e1 e2 : Z,
      0 <= e1 -> 0 <= e2 -> 0 <= e1 * e2.
  Proof. intros. Lia.nia. Qed.

  Lemma div_nonneg : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a / b.
  Proof. intros. apply Z.div_pos; assumption. Qed.

  Lemma div_mul_lt: forall x d1 d2,
      0 < x ->
      0 < d1 ->
      d1 < d2 ->
      x / d2 * d1 < x.
  Proof. intros. Z.to_euclidean_division_equations. Lia.nia. Qed.

  Lemma lt_from_le_and_neq: forall x y,
      x <= y -> x <> y -> x < y.
  Proof. intros. Lia.lia. Qed.

  Lemma forget_mod_in_lt_l : forall a b m : Z,
      0 <= a ->
      0 < m ->
      a < b ->
      a mod m < b.
  Proof.
    intros. eapply Z.le_lt_trans. 1: eapply Z.mod_le. all: assumption.
  Qed.
End Z.

Lemma neq_sym{A: Type}: forall (x y: A), x <> y -> y <> x. congruence. Qed.

Ltac consts :=
  cbv; intuition discriminate.

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
          (wadd_to_left_assoc : forall a b c, wadd a (wadd b c) = wadd (wadd a b) c)
          (wadd_to_right_assoc: forall a b c, wadd (wadd a b) c = wadd a (wadd b c))
          (wadd_opp: forall a, wadd a (wopp a) = ZToWord 0).

  Context (wsub_def: forall a b, wsub a b = wadd a (wopp b)).

  Context (unsigned_of_Z: forall a, 0 <= a < 2 ^ 32 -> unsigned (ZToWord a) = a).

  Context (unsigned_nonneg: forall x : word, trigger! ((unsigned x)) (0 <= unsigned x))
          (unsigned_sru_to_div_pow2: forall (x : word) (a : Z),
              0 <= a < 32 ->
              (unsigned (wsru x (ZToWord a))) = (unsigned x) / 2 ^ a)
          (unsigned_slu_to_mul_pow2: forall (x : word) (a : Z),
              0 <= a < 32 ->
              (unsigned (wslu x (ZToWord a))) = ((unsigned x) * 2 ^ a) mod 2 ^ 32).
(* BAD:
      (word_sub_add_l_same_l: forall x y : word, (wsub (wadd x y) x) = y)
      x + v - x
      gets rewritten into
      x + (x + v - x) - x
      and so on, because (x + v - x) is already present

same issue also appears without word_sub_add_l_same_l,
because wsub_def, wadd_comm, wadd_to_right_assoc together can prove this
equality as well, just in more steps
*)

  Ltac pose_const_sideconds :=
    assert (0 <= 8 < 2 ^ 32) as C1 by consts;
    assert (0 <= 3 < 32) as C2 by consts;
    assert (0 <= 4 < 32) as C3 by consts;
    assert (0 <= 2 ^ 3) as C4 by consts;
    assert (0 < 2 ^ 4) as C5 by consts;
    assert (0 < 2 ^ 32) as C6 by consts;
    assert (0 < 2 ^ 3) as C7 by consts;
    assert (2 ^ 3 < 2 ^ 4) as C8 by consts.

  Ltac pose_lib_lemmas :=
    pose proof Z.forget_mod_in_lt_l as Z_forget_mod_in_lt_l;
    pose proof (Z.mul_nonneg: forall e1 e2 : Z,
      trigger! ((e1 * e2)) (0 <= e1 -> 0 <= e2 -> 0 <= e1 * e2))
      as Z_mul_nonneg;
    pose proof (Z.div_nonneg: forall a b : Z,
      trigger! ((a / b)) (0 <= a -> 0 < b -> 0 <= a / b)) as Z_div_nonneg;
    pose proof Z.div_mul_lt as Z_div_mul_lt;
    pose proof Z.lt_from_le_and_neq as Z_lt_from_le_and_neq;
    pose proof @eq_eq_sym as H_eq_eq_sym.

  Definition bsearch_goal1 := forall (x : list word) (x1 x2 : word),
      unsigned (wsub x2 x1) = 8 * Z.of_nat (length x) ->
      unsigned (wsub x2 x1) <> 0 ->
      unsigned (wsub (wadd x1 (wslu (wsru (wsub x2 x1) (ZToWord 4)) (ZToWord 3))) x1) <
        unsigned (ZToWord 8) * Z.of_nat (length x).
  Lemma rm_annot : forall t (x:t) , x = x.
  trivial. Qed.
  Lemma bsearch_goal1_proof_with_transitivity: bsearch_goal1.
  Proof.
    unfold bsearch_goal1. intros. pose_const_sideconds. pose_lib_lemmas.
    clear Z_forget_mod_in_lt_l.
    pose proof Z.le_lt_trans as Z_le_lt_trans.
    pose proof Z.mod_le as Z_mod_le.
    egg_simpl_goal 6.
    1: exact C1.
    simpl.

    (* egg_simpl_goal 6. *)
    (* 4: exact I. *)
    (* transitivity leads to uninferrable evars! *)
  Abort.

  Lemma bsearch_goal1_proof_without_transitivity: bsearch_goal1.
  Proof.
    unfold bsearch_goal1. intros. pose_const_sideconds. pose_lib_lemmas.

    rewrite wsub_def.
    rewrite (wadd_comm x1).
    rewrite wadd_to_right_assoc.
    rewrite wadd_opp.
    rewrite wadd_0_r.
    rewrite unsigned_of_Z by exact C1.
    rewrite <- H.

    rewrite unsigned_slu_to_mul_pow2 by exact C2.
    rewrite unsigned_sru_to_div_pow2 by exact C3.

    pose proof (unsigned_nonneg (wsub x2 x1)) as p1.
    pose proof (Z_div_nonneg (unsigned (wsub x2 x1)) (2 ^ 4) p1 C5) as p2.
    pose proof (Z_mul_nonneg (unsigned (wsub x2 x1) / 2 ^ 4) (2 ^ 3) p2 C4) as p3.
    pose proof (eq_eq_sym (unsigned (wsub x2 x1)) 0) as q1.
    rewrite q1 in H0.
    pose proof (Z_lt_from_le_and_neq 0 (unsigned (wsub x2 x1)) p1 H0) as q2.
    pose proof (Z_div_mul_lt (unsigned (wsub x2 x1)) (2 ^ 3) (2 ^ 4) q2 C7 C8) as q3.
    rewrite (prove_eq_True _ (Z.forget_mod_in_lt_l _ _ _ p3 C6 q3)).
    exact Coq.Init.Logic.I.
  Qed.

  Goal True.
    let c := open_constr:(@id _ _) in inspect c.
  Abort.


  Lemma bsearch_goal1_proof_egg: bsearch_goal1.
  Proof.
    unfold bsearch_goal1. intros. pose_const_sideconds. pose_lib_lemmas.
    Time egg_simpl_goal 6.
    all: try assumption.
    simpl.
    Time egg_simpl_goal 6.
    rewrite unsigned_slu_to_mul_pow2; eauto.
    rewrite unsigned_sru_to_div_pow2; eauto.
assert (forall {t: Set} (x y : t), (x<>y) -> (y <> x)).
        {intros.
          intuition eauto. 
        }

Time egg_simpl_goal 7;  try solve [ simpl; intuition trivial].
all: egg_simpl_goal 7;  try solve [ simpl; intuition trivial].
all: egg_simpl_goal 7;  try solve [ simpl; intuition trivial].
all: egg_simpl_goal 7;  try solve [ simpl; intuition trivial].
all: egg_simpl_goal 7;  try solve [ simpl; intuition trivial].
    apply Z_forget_mod_in_lt_l; try assumption.
    (* 2:{
Time egg_simpl_goal 7; try assumption; eauto.
     } *)
    - Time egg_simpl_goal 7; try assumption; eauto; try solve [ simpl; intuition trivial].
    + Time egg_simpl_goal 7; try assumption; eauto; try solve [ simpl; intuition trivial].
    * Time egg_simpl_goal 7; simpl; try assumption; intuition trivial.
    - 

Time egg_simpl_goal 7; try assumption; try solve [ simpl; intuition trivial].
all: egg_simpl_goal 7; try assumption; try solve [ simpl; intuition trivial].
all: egg_simpl_goal 7; try assumption; try solve [ simpl; intuition trivial].
Time egg_simpl_goal 7; try assumption; eauto.
simpl.
      eapply Z_div_mul_lt; try assumption.

Time egg_simpl_goal 7; try assumption; eauto.
      + Time egg_simpl_goal 7; try assumption; eauto.
        simpl.
       

 Time egg_simpl_goal 7; try assumption; eauto;  try solve [ simpl; intuition trivial].
        assert (0 <> unsigned (wsub x2 x1) ).
{
 Time egg_simpl_goal 7; try assumption; eauto;  try solve [ simpl; intuition trivial].
}
 Time egg_simpl_goal 7; try assumption; eauto;  try solve [ simpl; intuition trivial].
 all:egg_simpl_goal 7; try assumption; eauto;  try solve [ simpl; intuition trivial].
 Time egg_simpl_goal 7; try assumption; eauto;  try solve [ simpl; intuition trivial].


        apply Z_lt_from_le_and_neq.
        * Time egg_simpl_goal 7; try assumption; eauto;  try solve [ simpl; intuition trivial].
        * Time egg_simpl_goal 7; try assumption; eauto;  try solve [ simpl; intuition trivial].







    all: try assumption.
    simpl.
    
    Time egg_simpl_goal 6.
    all: try exact I.


    Set Egg Backend "RecompilationBackend". (* makes it much slower *)
    (* Time 1: egg_simpl_goal 6. *)
    (* all: try assumption. *)
    (* all: try exact I. *)

    Set Egg Log Ignored Hypotheses.
    Set Egg Backend "FileBasedEggBackend".
    (* 1: egg_simpl_goal 6. *)
    (* all: try assumption. *)
    (* all: try exact I. *)
    Unset Egg Log Ignored Hypotheses.
    Set Egg Log Proofs.
    simpl.
    1: egg_simpl_goal 6.
    all: try assumption.
    all: try exact I.

    Set Egg Backend "FileBasedSmtBackend". (* doesn't support proofs *)
    (* clear Z_div_mul_lt. *)
    egg_cvc5.
    Set Egg Backend "FileBasedEggBackend". (* doesn't support proofs *)
    Time 1: egg_simpl_goal 6.
    Time 1: egg_simpl_goal 6.
    Time 1: egg_simpl_goal 6.
    all: try assumption.
    all: try exact I.
    Time 1: egg_simpl_goal 6.
    exact I.
  Time Qed. 0.024 secs *)

(*

constructor.
Unshelve.

(* sideconditions: *)
    all: eauto.
    rewrite unsigned_sru_to_div_pow2 by exact C3.
    pose proof (unsigned_nonneg (wsub x2 x1)) as p1.
    pose proof (Z_div_pos (unsigned (wsub x2 x1)) (2 ^ 4) p1 C5) as p2.
    pose proof (Z_mul_le (unsigned (wsub x2 x1) / 2 ^ 4) (2 ^ 3) p2 C4) as p3.
    pose proof (eq_eq_sym (unsigned (wsub x2 x1)) 0) as q1.
    rewrite q1 in H0.
    pose proof (Z_lt_from_le_and_neq 0 (unsigned (wsub x2 x1)) p1 H0) as q2.
    pose proof (Z_div_mul_lt (unsigned (wsub x2 x1)) (2 ^ 3) (2 ^ 4) q2 C7 C8) as q3.
    exact q3.
  Qed.

  Lemma bsearch_goal1_proof1: bsearch_goal1.
  Proof.
    unfold bsearch_goal1. intros. pose_const_sideconds.

    rewrite unsigned_of_Z by exact C1.
    rewrite <- H.
    rewrite word_sub_add_l_same_l.
    rewrite unsigned_slu_to_mul_pow2 by exact C2.
    rewrite unsigned_sru_to_div_pow2 by exact C3.
    rewrite (Z.le_lt_trans (unsigned (wsub x2 x1) / 2 ^ 4 * 2 ^ 3)).
    { reflexivity. }
    { rewrite Z.mod_le.
      { reflexivity. }
      { rewrite Z.mul_le.
        { reflexivity. }
        { rewrite Z.div_pos.
          { reflexivity. }
          { rewrite unsigned_nonneg. reflexivity. }
          { exact C5. } }
        { exact C4. } }
      { exact C7. } }
    rewrite Z.div_mul_lt.
    { reflexivity. }
    { rewrite Z.lt_from_le_and_neq.
      { reflexivity. }
      { apply unsigned_nonneg. }
      { rewrite (eq_eq_sym 0 (unsigned (wsub x2 x1))). exact H0. } }
    { exact C7. }
    { exact C8. }
  Qed.
*)

End WithLib.
