
Require Import Coq.Logic.PropExtensionality.

Definition qmid {A:Type} (i : A) := i.
Definition hide_qt {A:Type} (i : A) := i.
Definition hide_goal {A:Type} (i : A) := i.

Declare Custom Entry Egg.
Declare Custom Entry EggIff.
Declare Custom Entry EggGoal.
Declare Custom Entry EggNoEq.
Declare Custom Entry EggPrecond.
Declare Custom Entry EggPost.

Notation "'(@' f  a1 .. an ')'" := (.. (f a1) .. an) (in custom EggNoEq at level 0, f at level 0, a1 at level 0, an at level 0, left associativity, only printing).
Notation "'?' x" := (qmid x) (in custom EggNoEq at level 0, x at level 0, only printing, format "'?' x"). 
Notation "a" := (a) (in custom EggNoEq at level 0, a constr, only printing).

Notation "'(@and'  a b ')'" := (a /\ b) (in custom EggNoEq at level 200,  a custom EggGoal at level 200 , b custom EggGoal at level 200 , only printing).
Notation "'(@eq'  a b c ')'" := (@eq a b c) 
  (in custom EggNoEq at level 1,
  a custom EggNoEq,
  b custom EggNoEq,
  c custom EggNoEq,
   only printing).

(* Notation "'(' 'div' a b ')'" := (Z.div a b) (in custom EggNoEq at level 200,  a custom EggNoEq at level 200 , b custom EggNoEq at level 200 , only printing). *)

Notation "'(@' f  a1 .. an ')'" := (.. (f a1) .. an) (in custom Egg at level 0, f at level 0, a1 at level 0, an at level 0, left associativity, only printing).
Notation "'?' x" := (qmid x) (in custom Egg at level 0, x at level 0, only printing, format "'?' x"). 
Notation " '?FILLNAME' '=' a '=' b ',' " := (a = b) 
  (in custom EggPrecond at level 1,
  a custom EggNoEq at level 200,
  b custom EggNoEq at level 200,
   only printing).
Notation " '?FILLNAME' '=' a '=' 'True' ',' " := (a) 
  (in custom EggPrecond at level 0,
  a custom EggNoEq at level 200,
   only printing).

Notation " '?FILLNAME' '=' a "" '=>' "" b ""  " := (a = b) 
  (in custom EggPost at level 1,
  a custom EggNoEq at level 200,
  b custom EggNoEq at level 200,
   only printing).
Notation " '?FILLNAME' '=' 'True' "" '=>' "" b ""  " := (b) 
  (in custom EggPost at level 0,
  (* a custom EggNoEq at level 200, *)
  b custom EggNoEq at level 200,
   only printing).
(* Notation "a" := (a) (in custom Egg at level 0, a constr, only printing). *)

Notation " x .. y z " := (x -> .. (y -> z) ..) (in custom Egg at level 180, x custom EggPrecond at level 200, y custom EggPrecond at level 200, z custom EggPost at level 180, only printing). 
(* Notation " x y " := (x -> y) (in custom Egg at level 179, x custom EggPrecond at level 200, y custom EggPost at level 180, only printing).  *)
Notation "'/*' x .. y '*/' bdy" := (hide_qt (forall x, .. (forall y,  bdy) ..)) 
      (at level 200, x binder, y binder, bdy custom Egg at level 200, right associativity, only printing). 

Notation " a "" '=>' "" b """ := (a = b) 
  (in custom Egg at level 1,
  a custom EggNoEq at level 200,
  b custom EggNoEq at level 200,
  format " a "" '=>' "" b """,
   only printing).
Notation "a" := (a) (in custom Egg at level 0, a constr, only printing).

Notation "bdy" := (hide_qt bdy) 
      (at level 180, bdy custom Egg at level 200, right associativity, only printing).
Notation """ a "" '<=>' "" b """ := (a = b) 
  (in custom EggIff at level 1,
  a custom EggNoEq at level 200,
  b custom EggNoEq at level 200,
  format """ a "" '<=>' "" b """,
  only printing).
Notation "a" := (a) (in custom EggIff at level 0, a constr, only printing).

Notation "'(@' f  a1 .. an ')'" := (.. (f a1) .. an) (in custom EggGoal at level 0, f at level 0, a1 at level 0, an at level 0, left associativity, only printing).
Notation "'?' x" := (qmid x) (in custom EggGoal at level 0, x custom EggGoal at level 0, only printing, format "'?' x"). 
Notation "'<' bdy '>'" := (hide_goal bdy) 
      (at level 180, bdy custom EggGoal at level 200, right associativity, only printing).
Notation "a" := (a) (in custom EggGoal at level 0, a constr, only printing).
Notation "'(@and'  a b ')'" := (a /\ b) (in custom EggGoal at level 200,  a custom EggGoal at level 200 , b custom EggGoal at level 200 , only printing).
Notation "'(@eq'  a b c ')'" := (@eq a b c) (in custom EggGoal at level 200,  
                      a custom EggGoal at level 200 ,
                      b custom EggGoal at level 200 ,
                      c custom EggGoal at level 200 ,
                         only printing).

Ltac eggify_const cst := 
  lazymatch type of cst with 
  | forall x, _ => 
    let eggifyed_name := fresh x in
    constr:((forall eggifyed_name, ltac:(let yo := (eggify_const (cst (qmid eggifyed_name))) in exact yo)))
  | ?a => constr:(a)
  end.

Ltac get_quantifiers_t' t :=
  lazymatch t with
  | ?A -> ?B =>
  constr:(forall (x: True), ltac:(
        (* let body' := eval cbv beta in (t x) in *)
        let r := get_quantifiers_t' B in
        exact r))
  (* constr:(True) *)
  | forall (x: ?T), @?body x =>
      constr:(forall (x: T), ltac:(
        let body' := eval cbv beta in (body x) in
        let r := get_quantifiers_t' body' in
        exact r))
  | _ => constr:(True)
  end.

Ltac count_quantifiers' t :=
   lazymatch t with
  | ?tx -> ?a =>
    let rest := count_quantifiers' a in
    constr:(S rest)
    | _ => constr:(O)
  end.

Ltac count_quantifiers H :=
  let H := type of H in
  let t := get_quantifiers_t' H in
 let __ := match O with | _ => idtac t end in
  let t := get_quantifiers_t' t in

 let __ := match O with | _ => idtac t end in
  (* let t := eval simpl in t in *)
  let t := count_quantifiers' t in
  t.


Ltac number_to_ident n :=
  match n with 
  | O => fresh "O"
  | S ?n => 
    let rest_name := number_to_ident n in 
    fresh "S" rest_name 
  end.

Ltac eggify H :=
  match type of H with 
  | forall x, _ => 
    let count := count_quantifiers H in 
    let bouzin := (number_to_ident count) in
    let th_name := fresh "EGGTH" bouzin H in 
    let ret := (eggify_const H) in
    idtac ret;
    assert (hide_qt ret) as th_name by exact H;
    clear H
  | ?a => 
    let th_name := fresh "EGGHYP" H in 
    assert (hide_qt a) as th_name by exact H;
    clear H
  end.
Ltac eggify_goal := match goal with 
        | [|- ?g] => change g with (hide_goal g)
       end.

Lemma rew_zoom_fw{T: Type} {lhs rhs : T}:
  lhs = rhs ->
  forall P : T -> Prop, P lhs -> P rhs.
Proof.
  intros. subst. assumption.
Qed.

Lemma rew_zoom_bw{T: Type}{rhs lhs: T}:
  lhs = rhs ->
  forall P : T -> Type, P rhs -> P lhs.
Proof.
  intros. subst. assumption.
Qed.
Lemma prove_True_eq: forall (P: Prop), P -> True = P.
Proof.
  intros. apply propositional_extensionality. split; auto.
Qed.