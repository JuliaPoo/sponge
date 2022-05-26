Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Default Goal Selector "!".

Require Import Coq.Strings.String. Local Open Scope string_scope.

Inductive log_t : Type :=
| log_nil
| log_snoc {t : Type} (sofar : log_t) (elem : t).

Fixpoint append_log (l1 l2 : log_t) : log_t :=
  match l2 with
  | log_nil => l1
  | log_snoc l2' e => log_snoc (append_log l1 l2') e
  end.

Notation "'log:()'" := log_nil.
Notation "'log:(' e )" := (log_snoc log_nil e) (e at level 0, format "log:( e )").
Notation "'log:(' e1 e2 .. en )" := (log_snoc .. (log_snoc (log_snoc log_nil e1) e2) .. en)
  (e1 at level 0, e2 at level 0, en at level 0,
   format "log:( e1  e2  ..  en )").

Goal log:("v =" 42 "and T =" nat) =
           log_snoc (log_snoc (log_snoc (log_snoc log_nil "v =") 42) "and T =") nat.
  reflexivity. Abort.
Goal log:() = log_nil. reflexivity. Abort.
Goal log:(1) = log_snoc log_nil 1. reflexivity. Abort.

Module Export Temp.

Require Import PArith.
Local Open Scope positive.
Require EGraphList.
Import EGraphList.
Import EGraphList.ListNotations.
Section DeepType.
Inductive type :=
 | TBase : forall (t : positive), type
 | TArrow: type -> type -> type.

Definition lookup_type (typemap: list Type) (i: positive): Type :=
  nth (Pos.to_nat i - 1) typemap unit.

Fixpoint t_denote
  (typemap : list Type)
  (d : type) :=
  match d with
  | TBase e =>
    lookup_type typemap e
  | TArrow A B => (t_denote typemap A) -> (t_denote typemap B)
  end.

Fixpoint type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
  refine (match t1, t2 with
  | TBase n, TBase n' =>
    _ (Pos.eq_dec n n')
  | TArrow a b, TArrow a' b' =>
    _
  | _,_ => _
  end).
  {
    intros.
    destruct x.
    - left.
      subst; eauto.
    -
      right.
      intro.
      inversion H.
      contradiction.
  }
  {
    right.
    intro.
    inversion H.
  }
  {
    right.
    intro.
    inversion H.
  }
  {
    pose proof type_eq_dec as H.
    specialize (type_eq_dec a a').
    specialize (H b b').
    destruct H.
    -
      destruct type_eq_dec.
      +
        subst.
        left; eauto.
      +
        subst.
        right.
        intro.
        inversion H.
        eauto.
    -
        right.
        intro.
        inversion H.
        eauto.
  }
  Defined.

Fixpoint type_eqb (t1 t2 : type) : bool :=
match t1, t2 with
| TBase n, TBase n' =>
  Pos.eqb n n'
| TArrow a b, TArrow a' b' =>
  type_eqb a a' && type_eqb b b'
| _,_ => false
end.

Definition type_eqb_correct : forall (t1 t2 : type),
  type_eqb t1 t2 = true -> t1 = t2.
  induction t1.
  - cbn.
    destruct t2.
    {
      rewrite Pos.eqb_eq.
      intros; eauto.
      intros; inversion H.
      eauto.
    }
    discriminate 1.
  -
      cbn.
      intros.
      destruct t2;
      try inversion H; clear H.
      cbn in *.
      eapply Bool.andb_true_iff in H1.
      destruct H1.
      specialize IHt1_1 with (1:= H).
      specialize IHt1_2 with (1:= H0).
      rewrite IHt1_1.
      rewrite IHt1_2.
      eauto.
Qed.

End DeepType.

Notation "A '~>' B" := (TArrow A B) (right associativity, at level 20).
Notation "'`' A " := (TBase A) (at level 1, format "'`' A").

Eval simpl in (t_denote [nat] `1).
Eval simpl in (t_denote [nat : Type; Prop] (`1 ~> `2)).

Inductive term : type -> Type :=
    | TApp: forall {t td},
      term (t ~> td) ->
      term t ->
      term td
    | TVar : forall (n : positive) (t: type),
      term t
    | TConst : forall (n : positive) (t: type),
      term t.

Fixpoint term_eqb {t1 t2} (f1 : term t1) (f2 : term t2) : bool :=
  match f1, f2 with
  | TApp a b, TApp a' b' =>
    andb (term_eqb a a') (term_eqb b b')
  | TConst n t, TConst n' t' =>
  (* TODO maybe call type_eqb *)
    match type_eq_dec t t' with
    | left _ =>
      Pos.eqb n n'
    | right _ => false
    end
| TVar n t, TVar n' t' =>
  (* TODO maybe call type_eqb *)
    match type_eq_dec t t' with
    | left _ =>
      Pos.eqb n n'
    | right _ => false
    end
  | _, _ => false
  end.

Lemma term_eqb_same_type : forall {t1} (f1 : term t1) {t2} (f2 : term t2),
  term_eqb f1 f2 = true -> t1 = t2.
  induction f1.
  2:{
    intros; eauto.
    cbn in H.
    destruct f2 eqn:?; try inversion H; clear H.
    destruct (type_eq_dec) ; eauto.
    inversion H1.
  }
  {
    cbn.
    intros.
    destruct f2 eqn:?; try inversion H; clear H.
    eapply andb_prop in H1.
    destruct H1.
    specialize (IHf1_1 _ _ H).
    inversion IHf1_1.
    eauto.
  }
  {
    intros; eauto.
    cbn in H.
    destruct f2 eqn:?; try inversion H; clear H.
    destruct (type_eq_dec) ; eauto.
    inversion H1.
  }
  Qed.

Lemma term_eqb_eq : forall {t} (f1 : term t) (f2 : term t),
  term_eqb f1 f2 = true -> f1 = f2.
  induction f1.
  2:{
    intros; eauto.
    cbn in H.
    destruct f2 eqn:?; try inversion H; clear H.
    destruct (type_eq_dec) ; eauto.
    + eapply Pos.eqb_eq in H1.
      congruence.
    +
      discriminate.
  }
  {
    cbn.
    intros.
    destruct f2 eqn:?; try inversion H; clear H.
    eapply andb_prop in H1.
    destruct H1.
    pose (term_eqb_same_type _ _ H).
    inversion e.
    subst.
    specialize (IHf1_1 _  H).
    subst.
    specialize (IHf1_2 _  H0).
    subst.
    eauto.
  }
  {
    intros; eauto.
    cbn in H.
    destruct f2 eqn:?; try inversion H; clear H.
    destruct (type_eq_dec) ; eauto.
    + eapply Pos.eqb_eq in H1.
      congruence.
    +
      discriminate.
  }
  Qed.

Inductive dyn {typemap : list Type} :=
  mk_dyn { dyn_type : type ;
    dyn_val : t_denote typemap dyn_type }.
Arguments dyn : clear implicits.

Check mk_dyn [positive] `1 3.

Inductive hlist  : list Type -> Type :=
| HCons : forall (t : Type)
            (v : t)
            {tcdr : list Type} (cdr : hlist tcdr),
    hlist (t :: tcdr)
| HNil : hlist (nil : list Type).

Fixpoint hlist_nth (l : list Type) n T (pf : nth_error l n = Some T)
  (hl : hlist l) : T.
  destruct l.
  {
    destruct n; discriminate.
  }
  {
    inversion hl.
    subst.
    destruct n; simpl in *.
    - inversion pf.
      subst; exact v.
    -
      eapply hlist_nth.
      + exact pf.
      + exact cdr.
  }
Defined.

Fixpoint hlist_update_nth {l : list Type } (n : nat) (dl : hlist l) t
         (pf : nth_error l n = Some t) (e : t) {struct l} : hlist l.
  destruct l.
  - intros.
    destruct n; discriminate.
  - inversion dl.
    destruct n; simpl in *.
    + econstructor.
      * inversion pf.
        subst; exact e.
      * exact cdr.
    + subst.
      econstructor.
      * exact v.
      * eapply hlist_update_nth.
        ++ exact cdr.
        ++ exact pf.
        ++ exact e.
Defined.

(* (homogeneous) list whose length matches the length of another list *)
Definition llist{A: Type}(B: Type)(l: list A): Type := hlist (map (fun _ => B) l).

Definition llist_nth_error {A B : Type} {l : list A} (ll : llist B l)
           (n : positive) : option B.
  destruct (nth_error l (Pos.to_nat n - 1)) eqn: E.
  - eapply map_nth_error with (f := fun _ => B) in E.
    exact (Some (hlist_nth _ _ _ E ll)).
  - exact None.
Defined.

Definition llist_update_nth {A B : Type} {l : list A} (ll : llist B l)
           (n : positive) (b : B) : llist B l.
  destruct (nth_error l (Pos.to_nat n - 1)) eqn: E.
  - eapply map_nth_error with (f := fun _ => B) in E.
    exact (hlist_update_nth (Pos.to_nat n - 1) ll _ E b).
  - exact ll. (* out of bounds *)
Defined.

  Fixpoint hlist_app {l :list Type} (hl : hlist l) {r :list Type} (hr : hlist r) :
  hlist (l ++ r).
  destruct l.
  {
    exact hr.
  }
  {
    simpl.
    inversion hl.
    subst.
    econstructor.
    - exact v.
    - exact (hlist_app _ cdr _ hr).
  }
  Defined.

  Definition hlist_snoc {l :list Type} (hl : hlist l) {T : Type} (t : T) :
  hlist (l ++ [T]) := hlist_app hl (HCons T t HNil).

Section wf_term.
Context (typemap : list Type) (constmap : list (dyn typemap)) (types_of_varmap : list type).
Fixpoint wf_term {t : type} (a : term t) :=
  match a with
  | TApp fn arg =>
    andb (wf_term fn) (wf_term arg)
  | TVar n t =>
    match nth_error types_of_varmap (Pos.to_nat n - 1) with
    | Some d =>
      if (type_eq_dec d t) then true else false
    | None =>
      false
    end
  | TConst n t =>
    match nth_error constmap (Pos.to_nat n - 1) with
    | Some d =>
      if type_eq_dec (dyn_type d) t then true else false
    | None =>
      false
    end
  end.
End wf_term.
Definition computable_andb_true_iff :=
  fun b1 b2 : bool =>
  if b2 as b return ((b1 && b)%bool = true <-> b1 = true /\ b = true)
  then
   if b1 as b return ((b && true)%bool = true <-> b = true /\ true = true)
   then
    conj (fun _ : true = true => conj eq_refl eq_refl)
    (fun H : true = true /\ true = true =>
       and_ind (fun _ _ : true = true => eq_refl) H)
    :
    (true && true)%bool = true <-> true = true /\ true = true
   else
    conj (fun H : false = true => conj H eq_refl)
      (fun H : false = true /\ true = true =>
       and_ind (fun (H0 : false = true) (_ : true = true) => H0) H)
    :
    (false && true)%bool = true <-> false = true /\ true = true
  else
   if b1 as b return ((b && false)%bool = true <-> b = true /\ false = true)
   then
    conj (fun H : false = true => conj eq_refl H)
      (fun H : true = true /\ false = true =>
       and_ind (fun (_ : true = true) (H1 : false = true) => H1) H)
    :
    (true && false)%bool = true <-> true = true /\ false = true
   else
    conj (fun H : false = true => conj H H)
      (fun H : false = true /\ false = true =>
       and_ind (fun _ H1 : false = true => H1) H)
    .
Section weaken_wf_term.
Context (typemap : list Type) (constmap : list (dyn typemap)) .
Lemma weaken_varmap_wf_term {t : type} (a : term t)
(types_of_varmap : list type)
(ext: list type):
  wf_term typemap constmap types_of_varmap a = true ->
  wf_term typemap constmap (types_of_varmap ++ ext) a = true .
  induction a;eauto.
  {
    simpl.
    intros.
    eapply computable_andb_true_iff in H.
    destruct H.
    erewrite IHa1; eauto.
  }
  {
    simpl. intros.
    erewrite (nth_error_app1).
    - exact H.
    -
      destruct (nth_error) eqn:? in H; try discriminate.
      assert (nth_error types_of_varmap (Pos.to_nat n - 1) <> None) by congruence.
      eapply nth_error_Some in H0.
      eauto.
  }
  Defined.

End weaken_wf_term.

Section interp_term.
Context (typemap : list Type) (constmap : list (dyn typemap)) (types_of_varmap : list type).
Context (varmap : hlist (map (t_denote typemap) types_of_varmap)).

Definition interp_term {t : type} (a : term t) (wf : wf_term typemap constmap types_of_varmap a = true)
: t_denote typemap t.
 induction a.
 -
  simpl in *.
  eapply computable_andb_true_iff in wf.
  destruct wf.
  specialize (IHa1 H).
  specialize (IHa2 H0).
  exact (IHa1 IHa2).
-
  simpl in wf.
  destruct nth_error eqn:? in wf.
  2:{ discriminate. }
  (* destruct wf. *)
  destruct (type_eq_dec) in wf.
  2:{ discriminate. }
  simpl in e.
  rewrite e in Heqo.
  pose (hlist_nth (map (t_denote typemap) types_of_varmap) (Pos.to_nat n -1) (t_denote typemap t)).
  eapply t1.
  2:{ exact varmap. }
  eapply map_nth_error.
  exact Heqo.
-
  simpl in wf.
  destruct nth_error in wf.
  2:{ discriminate. }
  destruct d.
  destruct type_eq_dec in wf.
  2:{ discriminate. }
  simpl in e.
  rewrite e in dyn_val0.
  exact dyn_val0.
  Defined.

End interp_term.
Ltac CASE l ret :=
let __ := match O with
| _ => assert_succeeds l
end in ret.



Ltac inList e l :=
  lazymatch l with
  | nil =>
  false
  | cons ?t ?l =>
    let res := match O with
    | _ =>
    CASE ltac:(
      first [constr_eq e t ]
      ) true
    | _ =>
    inList e l
    end in res
  end.

Ltac indexList e l :=
  match l with
  | nil => constr:(false)
  | cons e _ => constr:(O%nat)
  | cons _ ?l =>
    let n := indexList e l in
    constr:((S n)%nat)
  end.


Ltac indexDynList e l :=
  match l with
  | nil => constr:(false)
  | cons {| dyn_type := ?t; dyn_val := e|} _  => constr:((O%nat, t))
  | cons _ ?l =>
    match indexDynList e l with
    | false => constr:(false)
    | (?n, ?res) =>
    constr:(((S n)%nat, res))
    end
  end.

Ltac indexHList e l :=
  lazymatch l with
  | HNil => constr:(false)
  | HCons _ e _ => constr:(O%nat)
  | HCons _ _ ?l =>
    lazymatch indexHList e l with
    | false => constr:(false)
    | ?n =>
    constr:((S n)%nat)
    end
  end.

Ltac eval_snoc l e := eval cbv [app] in (app l (cons e nil)).

Ltac addList e l :=
  let member := inList e l in
 (* let __ := match O with | _ => idtac "addlist" e l member end in *)
  match member with
  | true => l
  | false => eval_snoc l e
  end.

Definition index := nat.

Ltac reify_type tmap t :=
  match t with
  | ?a -> ?b =>
    let s1 := reify_type tmap a in
    let s2 := reify_type tmap b in
    constr:(s1 ~> s2)
  | _ =>
    let dt := indexList t tmap in
    let idx := eval cbv in (Pos.of_nat (1 + dt)) in
     constr:(TBase idx)
  end.

Ltac extend_constmap_with_const tmap acc expr :=
  (* Can fail if expr does not have a type that can be expressed in tmap *)
  let t := type of expr in
  let tmap' := eval unfold tmap in tmap in
  let deeply_represented := reify_type tmap' t in
  addList {| dyn_type := deeply_represented ; dyn_val := expr : (t_denote tmap deeply_represented)|} acc.

Ltac extend_constmap tmap varmap acc expr :=
  lazymatch expr with
  | ?a ?b  =>
    let ta := type of a in
    lazymatch ta with
    |  ?A -> ?B =>
      let acc := extend_constmap tmap varmap acc a in
      let acc := extend_constmap tmap varmap acc b in
      acc
    | _ =>
      extend_constmap_with_const tmap acc expr
    end
  | ?a =>
    (* Decide if var of const*)
    (* let __ := match constr:(O) with _ => idtac "hlist:" varmap "a:" a end in *)
    lazymatch indexHList a varmap with
    | false =>
      extend_constmap_with_const tmap acc expr
    | _ => acc
    end
  end.

Ltac extend_typemap_with_t acc t :=
  match t with
  | ?a -> ?b =>
      let acc' := extend_typemap_with_t acc a in
      let acc'' := extend_typemap_with_t acc' b in
      acc''
  | ?a =>
    addList (a : Type) acc
  end.

Ltac extend_typemap acc expr :=
  lazymatch expr with
  | ?a ?b  =>
    let ta := type of a in
    let tb := type of b in
    (* let __ := match O with | _ => idtac "extend with a" "(" a ":" ta ")" " b" "(b" ":" tb ")" "acc" acc end in *)
    let texpr := type of expr in
    (* let __ := match O with | _ => idtac "try to extend by one with " "(" expr ":" texpr ")" "acc" acc end in *)
    let acc := extend_typemap_with_t acc texpr in
    (* let __ := match O with | _ => idtac "extended" end in *)
    lazymatch type of a with
    | ?A -> ?B =>
      let acc' := extend_typemap acc a in
      let acc'' := extend_typemap acc' b in
      acc''
    | _ => acc
    end
  | ?a =>
    let ta := type of a in
    extend_typemap_with_t acc ta
  end.




Goal forall A C (B : (nat -> Prop) -> Prop) E ( D:Prop),
  A /\ (B E) \/ C -> False.
  intros.
  let t := type of H in
  let tmap'  := extend_typemap (nil : list Type) t in
  let tmap := fresh "tmap" in
  pose tmap' as tmap;
  let map := extend_constmap tmap (HNil) (nil : list (dyn tmap)) t in
  idtac tmap;
  idtac map.
  Abort.

Goal forall (l : Coq.Init.Datatypes.list nat),
  Coq.Init.Datatypes.app l l = Coq.Init.Datatypes.nil -> False.
  intros.
  let t := type of H in
  let tmap' := extend_typemap (nil : list Type) t in
  let tmap := fresh "tmap" in
  pose tmap' as tmap;
  let map := extend_constmap tmap HNil (nil : list (dyn tmap)) t in
  idtac tmap;
  idtac map.
  Abort.

Ltac reify_constant typemap constmap expr :=
  (* let __ := match O with | _ => idtac "Searching for constant" expr "in" constmap  end in *)
  match indexDynList expr constmap with
  | false =>
    fail "Did not find constant" expr "in constmap" constmap
  | (?n, ?t) =>
    let n := eval cbv in (Pos.of_nat (1 + n)) in
    constr:(TConst n t)
  end.

Ltac reify_expr typemap constmap types_of_varmap varmap expr :=
lazymatch expr with
 | ?a ?b =>
    let ta := type of a in
    let tb := type of b in
    (* let __ := match O with | _ => idtac "Try to reify " "a : (" a ":" ta ")" " b :" "(" b ":" tb ")"  end in *)
    lazymatch type of a with
    | ?A -> ?B =>
      let ra := reify_expr typemap constmap types_of_varmap varmap a in
      (* let __ := match O with | _ => idtac "successfully reifed a" a "by" ra  end in *)
      let rb := reify_expr typemap constmap types_of_varmap varmap b in
      (* let __ := match O with | _ => idtac "successfully reifed b" b "by" rb  end in *)
      let res := constr:(TApp ra rb) in
      (* let __ := match O with | _ => idtac "app worked resulting in res" res end in *)
      res
    | _ =>
    (* let __ := match O with | _ => idtac "Found an atomic application" expr end in *)
    reify_constant typemap constmap expr
    end
| ?a =>
  lazymatch indexHList expr varmap with
  | false =>
  (* It is not a quantifier *)
    (* let __ := match O with | _ => idtac "Reifing a constant" expr  end in *)
    reify_constant typemap constmap expr
  | ?n =>
    let t := eval cbv in (nth n types_of_varmap `1) in
    let n := eval cbv in (Pos.of_nat (1 + n)) in
    constr:(TVar n t)
  end
end.

Goal forall (l : Coq.Init.Datatypes.list nat),
  Coq.Init.Datatypes.app l l = Coq.Init.Datatypes.nil -> False.
  intros.
  Time let t := type of H in
  let tmap := extend_typemap (EGraphList.nil : EGraphList.list Type) t in
  pose tmap as ltm;
  let map := extend_constmap ltm HNil (EGraphList.nil : EGraphList.list (dyn ltm)) t in
  pose map;
  let tH := type of H in
  let rH := reify_expr tmap map (nil : list type) HNil tH in
  pose rH.
  Abort.

Require Import Enodes.
Require Import Lia.
Section egraphs.

  Definition eclass_id := positive.
  Definition idx_constmap := positive.
  Definition uf_t := PTree.t eclass_id.

  Definition init_uf : uf_t := PTree.empty _.
  Definition find (uf : uf_t) (x : eclass_id) := match PTree.get x uf with | Some y => y | None => x end.
  Definition union (g : uf_t) (x y : eclass_id ) : uf_t :=
    let px := find g x in
    let py := find g y in
    PTree.map_filter (fun el => let cel := find g el in if Pos.eq_dec cel px then Some py else Some cel) g.

  Inductive enode : Type :=
    | EApp: eclass_id -> eclass_id -> enode
    | EConst: forall (n: idx_constmap), enode.

  Definition map_enode_to_eid :=
      (PTree.t (enode * eclass_id) *
      (* Map EConst to eclass_id, the returned enode is the key *)
      (PTree.t (PTree.t (enode * eclass_id)))
      (* Map EApp to eclass_idm the returned enode is the key *)
      )%type.

  Definition lookup' (m : map_enode_to_eid) (n : enode) : option (enode * eclass_id) :=
    let '(atms, fs) := m in
    match n with
    | EApp f arg =>
        match PTree.get f fs with
        | Some snd_level_map => PTree.get arg snd_level_map
        | None => None
        end
    | EConst idx => PTree.get idx atms
    end.

  Definition lookup_non_canonical (m : map_enode_to_eid) (n : enode) : option eclass_id:=
     match lookup' m n with
    | Some res => Some (snd res)
    | None => None
     end.

  Definition add_enode (m : map_enode_to_eid) (n : enode) (e : eclass_id) : map_enode_to_eid :=
    match lookup_non_canonical m n with
    | Some _ => m
    | None =>
      let '(atms, fs) := m in
      match n with
      | EApp f arg =>
          let args := match PTree.get f fs with
              | Some snd_level_map => snd_level_map
              | None => PTree.empty _
               end
          in
          let newargs := PTree.set arg (n,e) args in
          (atms, PTree.set f newargs fs)
      | EConst idx => (PTree.set idx (n,e) atms, fs)
      end
    end.


  Definition set_enodes :=
      (* Set of EAtoms idx_varmap and Set of EApp1 eclass_id eclass_id *)
      (PTree.t idx_constmap *
      (* We keep the eclass_id instead of tt. This is because we don't have map_with_keys, so we keep the key int he value *)
      PTree.t (PTree.t (eclass_id * eclass_id))
      (* Similarly here we keep the pair of eclass_id, to represent the set of enodes of the form EApp1 idx_body idx_arg *)
      )%type.

  Definition add_enode_set (m : set_enodes) (n : enode) :=
      let '(atms, fs) := m in
      match n with
      | EApp f arg =>
          let args := match PTree.get f fs with
              | Some snd_level_map => snd_level_map
              | None => PTree.empty _
               end
          in
          let newargs := PTree.set arg (f,arg) args in
          (atms, PTree.set f newargs fs)
      | EConst idx => (PTree.set idx idx atms, fs)
    end.

  Definition map_eid_to_set_of_enode :=
    (* Set of enodes of each eclass_id *)
    PTree.t (eclass_id * type * set_enodes).

  Record egraph := {
    max_allocated : positive;
    (* eclass_id -> eclass_id *)
    uf : uf_t;
    (* enode -> eclass_id *)
    n2id : map_enode_to_eid;
    (* eclass_id -> Set enode *)
    id2s : map_eid_to_set_of_enode;
    (* for debugging: *)
    log : log_t;
  }.

  Definition print (msg : log_t) (e : egraph) : egraph :=
    match e with
    | Build_egraph max_allocated uf n2id id2s log =>
      Build_egraph max_allocated uf n2id id2s (append_log log msg)
    end.

  Definition canonicalize (e : egraph) (node : enode) : enode
  :=
    match node with
    | EApp f a =>
      let f := find (uf e) f in
      let a := find (uf e) a in
      EApp f a
    | a => a
    end.

  Definition lookup (e : egraph) (node : enode) : option eclass_id :=
    match lookup_non_canonical (n2id e) (canonicalize e node) with
    | Some to_canon => Some (find (uf e) to_canon)
    | None => None
    end.

  (* Invariant, we always merge stuff that are already present in the egraph *)
  (* So we don't consider the case where one of the two eclass has an empty set. *)
  Definition merge_id2s (e1 e2 : eclass_id) (m : map_eid_to_set_of_enode) : map_eid_to_set_of_enode :=
    (* e2 is the new canonical representant *)
    match (PTree.get e1 m), (PTree.get e2 m) with
    | Some (eid1, tl, (set_eatoms_l, set_eapp_l)), Some (eid2, tr, (set_eatoms_r, set_eapp_r)) =>
      if type_eq_dec tl tr then
        let newatoms :=
          PTree.merge_l set_eatoms_l set_eatoms_r in
        let newapps :=
          PTree.merge_with set_eapp_l set_eapp_r PTree.merge_l in
        PTree.set e2 (eid2, tl, (newatoms, newapps)) m
      else
        m
    | _, _  => m
    end.

  Definition merge_n2id (e1 e2 : eclass_id) (m : map_enode_to_eid ) : map_enode_to_eid :=
    let '(atms, apps) := m in
    (* EApp e1 e3 -> e143
    Add
       EApp e2 e3 -> e143
    No need to modify
       EConst n -> e1
    *)
    let eapp_gather_to_change := PTree.tree_fold_preorder (fun acc val  =>
    PTree.tree_fold_preorder (fun acci '(enode,eid) =>
                                    match enode with
                                    | EApp a b =>
                                      let one_e1 := orb (Pos.eqb a e1) (Pos.eqb b e1) in
                                      if one_e1 then
                                      let newa := if Pos.eqb a e1 then e2 else a in
                                      let newb := if Pos.eqb b e1 then e2 else b in
                                      (EApp newa newb, eid)::acci
                                      else acci
                                    | _ => acci
                                    end) val acc) apps nil in
    EGraphList.fold_left (fun acc '(enode,eid) =>
    add_enode acc enode eid
    ) eapp_gather_to_change m
    .

  Definition merge (e : egraph) (e1 e2 : eclass_id) := {|
    max_allocated := max_allocated e;
    uf := union (uf e) e1 e2;
    n2id := merge_n2id e1 e2 (n2id e);
    id2s := merge_id2s e1 e2 (id2s e);
    log := append_log (log e) log:("Merged" e1 "and" e2 ";");
  |}.

  Definition empty_egraph := {|
    max_allocated := 1;
    uf := init_uf;
    n2id := (PTree.empty _, PTree.empty _);
    id2s := PTree.empty _;
    log := log:();
  |}.

  Section WithVars.
    Context {types_of_varmap : list type}
            (var_instantiations : llist eclass_id types_of_varmap).

    (* Always returns a canonical eid *)
    Fixpoint lookup_term {t} (f : term t) (e : egraph) : option (eclass_id) :=
      match f with
      | TApp e1 e2 =>
          match lookup_term e1 e, lookup_term e2 e with
          | Some e1, Some e2 =>
              let fnode := EApp e1 e2 in
              lookup e fnode
          | _, _ => None
          end
      | TConst n _t => lookup e (EConst n)
      | TVar n _t =>
          match llist_nth_error var_instantiations n with
          | Some to_canon => Some (find (uf e) to_canon)
          | None => None
          end
      end.

    (* Always returns a canonical eid (which allows the implementation of
       merge to be simpler because it doesn't have to canonicalize the
       results of add_term) *)
    Fixpoint add_term (e : egraph) {t} (f : term t) : (egraph * eclass_id).
      refine (
      match f with
      | TVar n t => _
      | TApp f1 f2 =>
        let '(e, fid) := add_term e _ f1 in
        let '(e, arg1id) := add_term e _ f2 in
        match lookup e (EApp fid arg1id) with
        | Some a => (e, a)
        | None =>
        let eid_newterm := max_allocated e in
        ({|
        max_allocated := eid_newterm + 1;
        uf := PTree.set eid_newterm eid_newterm (uf e);
        (* The following canonicalize is unecessary but helps in the proof *)
        n2id := add_enode (n2id e) (canonicalize e (EApp fid arg1id)) eid_newterm;
        id2s := PTree.set eid_newterm (eid_newterm, t, (add_enode_set (PTree.empty _, PTree.empty _)
        (canonicalize e (EApp fid arg1id)))) (id2s e);
        log := log e|}, eid_newterm)
        end
      | TConst n _t =>
         match lookup_term f e with
        | Some a => (e, a)
        | None =>
        let eid_newterm := max_allocated e in
        ({|
        max_allocated := eid_newterm + 1;
        uf := PTree.set eid_newterm eid_newterm (uf e);
        n2id := add_enode (n2id e) (EConst n) eid_newterm;
        id2s := PTree.set eid_newterm
                          (eid_newterm, t, (add_enode_set (PTree.empty _, PTree.empty _) (EConst n)))
                          (id2s e);
        log := log e|}, eid_newterm)
        end
      end).
      exact (match llist_nth_error var_instantiations n with
              (* Invariant: it is always the case that the varmap contains eclass_ids that
                 were already in the egraph, BUT they might not be canonical *)
             | Some id => (e, find (uf e) id)
             | None => (e, 1) (* ruled out by wf_term *)
             end).
    Defined.
  End WithVars.

  Definition merge_terms {t} (e : egraph) (f : term t) (g : term t) : egraph * eclass_id * eclass_id :=
    (* One of the two returned eid become non-canonical and should not be returned *)
    let '(newe, fid) := @add_term [] HNil e _ f in
    let '(newe', gid) := @add_term [] HNil newe _ g in
    (merge newe' fid gid, fid, gid).

  Definition classIsCanonical e (n : eclass_id) :=
    find (uf e) n = n.

  Definition n2idCanonical e  := forall f (c : eclass_id),
    lookup e f = Some c ->
    classIsCanonical e c.


(* We stopped HERE *)
         (* if t = Prop then *)
          (* interp_formula ctx f <-> interp_formula ctx g; *)
        (* else  *)

  Context {typemap : list Type}.
  Context {constmap : list (dyn typemap)}.
  (* Context {varmap : list (dyn typemap)}. *)
  Record invariant_egraph {e} : Prop := {
      correct: forall t (f g : term t) (eid : eclass_id)
      (wf_f : wf_term typemap constmap [] f = true)
      (wf_g : wf_term typemap constmap [] g = true),
      @lookup_term [] HNil _ f e = Some eid ->
      @lookup_term [] HNil _ g e = Some eid ->
     interp_term typemap constmap [] HNil f wf_f = interp_term typemap constmap [] HNil g wf_g;

    canonical_witness : forall eid,
    (* such that eid is allocated *)
        eid < max_allocated e ->
    (* and eid is canonical*)
      find (uf e) eid = eid ->
      (* There exists a term represented by that class *)
      match PTree.get eid (id2s e) with
      | None => False
      | Some (_, tp, _) =>
        exists (t : term tp), @lookup_term [] HNil _ t e = Some eid /\
                                  wf_term typemap constmap [] t = true
                                  end;

      nobody_outside :
       forall a (eid : eclass_id),
          lookup e a = Some eid ->
           (eid < max_allocated e)%positive;

      no_args_eapp1_outside :
        forall (eid : eclass_id)
                (e1 : eclass_id)
                (e2 : eclass_id)
                ,
          lookup e (EApp e1 e2) = Some eid ->
          (find (uf e) e1 < max_allocated e)%positive /\
          (find (uf e) e2 < max_allocated e)%positive;

      sanely_assigned_lookup :
            n2idCanonical e;

      uf_id_outside :
        forall (a: eclass_id), (a >= max_allocated e)%positive ->
          classIsCanonical e a;

      wt_egraph:
        forall {t1 t2} (f : term t1) (g : term t2) (c : eclass_id)
        (wf_f : wf_term typemap constmap [] f = true)
        (wf_g : wf_term typemap constmap [] g = true),
        @lookup_term [] HNil _ f e = Some c ->
        @lookup_term [] HNil _ g e = Some c ->
        t1 = t2;

      wf_uf:
        forall (c : eclass_id),
          (c < max_allocated e)%positive ->
          (find (uf e) c < max_allocated e)%positive;
      }.

  Global Arguments invariant_egraph : clear implicits.
  Lemma add_term_safe : forall {t} (f : term t) e ,
    invariant_egraph e ->
    let '(newe, _eid) := @add_term [] HNil e _ f in
    invariant_egraph newe.
       Admitted.

  Lemma type_preserved : forall {t1}  (f1 : term t1) {t2 t} (f g : term t)
        (f2 : term t2) e n0 n1 n2,
      invariant_egraph e ->
      wf_term typemap constmap [] f = true ->
      wf_term typemap constmap [] g = true ->
      wf_term typemap constmap [] f1 = true ->
      wf_term typemap constmap [] f2 = true ->
      @lookup_term [] HNil _ f e = Some n0 ->
      @lookup_term [] HNil _ g e = Some n1 ->
      @lookup_term [] HNil _ f1 (merge e n0 n1) = Some n2 ->
      @lookup_term [] HNil _ f2 (merge e n0 n1) = Some n2 ->
      t1 = t2.
      Admitted.

  Theorem merge_preserve : forall {t} (e : egraph) (f g : term t)
    (wf_f : wf_term typemap constmap [] f = true)
    (wf_g : wf_term typemap constmap [] g = true),
    invariant_egraph e ->
    interp_term typemap constmap [] HNil f wf_f = interp_term typemap constmap [] HNil g wf_g ->
    let '(newe, before_merge_f, before_merge_g) := merge_terms e f g in
    invariant_egraph newe.
    Admitted.
End egraphs.

Section TcVarmap.
  Context (e: egraph).

  Definition typecheck_eid(eid: eclass_id)(expected_type: type): bool :=
    match PTree.get eid (id2s e) with
    | Some (_, actual_type, _) => type_eqb actual_type expected_type
    | None => false
    end.

  Fixpoint typecheck_varmap{types_of_varmap : list type}
           (varmap: llist (eclass_id) types_of_varmap): bool.
    unfold llist in varmap.
    destruct types_of_varmap. 1: exact true.
    inversion varmap. subst.
    refine (andb (typecheck_eid v t) _).
    exact (typecheck_varmap types_of_varmap cdr).
  Defined.
End TcVarmap.

Arguments invariant_egraph : clear implicits.

(* Note we need to make sure that types are uniquely put in the list, no duplicate! *)
(* Tests local:
En partant d'un egraph vide, ajouter quelques noeuds, et query le graph.
Voir si on peut reduire les ensembles d'une manière qui soit utilisable.

Voir si on peut reconstruire une Formula depuis un enode.
Grace au type deeply embedded, et la recursion sur les TArrows,
je crois qu'une telle recursion devcrait etre possible structurellement. *)
Lemma empty_invariant typemap constmap:
  invariant_egraph typemap constmap empty_egraph.
Admitted.

Fixpoint propose_term {typemap}
   (constmap : list (dyn typemap))
   (e : egraph) (fuel : nat)
   (current_class : eclass_id)
   (t : type)
   : option (term t).
  unshelve refine(match fuel with
  | O => None
  | S fuel =>
     match PTree.get current_class (id2s e) with
     | None => None
     | Some (eid, t', (set_consts, set_eapp)) =>
      _
     end
  end).
  unshelve refine (let option_const := PTree.tree_any set_consts in
                          _).
  destruct option_const.
  {
    destruct (type_eq_dec t' t).
    {
      subst.
      exact (Some (TConst i t)).
    }
    {
      (* Type query is inconsistent, we can stop looking *)
      exact None.
    }
  }
  {
    (* Did not find a constant, but there might be applications *)
    unshelve refine (let option_app := PTree.tree_any set_eapp in
                          _).
    destruct option_app.
    2:{
      (* No app found in the set represented by the class *)
      exact None.
    }
    {
      (* Here we returned any eapp, in the following example, we may run out of fuel trying to construct wrongly
        and infinite term while there exist a finite one :
          2 :: 1 :: x = 1 :: x
          find_term (class_of 1::x)
          may generate (2 :: 2 :: 2 :: 2 :: ....), so run out of fuel and return None,
          even though (1::x) was a finite answer
           *)
        destruct (PTree.tree_any t0) as [[subclass1 subclass2]| ].
        2:{
          (* Impossible case, this map should never be empty *)
          exact None.
        }
        {
          destruct (PTree.get subclass2 (id2s e)) as [[[_ t_subclass2] _]|].
          2:{
            exact None.
          }
          {
            pose (propose_term typemap constmap e fuel subclass2 t_subclass2) as term_arg.
            pose (propose_term typemap constmap e fuel subclass1 (t_subclass2 ~> t)) as term_fn.
            destruct term_fn.
            2:{ exact None. }
            destruct term_arg.
            2:{ exact None. }
            exact (Some (TApp t1 t2)).
          }
        }
    }
  }
  Defined.

Section TheoremGenerator.
  Context {typemap : list Type}.
  Context {constmap: list (dyn typemap)}.

  Fixpoint generate_theorem'
    (* Environment *)
    (types_of_varmap : list type)
    (varmap : hlist (map (t_denote typemap) types_of_varmap))
    (* Things to reify *)
    (types_of_varmap_remaining: list type)
    (t : type)
    (clc1 : term t)
    (clc2 : term t)
    (* wf hypothesis: *)
    (wf_clc1 : wf_term typemap constmap (types_of_varmap ++ types_of_varmap_remaining) clc1 = true)
    (wf_clc2 : wf_term typemap constmap (types_of_varmap ++ types_of_varmap_remaining) clc2 = true)
    : Type .
    destruct types_of_varmap_remaining as [| t_var types_of_varmap_remaining].
    -
      rewrite app_nil_r in wf_clc1.
      rewrite app_nil_r in wf_clc2.
      exact (interp_term typemap constmap types_of_varmap varmap clc1 wf_clc1 =
             interp_term typemap constmap types_of_varmap varmap clc2 wf_clc2).
    -
      refine (forall (x : t_denote typemap t_var), (_:Type)).
      pose (hlist_snoc varmap x).
      change ([t_denote typemap t_var]) with (map (t_denote typemap)[t_var]) in h.
      rewrite <- map_app in h.
      refine (generate_theorem'
                (types_of_varmap ++ (cons t_var nil))
                h
                types_of_varmap_remaining
                t clc1 clc2 _ _
                ).
      + rewrite <- app_assoc.
      eauto.
      + rewrite <- app_assoc.
      eauto.
    Defined.

 Definition generate_theorem
    (types_of_varmap : list type)
    {t : type}
    (clc1 : term t)
    (clc2 : term t)
    (* wf hypothesis: *)
    (wf_clc1 : wf_term typemap constmap types_of_varmap clc1 = true)
    (wf_clc2 : wf_term typemap constmap types_of_varmap clc2 = true)
    : Type.
    pose proof (generate_theorem' [] HNil types_of_varmap t clc1 clc2 wf_clc1 wf_clc2).
    exact X.
    Defined.
End TheoremGenerator.

(* reified equality with quantifiers *)
Inductive reified_q_equ :=
| mk_reified_q_equ(tvm : list type){t : type}(lhsP rhsP: term t).

(* reified quantifier-free equality *)
Inductive reified_qf_equ :=
| mk_reified_qf_equ{t : type}(lhs rhs : term t).

Inductive command_name :=
| CSaturateL2R
| CAddEqu
| CAddTerm.
(* later:
| CSaturateR2L
| CSaturateNoNewTerms
| CComputeGroundTerms
...

Possible notation: 3 chars:
- Match (?) or Create (!) LHS
- Treat LHS first (>) or Treat RHS first (<)
- Match (?) or Create (!) RHS

Eg CSaturateL2R would be ?>! : match LHS, then create all resulting RHS terms
Here, direction is actually implied.
But in ?>? vs ?<?, we might want to specify the "query plan" of where to match first.
*)

Definition command_arg (c : command_name) : Type :=
  match c with
  | CSaturateL2R => reified_q_equ
  | CAddEqu => reified_qf_equ
  | CAddTerm => { tp : type & term tp }
  end.

Record command := mk_command {
  get_command_name : command_name;
  get_command_arg : command_arg get_command_name;
}.

Module Mut.
  Definition mut {T : Type} (x : T) := unit.
  Ltac make name val := pose proof (tt : mut val) as name.
  Ltac put name val := change (mut val) in name.
  Ltac get name := lazymatch type of name with
    | mut ?val => val
    end.
End Mut.

(* Mutable reference to a constmap (and typemap as well).
   cm is of the form (let tm := <typemap> in let cm := <constmap> in tt).
   The extra `in tt` is so that the return type of the expression can be
   expressed without having to inline tm.
   The argument is made implicit so that it's not displayed, because it
   can grow quite big, despite the sharing of tm. *)
Definition constmap_ref {cm : unit} := unit.
Ltac constmap_ref_init :=
  let name := fresh "constmap" in
  pose proof (tt : @constmap_ref (let tm := @EGraphList.nil Type in
                                 let cm := @EGraphList.nil (dyn tm) in tt)) as name.
Ltac constmap_ref_put val :=
  lazymatch goal with
  | name: @constmap_ref _ |- _ => change (@constmap_ref val) in name
  end.
Ltac constmap_ref_get :=
  lazymatch goal with
  | name: @constmap_ref ?val |- _ => val
  end.

Ltac make_varmap :=
  lazymatch goal with
  | [ |- ?A -> ?B] =>
    constr:(HNil)
  | [ |- forall (x : ?t), _] =>
    let x' := fresh "x" in
    let __ := match constr:(O) with _ => intro x' end in
    let rest := make_varmap in
    constr:(HCons t x' rest)
  | _ =>
    constr:(HNil)
  end.

Ltac ltac_map f l :=
  lazymatch l with
  | ?t :: ?q =>
    let newt := f t in
    let rest := ltac_map f q in
    uconstr:(newt::rest)
  | nil => uconstr:(nil)
  end.

Ltac lift_dynelement typemap e :=
  lazymatch e with
  | mk_dyn _ ?dt ?dv => constr:(mk_dyn typemap dt dv)
  end.

Ltac reify_theorem_let typemap constmap new_th H :=
    let oldtypemap := fresh "oldtm" in
    let oldconstmap := fresh "oldcm" in
    rename typemap into oldtypemap;
    rename constmap into oldconstmap;
    evar (typemap : list Type);
    evar (constmap: list (dyn typemap));
    evar (new_th: reified_q_equ);
    let t := type of H in
    let _ := open_constr:(ltac:(
    let varmap := make_varmap in
    lazymatch goal with
    | [ |- ?g] =>
    let oldtypemap_u := eval unfold oldtypemap in oldtypemap in
    let tmap' := extend_typemap oldtypemap_u g in
    let typemap_u := eval unfold typemap in typemap in
    unify typemap_u tmap';
    let types_of_varmap := match type of varmap with
                            | hlist ?list_types => ltac_map ltac:(reify_type tmap') list_types
                            end in
    let oldconstmap_u := eval unfold oldconstmap in oldconstmap in
    let lifted_oldconstmap0 := ltac_map ltac:(lift_dynelement typemap) oldconstmap_u in
    let lifted_oldconstmap := constr:(lifted_oldconstmap0 : list (dyn typemap)) in
    let cmap' := extend_constmap typemap varmap lifted_oldconstmap g in
    let constmap_t := type of constmap in
    idtac typemap cmap' constmap_t;
    let constmap_u := eval unfold constmap in constmap in
    unify constmap_u cmap';
    lazymatch goal with
    | [ |- ?lhs = ?rhs ] =>
      let reified_lhs := reify_expr tmap' cmap' types_of_varmap varmap lhs in
      let reified_rhs := reify_expr tmap' cmap' types_of_varmap varmap rhs in
      let new_th_u := eval unfold new_th in new_th in
      unify (let lhs' := reified_lhs in
             let rhs' := reified_rhs in
        mk_reified_q_equ types_of_varmap lhs' rhs')
        new_th_u
    end
    end; eapply H):t) in
    (* subst oldtypemap;  *)
    (* subst oldconstmap; *)
    idtac.

(* Testing reification theorem: *)
Goal (forall m n, (forall x y ,  x + y = y + x)  -> (forall x y, x * y = y * x) -> (m + m = m) = True -> m + n = n + m ).
  intros.
  pose (@nil Type) as tm.
  pose (@nil (dyn tm)) as cm.
  Time reify_theorem_let tm cm theorem H.
  Show Proof.
  Abort.



Inductive Prod {T T': Type}: Type :=
  | prod : forall  (x:T) (y : T'), Prod .
Arguments Prod : clear implicits.
Definition fstP {A B:Type} (x : Prod A B) := match x with
| prod f s => f
end.
Definition sndP {A B:Type} (x : Prod A B) := match x with
| prod f s => s
end.


(* Definition upcast_varmap typemap typemap_extension
(varmap : list {f : SModule (typemap := typemap) & max_t (T f) <? length typemap = true})
 : list (SModule (typemap := typemap ++ typemap_extension)).
    refine (map (fun a => _ ) varmap).
    destruct a.
    pose( travel_value typemap (T x) typemap_extension e).
    inversion p.
    exact ({| T := _; state := y (state x) |}).
Defined. *)

  Fixpoint dropNone {A:Type} (l : list (option A))  : list A :=
    match l with
    | Some a :: b => a :: dropNone b
    | _::b => dropNone b
    | _ => nil
    end.

  Definition FUEL := 30%nat.

(* I will do translation validation for hte match pattern, that will be the easiest.
Validator will simply return a boolean if the candidate matches the pattern and hence if the fn is correct *)
Definition no_constraints (quanttype : list type) : llist (option eclass_id) quanttype.
  induction quanttype.
  - econstructor.
  - econstructor.
    + exact None.
    + exact IHquanttype.
Defined.
(* forall x y z, f (g ?x ?y) ?x *)
(* (0 ( _))
   (42 (_ _)) *)
(* (_ (_ _ _ _)) *)
Fixpoint rev_seq_pos' acc (n: nat) :=
  match n with
  | O => nil
  | S n => acc :: rev_seq_pos' (acc - 1) n
  end.

Definition rev_seq_pos (n: positive) :=
  rev_seq_pos' n (Pos.to_nat n).

Definition init_consider (types_of_varmap: list type) (e : egraph) :
 list (Prod eclass_id (llist (option eclass_id) types_of_varmap)) :=
  dropNone (map (fun el =>
      if find (uf e) el =? el then
        Some (prod el (no_constraints types_of_varmap))
      else
        None) (rev_seq_pos (max_allocated e))).

Section MiniTests.
Import EGraphList.ListNotations.

Open Scope list_scope.
Definition test0 := [`1; `1].
Definition in0 := no_constraints test0.

Compute (hlist_update_nth 0 in0 _ eq_refl (Some 2%positive)).

End MiniTests.


Fixpoint match_pattern_aux' (fuel : nat) (types_of_varmap : list type)
(e : egraph)
(current_root : eclass_id)
(quant_constraints : llist (option eclass_id) types_of_varmap)
t (p : term  t) :
list (llist (option eclass_id) types_of_varmap).
  refine (match p with
  | TApp p1 p2 => _
  | TVar n t => _
  | TConst n t => _
  end).
  {
    pose (PTree.get current_root (id2s e)) as root_set_enodes_package.
    destruct root_set_enodes_package as [[[_ type_root] enodes_represented_by_root]|].
    2:{ exact nil.  }
    destruct (enodes_represented_by_root) as [const_represented_by_root apps_represented_by_root].
    clear const_represented_by_root.
    pose (PTree.tree_fold_preorder (fun acc mid  =>
            PTree.tree_fold_preorder (fun acci '(fnbody, arg) =>
                    match_pattern_aux' fuel types_of_varmap e fnbody quant_constraints _ p1
                    ++ acci
                  ) mid acc
            ) apps_represented_by_root nil) as list_constraints_after_fn.
    refine(flat_map (fun elret =>  _: list (llist (option eclass_id) types_of_varmap)) list_constraints_after_fn ).
    exact (PTree.tree_fold_preorder (fun acc mid  =>
            PTree.tree_fold_preorder (fun acci '(fnbody, arg) =>
                    match_pattern_aux' fuel types_of_varmap e arg elret _ p2
                    ++ acci
                  ) mid acc
            ) apps_represented_by_root nil).
  }
  2:{
    unshelve refine (let id_atom2 := lookup e (EConst n ) in _).
    destruct id_atom2.
    - destruct ((e0 =? find (uf e) current_root)%positive).
      * exact [quant_constraints].
      * exact [].
    - exact [].
  }
  {
    destruct (llist_nth_error quant_constraints n) as [quantifier_constraint|].
    - (* n in bounds *)
      destruct quantifier_constraint as [instantiation|].
      + (* quantifier is constrained *)
        destruct ((find (uf e) instantiation =? find (uf e) current_root)%positive).
        * (* consistent with instantiation *)
          exact [quant_constraints].
        * (* contradicts instantiation *)
          exact [].
      + (* quantifier can be anything, so let's instantiate it *)
        exact [llist_update_nth quant_constraints n (Some current_root)].
    - (* n out of bounds *)
      exact [].
  }
Defined.

Definition match_pattern_any_root (fuel : nat) (types_of_varmap : list type)
(e : egraph)
t (p : term t) :
list
   (Prod eclass_id (llist (option eclass_id) types_of_varmap))
    :=
  flat_map
    (fun (el : (Prod eclass_id (llist (option eclass_id) types_of_varmap)))  =>
    match el with
    | prod root quant_constraints => map (prod root) (match_pattern_aux' fuel types_of_varmap e root quant_constraints t p)
    end)
    (init_consider types_of_varmap e).

Definition saturate_1LtoR_aux
  (types_of_varmap: list type) t'
  (rootL : eclass_id)
  (qInsts : llist eclass_id types_of_varmap)
  (pr : term  t')
  (e : egraph):
  egraph :=
  let (e, rootR) := add_term qInsts e pr in
  merge e rootL rootR.

Fixpoint llist_all_Some {A B : Type} {l : list A} (ll : llist (option B) l)
  : option (llist B l).
  destruct l.
  - exact (Some HNil).
  - inversion ll. subst.
    refine (match v with
            | Some b => match llist_all_Some _ _ _ cdr with
                        | Some rest => Some _
                        | None => None
                        end
            | None => None
            end).
    econstructor.
    1: exact b. exact rest.
Defined.

(* saturate left-to-right with 1 match of an equality theorem *)
Definition saturate_1LtoR (types_of_varmap: list type) {t} (pR : term t) (e : egraph)
           (matchL : Prod eclass_id (llist (option eclass_id) types_of_varmap))
  : egraph :=
  let 'prod rootL qInsts := matchL in
  match llist_all_Some qInsts with
  | Some qInsts => saturate_1LtoR_aux types_of_varmap t rootL qInsts pR e
  | None => e (* if a variable only appears in the RHS, it won't be instantiated
                 by matching the LHS against all terms, so it will remain None,
                 and in this case, we don't use the lemma to saturate *)
  end.

(* saturate left-to-right with all matches of an equality theorem *)
Definition saturate_LtoR (types_of_varmap: list type) {t} (pL pR : term t) (e : egraph)
  : egraph :=
  let matches := match_pattern_any_root FUEL types_of_varmap e t pL in
  fold_left (saturate_1LtoR types_of_varmap pR) matches e.

(* TODO: duplicate of merge_terms, but only returns an egraph instead of also rootL/rootR *)
Definition add_equ {t} (lhs rhs : term t) (e: egraph) : egraph :=
  let (e, rootL) := @add_term [] HNil e _ lhs in
  let (e, rootR) := @add_term [] HNil e _ rhs in
  merge e rootL rootR.

Definition constmap_app (tm tm_ext : list Type)
           (constmap : list (dyn tm)) (ext: list (dyn (tm ++ tm_ext))) :
  list (dyn (tm ++ tm_ext)).
Admitted.

Require Import Coq.Program.Equality.

Lemma use_bool_true  : forall {RET : Type}
  (y : bool)
  (t1 : y = true -> RET)
  (t2 : y = false -> RET)
  (pf : y = true),
  (if y as b return y = b -> RET
      then (fun Ht => t1 Ht)
      else (fun Hf => t2 Hf)) eq_refl
  = t1 pf.
  intros.
  destruct y.
  {
    dependent destruction pf.
    reflexivity.
  }
  inversion pf.
Defined.

Lemma use_bool_false  : forall {RET : Type}
  (y : bool)
  (t1 : y = true -> RET)
  (t2 : y = false -> RET)
  (pf : y = false),
  (if y as b return y = b -> RET
      then (fun Ht => t1 Ht)
      else (fun Hf => t2 Hf)) eq_refl
  = t2 pf.
  intros.
  destruct y.
  - inversion pf.
  - dependent destruction pf.
    reflexivity.
Defined.

Fixpoint max_t (t : type) :=
  match t with
  | `n => n
  | a ~> b => Pos.max (max_t a) (max_t b)
  end.

Lemma weaken_t_denote: forall tm ext t,
    (Pos.to_nat (max_t t) < length tm)%nat ->
    t_denote tm t = t_denote (tm ++ ext) t.
Admitted.

Definition cast_weaken_t_denote: forall tm ext t,
    (Pos.to_nat (max_t t) < length tm)%nat ->
    t_denote tm t -> t_denote (tm ++ ext) t.
  intros.
  erewrite <- weaken_t_denote.
  all: assumption.
Defined.

Lemma constmap_nth_error_app1 : forall n tm tmext constmap ext t v
       (pf: (Pos.to_nat (max_t t) < length tm)%nat),
    nth_error constmap n = Some (mk_dyn tm t v) ->
    nth_error (constmap_app tm tmext constmap ext) n =
    Some (mk_dyn (tm ++ tmext) _ (cast_weaken_t_denote tm tmext t pf v)).
Admitted.
(*
      induction n .
      {
        intros; destruct ctx; simpl in *; inversion H.
        unfold lift_ctx.
        unfold upcast_varmap.
        destruct t0.
        simpl in *.
        subst.
        unshelve erewrite use_bool_true ; eauto.
      }
      {
        simpl.
        intros.
        destruct ctx eqn:?.
        inversion H.
        simpl in pf.
        eapply andb_true_iff in pf.
        destruct pf.
        erewrite <- IHn.
        3:{ exact H. }
        unfold lift_ctx at 1.
        unfold upcast_varmap.
        simpl in *.
        destruct s.
        unshelve erewrite use_bool_true. exact H0.
        simpl.
        reflexivity.
        eauto.
      }
    Defined.
*)

Lemma eqPropType : forall {P P0 : Prop}, @eq Prop P P0 -> @eq Type P P0.
  intros.
  rewrite H.
  reflexivity.
Defined.
Require Import Coq.Logic.EqdepFacts.

(* Fixpoint match_respects_pattern(e : egraph)(types_of_varmap : list type)
         (root: eclass_id)
         (varmap: llist eclass_id types_of_varmap)
         {t} (p : term t) : bool .
  pose (lookup_term varmap p e).
  destruct o.
  -
  (* TODO: think twice about canoninicity *)
    exact (Pos.eqb root e0).
  -
    exact false.
  Defined.
   *)

(*
Lemma match_respects_pattern_to_lookup{types_of_varmap : list type}
      (* (varmap : llist eclass_id types_of_varmap)  *)
    (varmap: hlist (map (fun t => term t) types_of_varmap))
      e root {t} (p : term t):
    match_respects_pattern e types_of_varmap root varmap p = true ->
    lookup_term varmap p e = Some root.
Admitted. *)

Lemma add_already_there : forall e {t} (p : term t) root
  types_of_varmap (varmap : llist eclass_id types_of_varmap),
    lookup_term varmap p e = Some root ->
    add_term varmap e p = (e, root).
Proof.
  induction p.
  {
    intros.
    simpl.
    simpl in H.
    destruct (lookup_term) eqn:? in H.
    2:{ inversion H. }
    destruct (lookup_term) eqn:? in H.
    2:{ inversion H. }
    erewrite IHp1; eauto.
    erewrite IHp2; eauto.
    rewrite H.
    reflexivity.
  }
  {
    intros; simpl in *.
    destruct llist_nth_error. 2: discriminate.
    inversion H.
    reflexivity.
  }
  {
    simpl;  intros.
    rewrite H.
    eauto.
  }
  Qed.

Fixpoint subst_pattern {et t0}
  (p : term et)
  (replacement_term : term t0)
   :
  term et.
  induction p.
  {
    eapply (TApp
        (subst_pattern _ _ p1 replacement_term )
        (subst_pattern _ _ p2 replacement_term )).
  }
  {
    destruct (n =? 1).
    {
      simpl in *.
      destruct (type_eq_dec t t0).
      - subst. exact replacement_term.
      -
      (* Garbage in, garbage out *)
        exact (TVar 1 t).
    }
    {
      eapply TVar.
      (* Shift *)
      exact (n - 1).
    }
  }
  {
    eapply TConst.
    eapply n.
  }
  Defined.

Lemma subst_pattern_preserve_wf : forall {typemap constmap types_of_varmap} (tp : type)
(t : term tp) (tp_hole: type) (hole : term tp_hole),
 wf_term typemap constmap (tp_hole :: types_of_varmap) t = true ->
 wf_term typemap constmap [] hole = true ->
wf_term typemap constmap types_of_varmap (subst_pattern t hole) = true.
induction t.
{
  simpl in *.
  intros.
  eapply Bool.andb_true_iff in H.
  destruct H.
  erewrite IHt1; eauto.
}
{
  intros.
  simpl in *.
  destruct (nth_error) eqn:? in H.
  2:{ inversion H. }
  destruct type_eq_dec in H. 2:{ inversion H. }
  subst.
  destruct (match n with
      | 1 => true
      | _ => false
      end) eqn:?.
  - destruct n; try discriminate.
    simpl in Heqo.
    inversion Heqo.
    subst.
    destruct type_eq_dec; try firstorder.
    dependent destruction e.
    change (types_of_varmap) with ([] ++ types_of_varmap).
    eapply weaken_varmap_wf_term.
    exact H0.
  -
    replace ((Pos.to_nat n - 1)%nat) with (S (Pos.to_nat (n - 1) - 1)) in Heqo .
    2:{
      destruct n; lia.
    }
    simpl in Heqo.
    simpl.
    rewrite Heqo.
    destruct type_eq_dec; try firstorder.
}
{
  simpl; intros.
  destruct (nth_error) eqn:? in H.
  2:{ inversion H. }
  rewrite Heqo.
  eauto.
}
Defined.
Definition cast_hlist {typemap} l r: hlist
     (map (t_denote typemap) l ++ map (t_denote typemap) r) ->
hlist
     (map (t_denote typemap) (l ++ r)).
     intros.
     erewrite <- map_app in X.
     exact X.
Defined.

Definition cast_hlist_assoc {typemap constmap} (l1 l2 l3: list type) {t} (pL : term t) :
wf_term typemap constmap
     (l1 ++ l2 ++ l3) pL =
   true ->
wf_term typemap constmap
     ((l1 ++ l2) ++ l3) pL = true
 .
     intros.
     erewrite app_assoc in H.
     exact H.
Defined.

Lemma interp_subst : forall
      (typemap: list Type)
      (tHole t: type)
      (pL: term t)
      (hole: term tHole)
      (constmap: list (dyn typemap))
      (l: list type)
      (varmap: hlist (map (t_denote typemap) l))
      (wfH: wf_term typemap constmap [] hole = true)
      (wfL: wf_term typemap constmap (tHole :: l) pL = true),
      interp_term typemap constmap (tHole :: l)
        (HCons (t_denote typemap tHole)
           (interp_term typemap constmap [] HNil hole wfH) varmap) pL wfL =
      interp_term typemap constmap l varmap (subst_pattern pL hole)
        (subst_pattern_preserve_wf t pL tHole hole wfL wfH).
        Admitted.
  (* induction pL.
  {
    intros.
    simpl.
    simpl in wfL.
    destruct (computable_andb_true_iff _ _) eqn:?.
    pose (Bool.andb_true_iff
                (wf_term typemap constmap (tHole :: l) pL1)
                (wf_term typemap constmap (tHole :: l) pL2)).
    destruct i.
    clear H0.
    specialize (H wfL).
    destruct H.
    remember (  match
    computable_andb_true_iff
      (@wf_term typemap constmap (tHole :: l) (t ~> td) pL1)
      (@wf_term typemap constmap (tHole :: l) t pL2)
         with
         | conj H1 _ => H1
         end wfL).
    unfold computable_andb_true_iff in Heqa.
    rewrite H0 in Heqa.
    dependent destruction (wf_term typemap constmap (tHole :: l) pL2) in Heqa.
         simpl in Heqa.
    rewrite H in a.
    rewrite  in wfL.

  } *)


Lemma elim_quant_generate_theorem :
forall {types_of_varmap_remaining typemap types_of_varmap tHole t}
varmap constmap
(hole : term tHole) wfH
(pL pR : term t)
wfL wfR,
  generate_theorem' (tHole::types_of_varmap) (HCons (t_denote typemap tHole) (interp_term typemap constmap [] HNil hole wfH) varmap)
       types_of_varmap_remaining t pL pR wfL wfR =
generate_theorem' types_of_varmap varmap
       types_of_varmap_remaining t (subst_pattern pL hole) (subst_pattern pR hole)
       (subst_pattern_preserve_wf _ _ _ _ wfL wfH)
       (subst_pattern_preserve_wf _ _ _ _ wfR wfH)
        .
    induction types_of_varmap_remaining.
    2:{
      intros.
      specialize (IHtypes_of_varmap_remaining typemap ( types_of_varmap ++ cons a nil)).
      specialize (IHtypes_of_varmap_remaining tHole) with (constmap:=constmap)  (t:= t).
      specialize (IHtypes_of_varmap_remaining) with (hole:= hole).
      pose wfL as savedWfL.
      change (a :: types_of_varmap_remaining) with ([a] ++ types_of_varmap_remaining) in savedWfL.
      pose (cast_hlist_assoc _ _ _ _  savedWfL).
      rename savedWfL into savedWfl'.
      rename e into savedWfL.
      specialize (IHtypes_of_varmap_remaining) with (wfL:= savedWfL).
       pose wfR as savedWfR.
      change (a :: types_of_varmap_remaining) with ([a] ++ types_of_varmap_remaining) in savedWfR.
      pose (cast_hlist_assoc _ _ _ _  savedWfR).
      rename savedWfR into savedWfR'.
      rename e into savedWfR.
      specialize (IHtypes_of_varmap_remaining) with (wfR:= savedWfR).
      specialize (IHtypes_of_varmap_remaining) with (wfH:= wfH).
      simpl.
      Require Import Coq.Logic.FunctionalExtensionality.
      pose @forall_extensionality.
      set (eq_ind _ _ _ _ _ ) as wfL_transported.
      set (eq_ind _ _ _ _ _ ) as wfR_transported.
      set (eq_ind _ _ _ _ _ ) as wfsubL_transported.
      set (eq_ind _ _ _ _ _ ) as wfsubR_transported.
      match goal with
      | [ |- (forall (x : ?t), @?body1 x)= (forall y, @?body2 y)] =>
        specialize (e t body1 body2)
        end.
      match type of e with
      | ?A -> ?B =>  assert A
      end.
      {
          clear e.
          intros.
          set (hlist_snoc varmap x).
          change ((fix map (l : list type) : list Type :=
          match l with
          | [] => []
          | a :: t => t_denote typemap a :: map t
          end) types_of_varmap) with (map (t_denote typemap) types_of_varmap ) in h.
          change ([t_denote typemap a]) with (map (t_denote typemap ) [a]) in h.
          pose (cast_hlist _ _ h).
          specialize (IHtypes_of_varmap_remaining h0).
          subst h0.
          unfold cast_hlist in IHtypes_of_varmap_remaining.
          move IHtypes_of_varmap_remaining at bottom.
          match goal with
          | [H: generate_theorem' _ ?l _ _ _ _ _ _ = _ |- generate_theorem' _ ?r _ _ _ _  _ _ = _] =>
            assert (l = r)
            end.
          {
            subst h.
            remember (interp_term _ _ _ _ _ _ ).
            clear.
            change ((fix map (l : list type) : list Type :=
               match l with
               | [] => []
               | a :: t => t_denote typemap a :: map t
               end) types_of_varmap) with (map (t_denote typemap) types_of_varmap ) in varmap.
            match goal with
            | [|- _ = eq_rect_r _ ?hsn _ ] => remember hsn
            end.
            unfold hlist_snoc at 1 in Heqh.
            simpl in Heqh.
            unfold eq_rect_r, eq_rect, eq_sym in Heqh.
            unfold hlist_snoc.
            remember (hlist_app varmap (HCons (t_denote typemap a) x HNil)).
            revert Heqh.
            generalize h.
            generalize h0.
            clear.
            intros.
            dependent destruction h.
            dependent destruction Heqh.
            generalize h0.
            clear.
            change ([t_denote typemap a]) with (map (t_denote typemap) [a]).
            generalize [a].
            intro.
            remember (map_app _ _ _).
            generalize e.
            clear.
            unfold eq_rect_r at 2.
            unfold eq_rect.
            unfold eq_sym.
            unfold eq_ind_r.
            unfold eq_ind.
            unfold eq_sym.
            clear.
            destruct e.
            cbn.
            eauto.
        }
        rewrite <- H .
        match goal with
        | [H: generate_theorem' _ _ _ _ _ _ ?l1 ?l2 = _ |- generate_theorem' _ _ _ _ _ _ ?r1 ?r2 = _] =>
          assert (l1 = r1); [ | assert (l2=r2)]
          end.
          3:{
            rewrite <- H0 . rewrite <- H1.
            rewrite IHtypes_of_varmap_remaining.
            match goal with
            | [ |- generate_theorem' _ _ _ _ _ _ ?l1 ?l2 =  generate_theorem' _ _ _ _ _ _ ?r1 ?r2] =>
            assert (l1 = r1); [ | assert (l2=r2)]
            end.
            3:{
              rewrite H2.
              rewrite H3.
              eauto.
            }
            {
              clear.
              subst wfsubL_transported.
              subst savedWfL.
              subst savedWfl'.
              unfold cast_hlist_assoc.
              unfold eq_ind.
              simpl.
              remember (app_assoc _ _ _ ).
              unfold eq_trans, f_equal.
              change ((fix app (l m : list type) {struct l} : list type :=
                       match l with
                       | [] => m
                       | a0 :: l1 => a0 :: app l1 m
                       end)(types_of_varmap ++ [a]) types_of_varmap_remaining)  with ((types_of_varmap ++ [a]) ++ types_of_varmap_remaining).
              change ((fix app (l m : list type) {struct l} : list type :=
                       match l with
                       | [] => m
                       | a0 :: l1 => a0 :: app l1 m
                       end)(types_of_varmap) (a::types_of_varmap_remaining))  with ((types_of_varmap) ++ ([a] ++ types_of_varmap_remaining)).
              generalize wfL.
              generalize wfH.
              clear.
              generalize pL.
              clear.
              generalize hole.
              generalize constmap.
              generalize typemap.
              generalize t.
              generalize e.
              dependent destruction e0.
              eauto.
            }
            {
              clear.
              subst wfsubR_transported.
              subst savedWfR.
              subst savedWfR'.
              unfold cast_hlist_assoc.
              unfold eq_ind.
              simpl.
              remember (app_assoc _ _ _ ).
              unfold eq_trans, f_equal.
              change ((fix app (l m : list type) {struct l} : list type :=
                       match l with
                       | [] => m
                       | a0 :: l1 => a0 :: app l1 m
                       end)(types_of_varmap ++ [a]) types_of_varmap_remaining)  with ((types_of_varmap ++ [a]) ++ types_of_varmap_remaining).
               change ((fix app (l m : list type) {struct l} : list type :=
                       match l with
                       | [] => m
                       | a0 :: l1 => a0 :: app l1 m
                       end)(types_of_varmap) (a::types_of_varmap_remaining))  with ((types_of_varmap) ++ ([a] ++ types_of_varmap_remaining)).
              generalize wfR.
              generalize wfH.
              clear.
              generalize pR.
              clear.
              generalize hole.
              generalize constmap.
              generalize typemap.
              generalize t.
              generalize e.
              dependent destruction e0.
              eauto.
            }
          }
          {
            eauto.
          }
          {
            eauto.
          }
      }
      specialize (e H).
      simpl in e.
      eapply e.
    }
    {
      intros.
      cbn [generate_theorem'].
      simpl.
      unfold eq_ind, eq_trans, f_equal.
      remember (app_nil_r types_of_varmap).
      clear Heqe.
      change ((fix app (l m : list type) {struct l} : list type :=
             match l with
             | [] => m
             | a :: l1 => a :: app l1 m
             end) types_of_varmap []) with (types_of_varmap ++ []).
      change (((fix map (l : list type) : list Type :=
          match l with
          | [] => []
          | a :: t0 => t_denote typemap a :: map t0
          end) types_of_varmap)) with (map (t_denote typemap) types_of_varmap) in *.

      eapply eqPropType.
      Require Import Coq.Logic.PropExtensionality.
      pose propositional_extensionality.
      match goal with
      | [ |- ?a = ?b] => set a; set b end.
      specialize (e0 P P0).
      (* Upcaster from P = P0 in Prop, to P = P0 in type*)
      eapply e0.
      subst P P0.
      clear e0.
      split.
      {
        intros.
        (* This was surprisingly tricky the first time *)
        match goal with
        | [ |- ?a = ?b] =>
          match type of H with
          | ?c = ?d =>
          assert (a = c); [|assert (b = d)]
          end
        end.
        {
          clear.
          generalize wfH, wfL.
          generalize varmap.
          clear.
          generalize constmap.
          clear.
          intro.
          dependent destruction e.
          clear.
          intros.
          simpl in wfL.
          remember (types_of_varmap ++ []).
          clear Heql.
          clear.
          erewrite interp_subst.
          eauto.
        }
        {
          clear.
          generalize wfH, wfR.
          generalize varmap.
          clear.
          generalize constmap.
          clear.
          intro.
          dependent destruction e.
          clear.
          intros.
          simpl in wfR.
          remember (types_of_varmap ++ []).
          clear Heql.
          clear.
          erewrite interp_subst.
          eauto.
        }

        rewrite H0.
        rewrite H1.
        eauto.
      }
      {
        intros.
        (* This was surprisingly tricky the first time *)
        match goal with
        | [ |- ?a = ?b] =>
          match type of H with
          | ?c = ?d =>
          assert (a = c); [|assert (b = d)]
          end
        end.
        {
          clear.
          generalize wfH, wfL.
          generalize varmap.
          clear.
          generalize constmap.
          clear.
          intro.
          dependent destruction e.
          clear.
          intros.
          simpl in wfL.

          remember (types_of_varmap ++ []).
          clear Heql.
          clear.
          erewrite interp_subst.
          eauto.
        }
        {
          clear.
          generalize wfH, wfR.
          generalize varmap.
          clear.
          generalize constmap.
          clear.
          intro.
          dependent destruction e.
          clear.
          intros.
          simpl in wfR.
          remember (types_of_varmap ++ []).
          clear Heql.
          clear.
          erewrite interp_subst.
          eauto.
        }

        rewrite H0.
        rewrite H1.
        eauto.
      }
    }
    Qed.

Lemma lookup_closed_term_varmap : forall {types_of_varmap typemap constmap} {tw}
   (w : term tw) e (v : eclass_id) (varmap : llist eclass_id types_of_varmap),
wf_term typemap constmap [] w = true ->
    @lookup_term [] HNil _ w e = Some v ->
    lookup_term varmap w e = Some v.
    induction w.
    {
      intros.
      simpl in *.
      eapply Bool.andb_true_iff in H.
      destruct H.
      destruct lookup_term eqn:? in H0.
      2:{ inversion H0. }
      destruct lookup_term eqn:? in H0 .
      2:{ inversion H0. }
      erewrite IHw1; eauto.
      erewrite IHw2; eauto.
    }
    {
      simpl.
      intros.
      destruct ((Pos.to_nat n - 1)%nat) in H; inversion H.
    }
    {
      simpl.
      eauto.
    }
    Qed.

Theorem lookup_term_canonical e :
(*  invariant_egraph e -> *)
  forall {t} (f : term t) (c : eclass_id),
    @lookup_term [] HNil _ f e = Some c ->
    classIsCanonical e c.
Proof.
   intro.
(*
   induction f.
  -
    intros; cbn in H0.
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    repeat auto_specialize.
    destruct H.
    unfold n2idCanonical in sanely_assigned_lookup0.
    cleanup'.
    repeat auto_specialize.
    eauto.
  -
    intros.
    cbn in H0.
    unfold lookup in H0.
    cbn in H0.
    destruct H.
    unfold n2idCanonical in sanely_assigned_lookup0.
    cleanup'.
    eapply sanely_assigned_lookup0 with (f:=EAtom1 n).
    eauto.
  Qed.
*)
Admitted.

Lemma lookup_subst : forall {types_of_varmap typemap constmap} tl (pL : term tl) e (v : eclass_id) (varmap : llist eclass_id types_of_varmap)
rootL  {tw} (w : term tw) ,
wf_term typemap constmap (tw::types_of_varmap) pL = true ->
wf_term typemap constmap [] w = true ->
@lookup_term (tw::types_of_varmap) (HCons ((fun _ => eclass_id) tw) v varmap) _ pL  e = Some rootL ->
    @lookup_term [] HNil _ w e = Some v ->
    lookup_term varmap (subst_pattern pL w) e = Some rootL.
    induction pL.
    {
      intros.
      simpl in *.
      destruct lookup_term eqn:? in H1.
      2:{ inversion H1. }
      destruct lookup_term eqn:? in H1 .
      2:{ inversion H1. }
      erewrite IHpL1; eauto.
      -
      erewrite IHpL2; eauto.
      eapply Bool.andb_true_iff in H; eauto.
      eapply H.
      -
      eapply Bool.andb_true_iff in H; eauto.
      eapply H.
    }
    2:{
      intros.
      simpl in *.
      eauto.
    }
    {
      intros.
      simpl in *.
      destruct (match n with
        | 1 => true
        | _ => false
        end) eqn:?.
      - destruct n; try discriminate.
        simpl in H.
        destruct (type_eq_dec) in H.
        2:{ inversion H. }
        subst.
        destruct (type_eq_dec) ; intuition eauto.
        dependent destruction e0.
        unfold eq_rec_r,eq_rec, eq_sym, eq_rect.
        unfold llist_nth_error in H1.
        simpl in H1.
        unfold eq_rect_r, eq_rect, eq_sym in H1.
        inversion H1.
        subst.
        eapply lookup_closed_term_varmap; eauto.
        pose proof H2 as C.
        eapply lookup_term_canonical in C.
        unfold classIsCanonical in C.
        rewrite C.
        exact H2.
      -
        replace ((Pos.to_nat n - 1)%nat) with (S (Pos.to_nat (n - 1) - 1)) in H.
        2:{ destruct n; intuition lia. }
        unfold llist_nth_error in H1.
        destruct (nth_error) eqn:? in H.
        2:{ inversion H. }
        replace ((Pos.to_nat n - 1)%nat) with (S (Pos.to_nat (n - 1) - 1)) in H1.
        2:{ destruct n; intuition lia. }
        eauto.
    }
    Qed.

Lemma saturate_1LtoR_correct : forall
    {typemap} constmap (types_of_varmap : list type) t
    (pL pR: term t)
    (wfL : wf_term typemap constmap types_of_varmap pL = true)
    (wfR : wf_term typemap constmap types_of_varmap pR = true)
    (e : egraph)
    (e_pf: invariant_egraph typemap constmap e)
    (rootL : eclass_id)
    (varmap: llist eclass_id types_of_varmap)
    (varmap_ok : typecheck_varmap e varmap = true)
    (vtrue : lookup_term varmap pL e = Some rootL)
    (th_true : generate_theorem types_of_varmap pL pR wfL wfR),
    invariant_egraph typemap constmap
           (saturate_1LtoR_aux types_of_varmap t rootL varmap pR e).
Proof.
  induction types_of_varmap; intros.
  - unfold generate_theorem in th_true.
    simpl in th_true.
    unfold saturate_1LtoR_aux.
    pose proof @merge_preserve as P.
    specialize P with (1:=e_pf) (2:=th_true).
    unfold merge_terms in P.
    erewrite add_already_there in P.
     2: eassumption.
    destruct (add_term _ _ _) eqn: E.
    exact P.
  - unfold generate_theorem in th_true.
    simpl in th_true.
    unfold llist in varmap. cbn in varmap.
    dependent destruction varmap.
    pose proof (canonical_witness e_pf v).
    assert (v < max_allocated e) as MA by admit.
    assert (find (uf e) v = v ) as F by admit.
    specialize (H MA F).
    destruct (PTree.get) eqn:? in H. 2:{ inversion H. }
    destruct p. destruct p.
    destruct H as (w & L & Wf).
    simpl in varmap_ok.
    unfold eq_rect_r, eq_rect, eq_sym in varmap_ok.
    eapply Bool.andb_true_iff in varmap_ok.
    destruct varmap_ok.
    unfold typecheck_eid in H.
    rewrite Heqo in H.
    eapply type_eqb_correct in H.
    subst.
    epose (interp_term _  _ [] HNil  _ Wf) as witness.
    specialize (th_true witness).
    unfold eq_rect_r, eq_rect, eq_sym in th_true.
    unfold hlist_snoc,hlist_app in th_true.
    subst witness.
    pose @elim_quant_generate_theorem.
    specialize (e1) with (types_of_varmap_remaining:= types_of_varmap).
    specialize (e1) with (tHole:=a) (types_of_varmap := @nil type) (varmap := HNil).
    simpl in e1.
    specialize (e1) with (hole := w).
    specialize (e1) with (wfH:= Wf).
    specialize (e1) with (wfL:= wfL).
    specialize (e1) with (wfR:= wfR).
    rewrite e1 in th_true.
    specialize (IHtypes_of_varmap) with (4:= th_true).
    specialize (IHtypes_of_varmap _ e_pf rootL varmap H0).
    eapply (lookup_subst) with (w:= w) in vtrue; eauto.
    specialize (IHtypes_of_varmap vtrue).
    move IHtypes_of_varmap at bottom.
    unfold saturate_1LtoR_aux in IHtypes_of_varmap |- *.

    destruct (add_term ) eqn:? .
    destruct (add_term ) eqn:? in |-* .
    (* Little lwemma add_term subst *)
    assert ((e4,e5) = (e2,e3)) by admit.
    inversion H.
    subst.
    eauto.
Admitted.

(*
Lemma preserve : forall   {typemap} ctx quanttype t' input e p pnew,
match propose_formula ctx e FUEL (fstP input), deeplist2_from_deeplisteclass quanttype (sndP input) e with
| Some f, Some quantifiers =>
  interp_pattern (ctx:= ctx) (typemap := typemap) (deeplist_from_deeplist2 (ctx:=ctx) quanttype quantifiers) p
  =
  interp_formula ctx f
| _, _ => True
end ->
match propose_formula ctx (saturate_LtoR_aux ctx quanttype t' p pnew e) FUEL (fstP input), deeplist2_from_deeplisteclass quanttype (sndP input) (saturate_LtoR_aux ctx quanttype t' p pnew e) with
| Some f, Some quantifiers =>
  interp_pattern (ctx:= ctx) (typemap := typemap) (deeplist_from_deeplist2 (ctx:=ctx) quanttype quantifiers) p
  =
  interp_formula ctx f
| _, _ => True
end.
*)

Definition saturate_L2R_correct : forall
  {typemap} constmap (types_of_varmap : list type) t
  (pL pR: term t)
  (wfL : wf_term typemap constmap types_of_varmap pL = true)
  (wfR : wf_term typemap constmap types_of_varmap pR = true)
  (e : egraph)
  (e_pf: invariant_egraph typemap constmap e)
  (th_true : generate_theorem types_of_varmap pL pR wfL wfR),
  invariant_egraph typemap constmap (saturate_LtoR types_of_varmap pL pR e).
Admitted. (*
   intros.
   intros.
   unfold saturate_LtoR_aux.
   pose @saturate_1LtoR_correct.
   specialize (i) with (3:=th_true).
   pose proof (@match_pattern_correct typemap FUEL ctx quantifiermap e t' p).
   (* pose proof (@match_pattern_correct typemap FUEL ctx quantifiermap e t' p). *)
   remember (match_pattern_aux _ _ _ _ _ _).
   clear Heql.
   generalize dependent e.

  induction l; eauto.
  {
     intros.
     simpl.
     eapply IHl.
     eapply saturate_1LtoR_correct;
     eauto.
     inversion H.
     eauto.
     inversion H.

   }
   Qed.

Definition lift_pattern :
  forall (tm tmext : list Type)
    (t : type)
    (qm : list (type ))
    (ctx : asgn tm)
    (* Maybe add a proof that every term of the context is within tm *)
    (pf : forallb (fun el => max_t (T el) <? length tm) ctx  = true)
    (newctx : asgn (tm ++ tmext)),
      @Pattern tm qm ctx t ->
      @Pattern
        (tm++tmext)
        qm
        (lift_ctx tm tmext ctx newctx)
        t.
        intros.
        induction X.
        {
          eapply (PApp1 IHX1 IHX2).
        }
        {
          eapply (PVar n (t0:= t0) ).
          eauto.
        }
        {
          set ((T t0)).
          pose (state t0).
          pose (@PAtom1 (tm++tmext) (qm) (lift_ctx tm tmext ctx newctx)).
          pose lift_nth_error.
          specialize e0 with (1:=pf).
          specialize e0 with (1:=e).
          specialize (e0 tmext newctx).
          pose proof (forallb_forall (fun el => max_t (T el) <? length tm) ctx).
          destruct H.
          specialize (H pf). clear H0.
          eapply nth_error_In in e.
          specialize (H _ e).
          specialize (e0 H).
          specialize (p _ _ e0).
          exact p.
        }
  Defined.

Inductive reifed_obj {typemap : list Type} {ctx : asgn typemap} :=
| SingleFact (a : type) (f : Formula (typemap:=typemap) (ctx:=ctx) a)
| EqualFacts (a : type)
  (l : Formula (typemap:=typemap) (ctx:=ctx) a)
  (r : Formula (typemap:=typemap) (ctx:=ctx) a)
  (th : Type)
  (th_pf : th)
| Build_reifed_theorem  : forall
  (deept : type)
  (quant : list type)
  (lhsP : @Pattern typemap quant ctx deept)
  (rhsP : @Pattern typemap quant ctx deept)
  (th : Type)
  (th_pf : th)
, reifed_obj .

Definition lift_formula :
  forall (tm tmext : list Type)
    (t : type)
    (ctx : asgn tm)
    (* Maybe add a proof that every term of the context is within tm *)
    (pf : forallb (fun el => max_t (T el) <? length tm) ctx  = true)
    (newctx : asgn (tm ++ tmext)),
      @Formula tm ctx t ->
      @Formula
        (tm++tmext)
        (lift_ctx tm tmext ctx newctx)
        t.
        intros.
        induction X.
        {
          eapply (App1 IHX1 IHX2).
        }
        {
          set ((T t0)).
          pose (state t0).
          pose (@Atom1 (tm++tmext)  (lift_ctx tm tmext ctx newctx)).
          pose lift_nth_error.
          specialize e0 with (1:=pf).
          specialize e0 with (1:=e).
          specialize (e0 tmext newctx).
          pose proof (forallb_forall (fun el => max_t (T el) <? length tm) ctx).
          destruct H.
          specialize (H pf). clear H0.
          eapply nth_error_In in e.
          specialize (H _ e).
          specialize (e0 H).
          specialize (f _ _ e0).
          exact f.
        }
  Defined.


Definition lift_reifed_theorem {typemap : list Type} {ctx : asgn typemap}
    {diff_tm : list Type} {diff_vm : asgn (typemap ++ diff_tm)}
  (r : @reifed_obj typemap ctx)
  (pf :forallb (fun el : SModule => max_t (T el) <? length typemap) ctx = true )
  :
 @reifed_obj (typemap ++ diff_tm) (lift_ctx typemap diff_tm ctx diff_vm).
  destruct r.
  {
    eapply SingleFact.
    eapply lift_formula.  eauto.  eauto.
  }
  {
    eapply EqualFacts.
    eapply lift_formula. eauto. exact l.
    eapply lift_formula. eauto. exact r.
    exact th_pf.
  }
  {
    pose @Build_reifed_theorem.
    specialize (r) with (1:= (lift_pattern typemap diff_tm deept quant ctx pf diff_vm lhsP)).
    specialize (r) with (1:= (lift_pattern typemap diff_tm deept quant ctx pf diff_vm rhsP)).
    specialize (r) with (1:= th_pf).
    exact r.
  }
  Defined.

Definition lift_reifed_theorems {typemap : list Type} {ctx : asgn typemap}
    {diff_tm : list Type} {diff_vm : asgn (typemap ++ diff_tm)}
  (r : list (@reifed_obj typemap ctx))
  (pf :forallb (fun el : SModule => max_t (T el) <? length typemap) ctx = true )
  :
 list (@reifed_obj (typemap ++ diff_tm) (lift_ctx typemap diff_tm ctx diff_vm)).
 eapply (map (fun x => @lift_reifed_theorem _ _ _ _ x pf) r).
  Defined.

Definition get_tm {typemap : list Type} {ctx : asgn typemap} (r : @reifed_obj typemap ctx) := typemap.
Definition get_ctx {typemap : list Type} {ctx : asgn typemap} (r : @reifed_obj typemap ctx) := ctx.

Definition empty_theorem (typemap : list Type) (ctx : asgn typemap) : list (@reifed_obj typemap ctx) := nil.

Ltac add_theorem identtm identvm list_th new_th :=
  let temp := fresh "temp" in
  rename list_th into temp;
  let oldtm := match type of temp with
                | list (@reifed_obj ?tm _) => tm
                | _ => fail
                end in
  let oldvm := match type of temp with
                | list (@reifed_obj _ ?vm ) => vm
                | _ => fail
                end in
  let newtm := eval cbv [get_tm] in (get_tm new_th) in
  let newvm := eval cbv [get_ctx] in (get_ctx new_th) in
  let difft := eval cbv [skipn length] in (skipn (length oldtm) newtm) in
  let diffv := eval cbv [skipn length] in (skipn (length oldvm) newvm) in
  (* let term := eval cbv [new_th map empty_theorem identtm identvm lift_reifed_theorems lift_reifed_theorem deept quant lhsP rhsP th th_pf] in (new_th :: (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl)) in *)
  (* let term := eval cbv [identtm identvm lift_reifed_theorems map]  in (new_th :: (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl)) in *)
  let rest_list := eval hnf in (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl) in
  let term := constr:(new_th :: rest_list) in
  pose term as list_th;
  subst temp;
  subst new_th.

Ltac reify_hyp1 H oldtypemap oldvarmap :=
  idtac "start reify hyp";
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  let etm := fresh "quantifiers" in
  let nquant := fresh "quantifiers" in
  let patternlhs := fresh "lhsPat" in
  let patternrhs := fresh "rhsPat" in
  let deept := fresh "t_" in
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  evar (deept : type );
  evar (nquant : list (type ));
  evar (patternlhs : Pattern (quantifiermap:=nquant) (ctx:= oldvarmap) deept);
  evar (patternrhs : Pattern (quantifiermap:=nquant) (ctx:=oldvarmap) deept);
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  let newassert := fresh "newassert" in
  let quan := get_quantifiers H in
  let quan := type_term quan in
  idtac quan;
  let t := type of H in assert t as newassert;
  reify_forall 0;
   [
  match goal with
  | [ |- ?a = ?b] =>
  idtac "start listTypes" oldtm1;
  let typemap := listTypesFromProp oldtm1 (prod a b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  pose typemap;
  idtac typemap;
  let deepify_quant := ltac_map funToTArrow typemap quan in
  let deepify_quant := type_term deepify_quant in
  let oldvm := eval unfold oldvm in oldvm in
  let x' := eval unfold nquant in nquant in
  unify  deepify_quant x';
  idtac "deepquant" deepify_quant oldtm1 diff oldvm;
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (prod a b) in
  idtac "newvarmap" varmap;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  pose varmap;
  idtac "varmap" varmap deepify_quant typemap ;
  let reifedA := reify_prop' deepify_quant typemap varmap a in
  pose reifedA as A;
  let reifedB := reify_prop' deepify_quant typemap varmap b in
  pose reifedB as B;
  idtac "reifed" reifedA reifedB;
  let A':= eval unfold A in A in
  let B':= eval unfold B in B in
  let x' := eval unfold patternlhs in patternlhs in
  let y' := eval unfold patternrhs in patternrhs in
  let t := type of a in
  idtac "type of a" a t;
  let tm := eval unfold oldtypemap in oldtypemap in
  let deeply_represented := funToTArrow tm t in
  let t' := eval unfold deept in deept in
  unify t' deeply_represented;
  unify x' reifedA ;
  unify y' reifedB ;
  (* unify y' reifedB ; *)
  (* let c := type of A in
  match c with
  | Pattern ?rett =>
  let T := fresh "newlemma" in
  let rett := eval simpl in rett in
    pose (generate_theorem (ctx:= varmap) (typemap := typemap) rett deepify_quant [] DNil
                                A' B') as T;
  let x' := eval unfold x in x in
  unify x' T ;
  end *)
  eapply H
  end
 |]; clear newassert
 ;
 subst oldtm;
 subst oldvm.



Ltac reify_prop1 typemap varmap prop :=
  match prop with
   | ?a ?b =>
    lazymatch type of b with
        | Prop => let acc1 := reify_prop1 typemap varmap a in
           let acc2 := reify_prop1 typemap varmap b in
          (* let __ := match O with | _ => idtac "Node" a b acc1 acc2 end in *)
           let res :=
           constr:(App1 (typemap := typemap) acc1 acc2) in
          (* let __ := match O with | _ => idtac "Nodeok" res end in *)
          res
        | Type => fail
        | _ =>
           let acc1 := reify_prop1 typemap varmap a in
           let acc2 := reify_prop1 typemap varmap b in
          (* let __ := match O with | _ => idtac "Node" a b acc1 acc2 end in *)
           let res :=
           constr:(App1 (typemap := typemap) acc1 acc2) in
          (* let __ := match O with | _ => idtac "Nodeok" res end in *)
          res
   end
   | ?a =>
    let t := type of a in
    (* let typemap' := eval unfold typemap in typemap in *)
   (* let __ := match O with | _ => idtac "leaf" t a  typemap end in *)
    let deeply_represented := funToTArrow typemap t in
   (* let __ := match O with | _ => idtac "funTArrow" deeply_represented end in *)
    let deeply_represented := eval cbv in deeply_represented in
    let newa :=  eval cbv  [Pos.to_nat app_nth1 Pos.of_nat sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_value upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in (upcast_value typemap deeply_represented nil eq_refl a) in
    (* let __ := match O with | _ => idtac "lookingfor" a varmap end in *)
    (* idtac deeply_represented a varmap; *)
    let idx := indexList {| T := deeply_represented ; state := newa : (t_denote (typemap:= typemap) deeply_represented)|} varmap in
    let idx := eval cbv in (Pos.of_nat (1+idx)) in
    (* let __ := match O with | _ => idtac "idx" idx end in *)
    let res := constr:(@Atom1 typemap varmap idx _ eq_refl) in
      let tres := type of res in
    (* let __ := match O with | _ => idtac "ok " res tres end in *)
    constr:(@Atom1 typemap varmap idx _ eq_refl)
end.

Ltac init_maps tm vm :=
  pose ((cons Prop nil) : list Type) as tm;
  pose (nil : list (SModule (typemap := tm))) as vm.

Ltac reify_goal_equality oldtypemap oldvarmap :=
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  match goal with
  | [ |- ?a = ?b] =>
  idtac "start listTypes";
  let typemap := listTypesFromProp oldtm1 (prod a b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  let oldvm1 := eval unfold oldvm in oldvm in
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm1) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (prod a b) in
  idtac "newvarmap" varmap;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  subst oldvm;
  subst oldtm;
  match goal with
  | [|- ?a  = ?b] =>
    let oldtm := eval unfold oldtypemap in oldtypemap in
    let oldvm := eval unfold oldvarmap in oldvarmap in
    let reifedLHS := reify_prop1 oldtm oldvm a in
    let reifedRHS := reify_prop1 oldtm oldvm b in
    let lhs := fresh "goalLHS" in
    let rhs := fresh "goalRHS" in
    pose reifedLHS as lhs;
    pose reifedRHS as rhs
  end
  end.

Ltac reify_theorem_eq H oldtypemap oldvarmap list_th :=
  idtac "start reify hyp";
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  let etm := fresh "quantifiers" in
  let nquant := fresh "quantifiers" in
  let patternlhs := fresh "lhsPat" in
  let patternrhs := fresh "rhsPat" in
  let edeept := fresh "t_" in
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  evar (edeept : type );
  evar (nquant : list (type ));
  evar (patternlhs : Pattern (quantifiermap:=nquant) (ctx:= oldvarmap) edeept);
  evar (patternrhs : Pattern (quantifiermap:=nquant) (ctx:=oldvarmap) edeept);
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  let newassert := fresh "newassert" in
  let quan := get_quantifiers H in
  let quan := type_term quan in
  idtac quan;
  let t := type of H in assert t as newassert;
  reify_forall 0;
   [
  match goal with
  | [ |- ?a = ?b] =>
  idtac "start listTypes" oldtm1;
  let typemap := listTypesFromProp oldtm1 (prod a b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  pose typemap;
  idtac typemap;
  let deepify_quant := ltac_map funToTArrow typemap quan in
  let deepify_quant := type_term deepify_quant in
  let oldvm := eval unfold oldvm in oldvm in
  let x' := eval unfold nquant in nquant in
  unify  deepify_quant x';
  idtac "deepquant" deepify_quant oldtm1 diff oldvm;
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [ sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (prod a b) in
  idtac "newvarmap" varmap;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  pose varmap;
  idtac "varmap" varmap deepify_quant typemap ;
  let reifedA := reify_prop' deepify_quant typemap varmap a in
  pose reifedA as A;
  let reifedB := reify_prop' deepify_quant typemap varmap b in
  pose reifedB as B;
  idtac "reifed" reifedA reifedB;
  let A':= eval unfold A in A in
  let B':= eval unfold B in B in
  let x' := eval unfold patternlhs in patternlhs in
  let y' := eval unfold patternrhs in patternrhs in
  let t := type of a in
  idtac "type of a" a t;
  let tm := eval unfold oldtypemap in oldtypemap in
  let deeply_represented := funToTArrow tm t in
  let t' := eval unfold edeept in edeept in
  unify t' deeply_represented;
  unify x' reifedA ;
  unify y' reifedB ;
  eapply H
  end
 |]; clear newassert
 ;
 subst oldtm;
 subst oldvm;
 let tH0 := type of H in
 let new_th := fresh "newth" in
 pose (Build_reifed_theorem edeept nquant patternlhs patternrhs tH0 H )as new_th;
 add_theorem oldtypemap oldvarmap list_th new_th;
 subst patternlhs;
 subst patternrhs;
 subst nquant;
 subst edeept
 .

Ltac reify_quant_free oldtypemap oldvarmap H list_th :=
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  idtac "start" ;
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  lazymatch type of H with
    | ?a = ?b =>
idtac "start listTypes" a b;
  let typemap := listTypesFromProp oldtm1 (prod a b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  let oldvm1 := eval unfold oldvm in oldvm in
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm1) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (prod a b)  in
  idtac "newvarmap" varmap ;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  (* match goal with
  | [|- ?a  = ?b] => *)
    let reifedLHS := reify_prop1 typemap varmap a in
    let reifedRHS := reify_prop1 typemap varmap b in
    let lhs := fresh "hypL" H in
    let rhs := fresh "hypR" H in
    pose reifedLHS as lhs;
    pose reifedRHS as rhs;
  idtac "doneOld" ;
    let edeept := match type of lhs with
  | Formula ?a => a
  | _ => fail
  end in
  idtac "doneOldDual" a b edeept;
    let new_th := fresh "new_th" in
 pose (EqualFacts edeept lhs rhs _ H) as new_th;
  idtac "newtheorem" new_th;
  (* let new_th' := eval unfold new_th in new_th in  *)
 add_theorem oldtypemap oldvarmap list_th new_th;
 (* subst new_th;  *)
 subst lhs;
 subst rhs;
  subst oldvm;
  subst oldtm
 | ?a =>
  idtac "start listTypes";
  let typemap := listTypesFromProp oldtm1 a in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  let oldvm1 := eval unfold oldvm in oldvm in
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm1) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' a  in
  idtac "newvarmap" varmap ;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  let reifedLHS := reify_prop1 typemap varmap a in
  let lhs := fresh "hyp" H in
  pose reifedLHS as lhs;

  idtac "doneOld" ;
  let edeept := match type of lhs with
  | Formula ?a => a
  | _ => fail
  end in
  idtac "doneOldSingle" a;
  let new_th := fresh "new_th" in
  pose (SingleFact edeept lhs) as new_th;
  idtac "newtheorem" new_th;
  add_theorem oldtypemap oldvarmap list_th new_th;
  subst lhs;
  subst oldvm;
  subst oldtm
  end.


Ltac prove_eq goalLHS goalRHS i1 :=
  (* let e := fresh "aux_correct" in
  pose (correct _ i1 _ goalLHS goalRHS) as e ;
  match type of e with
  | forall q, ?l1 = _ -> ?l2 = _ -> _ =>
    set l1 in e; set l2 in e;
    let res := eval vm_compute in l1 in
    match res with
    | Some ?res =>
      eapply (e res)
    | _ => fail
    end
  end; clear e;
  vm_compute; exact eq_refl . *)
 let e := fresh "aux_correct" in
  pose (correct _ i1 _ goalLHS goalRHS) as e ;
  match type of e with
  | forall q, ?l1 = _ -> ?l2 = _ -> _ =>
    (* set l1 in e; set l2 in e; *)
    let res := eval vm_compute in l1 in
    match res with
    | Some ?res =>
      apply (e res); vm_compute; reflexivity
    | _ => fail
    end
  end.

(*  *)
(* Time reify_hyp1 sep_comm tm vm. *)

Ltac lift_for_goal tm vm lhs rhs list_th :=
  let temp := fresh "temp" in
  rename list_th into temp;
  let oldtm := match type of temp with
                | list (@reifed_obj ?tm _) => tm
                | _ => fail
                end in
  let oldvm := match type of temp with
                | list (@reifed_obj _ ?vm ) => vm
                | _ => fail
                end in
  let newtm := match type of lhs with
                | @Formula ?tm _ _ => tm
                | _ => fail end in
  let newvm := match type of lhs with
                | @Formula _ ?vm _ => vm
                | _ => fail end in
  let difft := eval cbv [skipn length] in (skipn (length oldtm) newtm) in
  let diffv := eval cbv [skipn length] in (skipn (length oldvm) newvm) in
  (* let term := eval cbv [new_th map empty_theorem identtm identvm lift_reifed_theorems lift_reifed_theorem deept quant lhsP rhsP th th_pf] in (new_th :: (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl)) in *)
  (* let term := eval cbv [identtm identvm lift_reifed_theorems map]  in (new_th :: (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl)) in *)
  let rest_list := constr:(@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl) in
  let term := constr:( (SingleFact _ lhs) :: (SingleFact _ rhs):: rest_list) in
  pose term as list_th;
  subst temp
  .

Ltac saturate_rec current_sponge name_sponge list_th :=
  let list_th := eval hnf in list_th in
  lazymatch list_th with
  | ?t :: ?q =>
  let t' := eval hnf in t in
  idtac t';
  lazymatch t' with
  | @Build_reifed_theorem _ _ ?deept ?quant ?lhsP ?rhsP _ ?th_pf =>
    saturate_rec (@saturate_L2R_correct _ _ quant deept lhsP rhsP _ current_sponge th_pf) name_sponge q
  | SingleFact ?t ?f =>
    saturate_rec (@apply_add_formula _ _ _ f _ _ current_sponge eq_refl) name_sponge q
  | EqualFacts ?t ?l ?r _ ?th_pf =>
  (* Currently does nothing here *)
    let interm1 := constr:(@apply_add_formula _ _ _ l _ _ current_sponge eq_refl) in
    let interm2 := constr:(@apply_add_formula _ _ _ r _ _ interm1 eq_refl) in
    let interm3 := constr:(@apply_merge _ _ _ _ _ l r interm2 th_pf eq_refl) in
    saturate_rec interm3 name_sponge q
  end
  | _ => pose proof current_sponge as name_sponge
  end.

Ltac saturate current_sponge list_th :=
    let list_th := eval unfold list_th in list_th in
    idtac list_th;
    let sponge := eval unfold current_sponge in current_sponge in
    clear current_sponge;
    saturate_rec sponge current_sponge list_th.

Notation Lipstick_sponge := (invariant_egraph _).


Goal (forall m n o, (forall x n ,  x + n = n + x) -> (forall x y z ,  (x + y) + z = x + (y + z)) ->
  m = 1 ->
  (* -> o + m + (pmya n + m) = (pmya n + m + o) + m ). *)
  (o + pmya n + 1  = o + ( m + pmya n))).
  intros.
  init_maps tm vm.
  pose ( empty_theorem tm vm) as list_th.
  Time reify_theorem_eq H tm vm list_th.
  Time reify_theorem_eq H0 tm vm list_th.
  rename list_th into basic_saturation.
  pose (basic_saturation ++ basic_saturation) as list_th.
  (* subst basic_saturation. *)
  (* pose (basic_saturation ) as list_th. *)
  Time reify_quant_free tm vm H1 list_th.
  Time reify_goal_equality tm vm.
  Time lift_for_goal tm vm goalLHS goalRHS list_th.
  pose (@empty_invariant tm vm) as sponge.
  Time saturate sponge list_th.
  (* match type of sponge with
  | invariant_egraph ?sponge =>
  pose (lookupF goalLHS sponge) as lhs;
  pose (lookupF goalRHS sponge) as rhs
  end. *)
  Time prove_eq goalLHS goalRHS sponge.
  Time Qed.

Goal (forall m n o, (forall x n ,  x + n = n + x) -> (forall x y z ,  (x + y) + z = x + (y + z))
  -> o + m + (pmya n + m) = (pmya n + m + o) + m ).
  intros.
  init_maps tm vm.
  pose ( empty_theorem tm vm) as list_th.
  Time reify_theorem_eq H tm vm list_th.
  Time reify_theorem_eq H0 tm vm list_th.
  (* Time reify_quant_free tm vm H1 list_th. *)
  Time reify_goal_equality tm vm.
  Time lift_for_goal tm vm goalLHS goalRHS list_th.
  pose (@empty_invariant tm vm) as sponge.
  Time saturate sponge list_th.
  Time prove_eq goalLHS goalRHS sponge.
  Time Qed.

End NonSamsam.



    pose_list_lemmas.
    pose_prop_lemmas.

    intros.
    specialize (eq_eq_True word).

    (* Make problems simpler by only considering one combination of the booleans,
       but it would be nice to treat all of them at once *)
    replace cond0_0 with false in * by admit.
    replace cond0 with false in * by admit.

    (* Make problem simpler by not requiring side conditions: since we know the
       concrete length of vs, we can destruct it, so firstn and skipn lemmas can
       be on cons without sideconditions rather than on app with side conditions
       on length *)
    destruct vs as [|v0 vs]. 1: discriminate HL.
    destruct vs as [|v1 vs]. 1: discriminate HL.
    destruct vs as [|v2 vs]. 1: discriminate HL.
    destruct vs as [|v3 vs]. 2: discriminate HL.
    clear HL.
    cbn.
    (* cbn in H. <-- We don't do this cbn because now that we've done the above
       destructs, cbn can do much more than it usually would be able to do. *)

    (* Preprocessing *)
    rewrite wsub_def in *.
    clear wsub_def.
    apply PropLemmas.eq_True in H.

    (* Rewrites with sideconditions, currently also part of separate preprocessing: *)
    pose proof (unsigned_of_Z 8 ltac:(lia)) as A1.

    (* Constant propagation rules, manually chosen to make things work,
       TODO how to automate? *)
    pose proof (eq_refl : (Z.to_nat (8 / 4)) = 2%nat) as C1.

  init_maps tm vm.
  pose (empty_theorem tm vm) as list_th.
  Time reify_theorem_eq and_True_l tm vm list_th.
  Time reify_theorem_eq skipn_cons tm vm list_th.
  Time reify_theorem_eq and_True_r tm vm list_th.
  Time reify_theorem_eq eq_eq_True tm vm list_th.

  (* Time vm_compute in list_th. *)
  (* Time reify_theorem_eq app_nil_r tm vm list_th.
  Time reify_theorem_eq app_nil_l tm vm list_th.
  Time reify_theorem_eq app_cons tm vm list_th.
 *)
  (* rename list_th into basic_saturation. *)
  (* pose (basic_saturation ) as list_th. *)
  (* clear basic_saturation. *)
  (* pose (basic_saturation ++ basic_saturation) as list_th. *)
  (* Time reify_theorem_eq sep_comm tm vm list_th. *)
  Time reify_theorem_eq wadd_0_l   tm vm list_th.
  Time reify_theorem_eq wadd_comm tm vm list_th.
  Time reify_theorem_eq wadd_assoc tm vm list_th.
  Time reify_theorem_eq wadd_opp tm vm list_th.

  (* Time reify_quant_free tm vm H list_th. *)
  Time reify_quant_free tm vm A1 list_th.
  Time reify_quant_free tm vm C1 list_th.
   split.
  2:{
    split.

  Time reify_goal_equality tm vm.
  Time lift_for_goal tm vm goalLHS goalRHS list_th.
  pose (@empty_invariant tm vm) as sponge.
  Time saturate sponge list_th.
  match type of sponge with
  | invariant_egraph ?sponge =>
  (* time(let v := eval native_compute in sponge in  *)
  pose (@lipstick _ sponge)  as sp
    (* let p := constr:(lookupF goalLHS sponge) in  *)
    (* pose p as lhs; *)
    (* let q := constr:(lookupF goalRHS sponge) in  *)
    (* pose q as rhs *)
  end.
  (* native_compute in sp. *)
  Time Eval native_compute in (max_allocated sp).
  Time Eval vm_compute in (max_allocated sp).

  (* Time vm_compute in lhs.
  Time vm_compute in rhs.
  Time prove_eq goalLHS goalRHS sponge.

  pose (@empty_invariant tm vm) as empty_e.


  Time reify_quant_free tm vm A1.
  pose ( empty_theorem tm vm) as list_th.
  cbv [empty_theorem] in list_th.


  Time saturate sponge1 list_th.
  pose (@apply_add_formula tm vm _ hypLA1 _ _ sponge1 eq_refl) as sponge2.
  Time reify_quant_free tm vm C1.

  reify_goal_equality tm vm.
  pose ( empty_theorem tm vm) as list_th.
  cbv [empty_theorem] in list_th.
  reify_theorem_eq H tm vm list_th.
  reify_theorem_eq H0 tm vm list_th.


  Time saturate i0 list_th.
  Time prove_eq goalLHS goalRHS i0.
    pose (@apply_add_formula tm vm _ goalLHS _ _ empty_e eq_refl).
    pose (@apply_add_formula tm vm _ goalRHS _ _ i eq_refl). *)

    (* If sep_comm first, it crashes *)



    (* Request for the sponge: Absorb all hypotheses, add the goal as a term,
       and then give me the smallest term that's equal to the goal.
       Below are manual steps consisting of only using equalities of the context
       (potentially forall-quantified, but without side conditions) and which
       result in the desired term in the goal *)
    rewrite (wadd_comm a (ZToWord 8)) in H.
    rewrite <- (wadd_assoc (ZToWord 8) a (wopp a)) in H.
    rewrite (wadd_opp a) in H.
    rewrite (wadd_0_r (ZToWord 8)) in H.
    rewrite A1 in H.
    rewrite C1 in H.
    repeat (rewrite ?firstn_cons, ?skipn_cons, <-?app_cons, ?firstn_O, ?skipn_O,
             ?app_nil_l, ?app_nil_r in H).
    rewrite sep_comm in H.
    rewrite H.
    rewrite and_True_l.
    rewrite (wadd_comm b a).
    rewrite eq_eq_True.
    rewrite and_True_r.

    (* This is the remaining conditions that can't be proven from the hypotheses,
       but having this reduced Prop is much simpler for the user than just to get
       the feedback "can't solve huge Prop automatically" *)
  Abort.

End WithLib.

Goal (forall m n o, (forall x n ,  x + n = n + x) -> (forall x y z ,  (x + y) + z = x + (y + z))
  -> o + m + m + (pmya n + m) = (pmya n + m + o) + m + m ).
  (* -> (o + m) + pmya n  = o + ( m + pmya n)). *)
  Time intros.
  Time init_maps tm vm.
  Time reify_hyp1 H tm vm.
  Time pose vm as oldvm.
  Time pose tm as oldtm.
  Time reify_hyp1 H0 tm vm.
  Time simpl in vm.
  Time pose vm as oldvm1.
  Time pose tm as oldtm1.
  Time reify_goal_equality tm vm.
  Time pose (skipn (length oldvm) vm) as diffv.
  Time pose (skipn (length oldtm) tm) as difft.
  Time pose (lift_pattern oldtm difft t_ quantifiers0 oldvm eq_refl diffv lhsPat).
  Time pose (lift_pattern oldtm difft t_ quantifiers0 oldvm eq_refl diffv rhsPat).
  Time pose (lift_pattern oldtm1 (skipn (length oldtm1) tm) t_0 quantifiers1 oldvm1 eq_refl (skipn (length oldvm1) vm) lhsPat0).
  Time pose (lift_pattern oldtm1 (skipn (length oldtm1) tm) t_0 quantifiers1 oldvm1 eq_refl (skipn (length oldvm1) vm) rhsPat0).
  Time pose (@empty_invariant tm vm) as empty_e.
  Time pose (@apply_add_formula tm vm _ goalLHS _ _ empty_e eq_refl).
  Time pose (@apply_add_formula tm vm _ goalRHS _ _ i eq_refl).
  Time pose (@saturate_L2R_correct _ vm quantifiers1 _ p1 p2 _ i0 H0).
  Time pose (@saturate_L2R_correct _ vm quantifiers0 _ p p0 _ i1 H).
  Time pose (@saturate_L2R_correct _ vm quantifiers1 _ p1 p2 _ i2 H0).
  Time pose (@saturate_L2R_correct _ vm quantifiers0 _ p p0 _ i3 H).
  Time prove_eq goalLHS goalRHS i4.
Time Qed.

(* CHENIL BROUGHT DOWN *)
  Inductive SModule {typemap : list Type} :=
    { T : type ; state : t_denote (typemap := typemap) T }.

  Definition generic_embed {typemap : list Type} (T': type ) (s:t_denote (typemap := typemap)T') :=
    {| T:= T'; state := s |}.

Notation "'<<' s '>>'" := (generic_embed s) (only parsing).


Section Term.
  Context {typemap : list Type}.
  Inductive Formula {ctx: asgn typemap} : type -> Type :=
      | App1: forall {t td},
        Formula (t ~> td) ->
        Formula t ->
        Formula td
      | Atom1 : forall (n : positive) t0,
        EGraphList.nth_error ctx ((Pos.to_nat n) - 1) = Some t0 ->
        Formula (T t0).


Require Import Eqdep.

Ltac auto_specialize :=
  match goal with
  | H : ?a,  H' : ?a -> _  |- _ =>
    let t := type of a in
    constr_eq t Prop;
    specialize( H' H)
  | H : ?a,  H' :  _  |- _ =>
    let t := type of a in
    constr_eq t Prop;
    specialize H' with (1:= H)
  |  H' :  _  |- _ =>
    specialize H' with (1:= eq_refl)
  end.

  Ltac cleanup' := intros;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: _ <-> _ |- _ => destruct H
  | H: exists _, _  |- _ => destruct H
  | H: True  |- _ => clear H
  | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
  | H : ?P, H' : ?P |- _ =>
    let t := type of P in
    assert_succeeds(constr_eq t Prop);
    clear H'
  end.
  Open Scope positive.

Theorem nobody_lookupF_outside e :
  invariant_egraph e ->
  forall t (a : Formula t) (eid : eclass_id),
    lookupF a e = Some eid ->
    eid < max_allocated e.
  intro.
  induction a.
  (* -
    cbn.
    intros.
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct H.
    eapply nobody_outside0; eauto. *)
  -
    cbn.
    intros.
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct H.
    eapply nobody_outside0; eauto.
  -
    cbn.
    intros.
    unfold lookup in H0.
    destruct H.
    eapply nobody_outside0; eauto.
  Qed.


Theorem lookupF_canonical e  :
  invariant_egraph e ->
  forall {t} (f : Formula t) (c : eclass_id),
   lookupF f e = Some c ->
   classIsCanonical e c.
   intro.
   induction f.
  -
    intros; cbn in H0.
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    repeat auto_specialize.
    destruct H.
    unfold n2idCanonical in sanely_assigned_lookup0.
    cleanup'.
    repeat auto_specialize.
    eauto.
  -
    intros.
    cbn in H0.
    unfold lookup in H0.
    cbn in H0.
    destruct H.
    unfold n2idCanonical in sanely_assigned_lookup0.
    cleanup'.
    eapply sanely_assigned_lookup0 with (f:=EAtom1 n).
    eauto.
  Qed.

  Lemma dt_eq'_refl : forall {t},
  exists p, dt_eq' t t = left p.
  induction t.
  - cbn.
    pose (nat_eq_refl t).
    destruct e.
    rewrite H.
    destruct x.
    cbn.
    eexists; eauto.
  -
    destruct IHt1.
    destruct IHt2.
    destruct x.
    destruct x0.
    cbn.
    rewrite H0.
    rewrite H.
    cbn.
    eexists; eauto.
  Qed.




  (* TODO this lemma will be a good exercise for exams in the future *)
  Lemma dt_sane : forall td t1, dt_eq (t1 ~> td) td = false.
  induction td.
  -
    cbn; eauto.
  -
    cbn in *.
    intros.
    destruct td2.
    2:{
      specialize (IHtd2 td2_1).
      eapply Bool.andb_false_iff in IHtd2.
      destruct IHtd2.
      erewrite dteq_refl in H.
      inversion H.
      rewrite H.
      eapply Bool.andb_false_iff .
      right.
      eapply Bool.andb_false_iff .
      right; eauto.
    }
      eapply Bool.andb_false_iff .
      right; eauto.
      Qed.
  Lemma dt_sanef : forall t1 td , dt_eq (t1 ~> td) t1 = false.
  induction t1.
  -
    cbn; eauto.
  -
    cbn in *.
    intros.
    destruct t1_1.
    eauto.
    {
      specialize (IHt1_1 t1_2).
      eapply Bool.andb_false_iff in IHt1_1 .
      destruct IHt1_1.
      rewrite H; eauto.
      rewrite H.
      rewrite Bool.andb_comm.
      rewrite Bool.andb_assoc.
      rewrite Bool.andb_comm.
      cbn. eauto.
    }
    Qed.
  (* TODO this lemma will be a good exercise for exam in the future *)
  Lemma dt_sane2 : forall td t1 t2, dt_eq (t1 ~> t2 ~> td) td = false.
  induction td.
  -
    cbn; eauto.
  -
    cbn in *.
    intros.
    destruct td2.
    2:{
      specialize (IHtd2 td2_1).
      eapply Bool.andb_false_iff in IHtd2.
      destruct IHtd2.
      erewrite dteq_refl in H.
      inversion H.
      rewrite H.
      eapply Bool.andb_false_iff .
      right.
      eapply Bool.andb_false_iff .
      right; eauto.
    }
      eapply Bool.andb_false_iff .
      right; eauto.
   Qed.

  Lemma dt_sane2f : forall t1 t2 td, dt_eq (t1 ~> t2 ~> td) t1 = false.
  induction t1.
  -
    cbn; eauto.
  -
    cbn in *.
    intros.
    case t1_1 eqn:?.
    simpl;eauto.
    case t1_2 eqn:?.
    rewrite Bool.andb_comm.
    cbn; eauto.
    {
      destruct d2.
      {
      eapply Bool.andb_false_iff in IHt1_1.
      destruct IHt1_1.
      rewrite H; eauto.
      rewrite Bool.andb_comm.
      rewrite Bool.andb_assoc.
      rewrite Bool.andb_comm.
      cbn. eauto.
      exact t2.
      exact t2.
      }
      {
        specialize (IHt1_1 d2_1 d2_2).
      eapply Bool.andb_false_iff in IHt1_1.
      destruct IHt1_1.
      rewrite H; eauto.
      rewrite dteq_refl in H.
      rewrite dteq_refl in H.
      cbn in *; inversion H.
      }
    }
   Qed.

  Fixpoint node_size (t : type ) :=
    match t with
    | TBase n => 1
    | TArrow a b => 1 + node_size a + node_size b
    end.

  Lemma size_eq_dt : forall t1 t2, dt_eq t1 t2 = true -> node_size t1 = node_size t2.
    induction t1.
    -
      cbn.
      destruct t2.
      intros.
      eauto.
      intros. inversion H.
    -
      intros.
      cbn in *.
      destruct t2.
      inversion H.
      cbn.
      eapply Bool.andb_true_iff in H.
      cleanup'.
      erewrite IHt1_1; eauto.
      erewrite IHt1_2; eauto.
    Qed.

  Require Import Lia.
  (* Even more interesting induction for this one! *)
  Lemma dt_sane2s : forall t2 t1 td, dt_eq (t1 ~> t2 ~> td) t2 = false.
  intros.
  destruct (dt_eq _ _) eqn:?; eauto.
  pose proof (size_eq_dt _ _ Heqb).
  cbn [node_size] in H.
  lia.
  Qed.

  Lemma dteq_neq_dteq'  : forall t1 t2, dt_eq t1 t2 = false -> exists p, dt_eq' (t1 ) t2 = right p.
    induction t1.
    -
      destruct t2; eauto.
      cbn; intros.
      eapply beq_nat_false in H.
      destruct (Nat.eq_dec t t0).
      contradiction H; eauto.
      intros; eexists; eauto.
      cbn.
      intros; eexists; eauto.
    -
      intros.
      cbn in *.
      destruct t2; [eexists; eauto|].
      eapply Bool.andb_false_iff in H.
      destruct H.
      specialize (IHt1_1 _ H).
      destruct IHt1_1.
      rewrite H0.
      destruct (dt_eq' t1_2 t2_2).
      destruct e.
      cbn; eexists; eauto.
      eexists; eauto.
      specialize (IHt1_2 _ H).
      destruct IHt1_2.
      rewrite H0.
      eexists; eauto.
  Qed.

  Lemma dt_sane'  : forall td t1, exists p, dt_eq' (t1 ~> td) td = right p.
    intros.
    eapply dteq_neq_dteq'.
    eapply dt_sane.
  Qed.
  Lemma dt_sane2'  : forall td t1 t2, exists p, dt_eq' (t1 ~> t2 ~> td) td = right p.
    intros.
    eapply dteq_neq_dteq'.
    eapply dt_sane2.
  Qed.
 Lemma dt_sane2f'  : forall td t1 t2, exists p, dt_eq' (t1 ~> t2 ~> td) t1 = right p.
    intros.
    eapply dteq_neq_dteq'.
    eapply dt_sane2f.
  Qed.
 Lemma dt_sane2s'  : forall td t1 t2, exists p, dt_eq' (t1 ~> t2 ~> td) t2 = right p.
    intros.
    eapply dteq_neq_dteq'.
    eapply dt_sane2s.
  Qed.
  Lemma dt_comm_right  : forall t1 t2 p, dt_eq' t1 t2 = right p -> exists p', dt_eq' t2 t1 = right p' .
    induction t1.
    - intros.
    destruct t2.
    cbn in *.
    destruct (Nat.eq_dec t t0).
    rewrite e.
    destruct (Nat.eq_dec _ _).
    inversion H.
    contradiction n; eauto.
    destruct (Nat.eq_dec _ _).
    contradiction n; eauto.
    eexists; eauto.
    cbn in *.
    eexists; eauto.
    -
      intros.
      cbn in *.
      destruct t2.
      cbn.
      eexists; eauto.
      cbn.
      destruct (dt_eq' t1_2 t2_2) eqn:?;
      destruct (dt_eq' t1_1 t2_1) eqn:?.
      subst.
      cbn in H.
      inversion H.
      destruct e.
      cbn in H.
      specialize (IHt1_1 _ _ Heqs0).
      destruct IHt1_1.
      rewrite H0.
      pose (@dt_eq'_refl t1_2).
      destruct e.
      rewrite H1.
      destruct x0.
      cbn.
      eexists; eauto.
      specialize (IHt1_2 _ _ Heqs).
      destruct IHt1_2.
      rewrite H0.
      eexists; eauto.
      specialize (IHt1_2 _ _ Heqs).
      destruct IHt1_2.
      rewrite H0.
      eexists; eauto.
  Qed.


  Lemma atom_correct : forall {t t' st} (f1 : Formula t) n eq,
    eqf f1 (Atom1 n {|T:= t'; state := st|} eq) = true ->
    exists st' eq', f1 = Atom1 n {| T:= t; state := st'|} eq'.
    induction f1; intros; cbn in H; try inversion H.
    destruct t0.
    cbn in *.
    destruct (dt_eq' T0 t').
    eapply Pos.eqb_eq in H; eauto.
    rewrite <- H.
    eexists; eexists; eauto.
    inversion H.
  Qed.

  Lemma lookup_update {t} (f : Formula t) {old_id2s} :
  forall e n (eid0 : eclass_id),
      invariant_egraph e ->
      lookup e (EAtom1 n) = None ->
      lookupF f {| max_allocated := max_allocated e + 1;
                   uf := uf e;
                   n2id := add_enode (n2id e) (EAtom1 n) (max_allocated e);
                   id2s := old_id2s |} = Some eid0 ->
      lookupF f e = Some eid0 \/
      exists st eq, eqf f (Atom1 n {| T:= t; state := st |} eq) = true.
    induction f; cbn.
       2:{
         intros.
         cbn.
         unfold add_enode.
         cbn.
         destruct t0.
         cbn in *.
         pose proof (@dt_eq'_refl T0).
         destruct H2.
         intros.
         (* rewrite H2. *)
         unfold lookup in H1.
         simpl in H1.
         destruct H.
         unfold lookup, Enodes.lookup, lookup' in H0, nobody_outside0, H1.
         unfold add_enode, Enodes.lookup, lookup' in H1.
         destruct (n2id e0) eqn:?.
         simpl in H0.
         destruct ((n =?  n0)%positive) eqn:?.
         {
           pose (@Pos.eqb_eq n n0).
           destruct i.
           specialize (H Heqb).
           rewrite H in *.
           destruct (PTree.get _ _ ) eqn:? in H0.
           inversion H0.
           rewrite Heqo in H1.
           rewrite PTree.gss in H1.
           rewrite H2.
           eauto.
         }
         {
         pose (@Pos.eqb_neq n n0).
         destruct i.
         specialize (H Heqb).
         destruct (PTree.get _ _ ) eqn:? in H0.
         inversion H0.
         rewrite Heqo in H1.
         rewrite PTree.gso in H1; eauto.
         specialize (nobody_outside0 (EAtom1 n) eid0 ).
         cbn in nobody_outside0.
         specialize (nobody_outside0 H1).
         destruct (PTree.get n t) eqn:?.
         2:{ inversion H1. }
         inversion H1.
         left.
         unfold lookup, Enodes.lookup, lookup'.
         rewrite Heqm.
         simpl.
         rewrite Heqo0.
         eauto.
       }
       }
       {
          intros.
          destruct (lookupF f1 _) eqn:? in H1.
          destruct (lookupF f2 _)  eqn :? in H1.
          specialize (IHf1 _ _ _ H H0 Heqo).
          specialize (IHf2 _ _ _ H H0 Heqo0).
          destruct IHf1.

          2:{
            cleanup'.
            pose proof (eq_preserve_type _ _ H2).
            subst.
            pose proof (@atom_correct).
            specialize (H4) with (1:= H2).
            cleanup'.
            subst.
            cbn in Heqo.
            unfold lookup, Enodes.lookup, lookup' in Heqo.
            cbn in Heqo.
            cbn .
            rewrite H0.
            simpl in *.
            unfold add_enode in *.
            destruct (n2id e) eqn:?.

            unfold lookup, Enodes.lookup, lookup' in *.
            destruct (PTree.get _ _) eqn:? in Heqo.
            rewrite Heqo1 in *.
            simpl in H1.
            rewrite Heqm in H0.
            simpl in H0.
            rewrite Heqo1 in H0.
            inversion H0.
            simpl in*.
            rewrite Heqo1 in *.
            simpl in*.
            rewrite PTree.gss in Heqo.
            simpl in Heqo.
            inversion Heqo.
            destruct H.

            unfold lookup in no_args_eapp1_outside0.
            simpl in no_args_eapp1_outside0.
            specialize (no_args_eapp1_outside0 eid0 e0 e1).
            unfold Enodes.lookup, lookup' in H1, no_args_eapp1_outside0.
            rewrite Heqm in no_args_eapp1_outside0.
            specialize (no_args_eapp1_outside0 H1).
            subst.
            cleanup'.
            unfold find in H.
            cbn in H.
            unfold classIsCanonical, find in uf_id_outside0.
            erewrite (uf_id_outside0 (max_allocated e)) in H.
            erewrite uf_id_outside0 in H.
            cbn in *.
            lia.
            lia.
            lia.
          }
          rewrite H2.
          destruct IHf2.
          2:{
            cleanup'.
            pose proof (eq_preserve_type _ _ H3).
            subst.
            pose proof (@atom_correct).
            specialize (H5) with (1:= H3).
            cleanup'.
            subst.
            cbn in Heqo.
            cbn in *.
            unfold lookup, Enodes.lookup, lookup' in *.
            cbn in Heqo.
            cbn .
            simpl in *.
            clear H3.
            unfold add_enode in *.
            destruct (n2id e) eqn:?.

            unfold lookup, Enodes.lookup, lookup' in *.
            destruct (PTree.get _ _) eqn:? in H0.
            rewrite Heqo1 in *.
            simpl in *.
            inversion H0.

            simpl in*.
            rewrite Heqo1 in *.
            simpl in*.

            rewrite PTree.gss in Heqo0.
            simpl in Heqo0.
            inversion Heqo0.
            destruct H.
            unfold lookup in no_args_eapp1_outside0.
            simpl in no_args_eapp1_outside0.
            specialize (no_args_eapp1_outside0 eid0 e0 e1).
            unfold Enodes.lookup, lookup' in H1, no_args_eapp1_outside0.
            rewrite Heqm in no_args_eapp1_outside0.
            specialize (no_args_eapp1_outside0 H1).
            subst.
            cleanup'.
            unfold find in H3.
            cbn in H3.
            unfold classIsCanonical, find in uf_id_outside0.
            erewrite (uf_id_outside0 (max_allocated e)) in H3.
            erewrite uf_id_outside0 in H3.
            cbn in *.
            lia.
            lia.
            lia.
          }
          rewrite H3.
          left.
          unfold add_enode,lookup, Enodes.lookup, lookup' in *.
          cbn in *.
          destruct (n2id e).
            unfold lookup, Enodes.lookup, lookup' in *.
            destruct (PTree.get _ _) eqn:? in H0.
            rewrite Heqo1 in *.
            simpl in *.
            inversion H0.
          rewrite Heqo1 in *.
          eauto.
          inversion H1.
          inversion H1.
       }
       Qed.

  Lemma lookup_add_not_there : forall {t} (g : Formula t) e node i {new_id2s},
    invariant_egraph e ->
    lookup e node = None ->
    lookupF g e = Some i ->
    lookupF g {| max_allocated := max_allocated e + 1;
                 uf := uf e;
                 n2id := add_enode (n2id e) (canonicalize e node) (max_allocated e);
                 id2s := new_id2s |} =
    Some i.
    induction g.
    {
      intros.
      cbn in *.
      repeat auto_specialize.
      destruct (lookupF _ _) eqn:? in H1.
      2:{ inversion H1. }
      destruct (lookupF _ _) eqn:? in H1.
      2:{ inversion H1. }
      repeat auto_specialize.
      rewrite IHg1.
      rewrite IHg2.

      unfold lookup, Enodes.lookup, lookup'  in *.
      simpl.
      destruct node;eauto.
      (* destruct (_&&_)eqn:?; eauto. *)
      (* eapply Bool.andb_true_iff in Heqb. *)
      cleanup'.
      pose proof (@lookupF_canonical _ H _ _ _ Heqo).
      pose proof (@lookupF_canonical _ H _ _ _ Heqo0).
      unfold add_enode.
      simpl in *.
      destruct (n2id e) eqn:?.
      rewrite H2 in H1.
      simpl in *.
      rewrite H3 in H1.
      rewrite H2.
      rewrite H3.

        unfold lookup, Enodes.lookup, lookup' in *.
      simpl in *.
        destruct (PTree.get _ _) eqn:? in H1  .
        2:{ inversion H1. }
        destruct (PTree.get _ _) eqn:? in H1  .
        2:{ inversion H1. }
      assert (e0 = find (uf e) e2 \/ e0 <> find (uf e) e2) by lia.
      destruct H4.
      2:{
        simpl in *.
        unfold lookup, Enodes.lookup, lookup' in *.

        destruct (PTree.get _ _) eqn:? in H0  .
        rewrite Heqo3.
        destruct (PTree.get _ _) eqn:? in H0  .
        rewrite Heqo4.
        rewrite Heqo1.
        rewrite Heqo2.
        eauto.
        rewrite Heqo4.
      erewrite PTree.gso;
      eauto.
      simpl in *.
      setoid_rewrite Heqo1.
      setoid_rewrite Heqo2.
      eauto.
      rewrite Heqo3.
      erewrite PTree.gso;
      eauto.
      setoid_rewrite Heqo1.
      setoid_rewrite Heqo2.
      eauto.
      }

      subst.
      rewrite Heqo1 in *.
      destruct (PTree.get _ _) eqn:? in H0  .
      inversion H0.
      rewrite Heqo3.

      erewrite PTree.gss.
      simpl in *.
      (* rewrite H2 iddn H0. *)
      assert (e1 = find (uf e) e3 \/ e1 <> find (uf e) e3) by lia.
      destruct H4.
      2:{
        erewrite PTree.gso; eauto.
        rewrite Heqo2.
        eauto.
      }
      subst.
      rewrite PTree.gss.
      simpl.
      inversion H1.
      2:{  simpl in *.
      destruct (n2id e) eqn:?.
      unfold add_enode.
      unfold Enodes.lookup, lookup'.
      destruct (PTree.get _ _) eqn:? in H0  .
      inversion H0.
      rewrite Heqo1 in *.
      eauto.
      }
      (* Contradiction *)
      congruence.
    }
    {
      intros.
      cbn in *.
      unfold add_enode.
      unfold lookup, Enodes.lookup, lookup'  in *.
      cbn in *.
      destruct (n2id e0) eqn:?.
      destruct node; eauto.
      cbn in *.
      destruct (PTree.get _ _) eqn:? in H0.
      rewrite Heqo.
      destruct (PTree.get _ _) eqn:? in H0.
      inversion H0.
      rewrite Heqo0.
      eauto.
      rewrite Heqo.
      eauto.
      simpl.
      destruct (n0 =? n) eqn:?; eauto.
      eapply Pos.eqb_eq in Heqb.
      subst.

      destruct (PTree.get _ _) eqn:? in H1.
      2:{ inversion H1. }
      setoid_rewrite Heqo.
      setoid_rewrite Heqo.
      eauto.

      eapply Pos.eqb_neq in Heqb.
      destruct (PTree.get n0 _) eqn:? .
      destruct (PTree.get _ _) eqn:? .
      eauto.
      inversion H1.
      rewrite PTree.gso.
      eauto.
      eauto.
    }
    Qed.

  (* On veut dire que si lookup = max_allocated, alors f2 est EAtom1 *)
  Lemma found_high_in_updated : forall {t} (g : Formula t) e node i {new_id2s},
    invariant_egraph e ->
    lookupF g {| max_allocated := max_allocated e + 1;
                 uf := uf e;
                 n2id := add_enode (n2id e) (canonicalize e node) (max_allocated e);
                 id2s := new_id2s |} =
    Some i ->
    (i < max_allocated e /\ lookupF g e = Some i ) \/
    (i = max_allocated e /\
    match g with
    | Atom1 n t eq => EAtom1 n = canonicalize e node
    | App1 f1 f2  =>
      exists e1 e2,
        lookupF  f1 e= Some e1 /\
        lookupF  f2 e= Some e2 /\
        EApp1 e1 e2 = canonicalize e node
    end).
    induction g.
    {
      intros e node i new_id2s inv.
      simpl.
      intros.
      destruct (lookupF _ _) eqn:? in H.
      2:{ inversion H. }
      destruct (lookupF _ _) eqn:? in H.
      2:{ inversion H. }
      unfold add_enode in H.
      repeat auto_specialize.
      destruct IHg1.
      destruct IHg2.
      {
        cleanup'.
        rewrite H3, H2.
        unfold lookup, Enodes.lookup, lookup' in *.
        simpl in *.
        destruct (n2id e) eqn:?.
        pose proof (@lookupF_canonical _ inv _ _ _ H3) as can_n1.
        pose proof (@lookupF_canonical _ inv _ _ _ H2) as can_n0.
        rewrite can_n0, can_n1 in *.
        cleanup'.
        destruct node eqn:?.
        2:{ left. split; eauto. simpl in *. destruct inv.

        unfold lookup, Enodes.lookup, lookup' in nobody_outside0.
        erewrite Heqm in nobody_outside0.
        specialize (nobody_outside0 (EApp1 e0 e1) i).
        simpl in nobody_outside0.
        rewrite can_n0 in nobody_outside0.
        rewrite can_n1 in nobody_outside0.
        destruct (PTree.get _ _) in H.
        specialize (nobody_outside0 H).
        eauto.
        eauto.
        simpl in *.
        destruct (PTree.get _ _) in H.
        eauto.
        eauto.
        }
        simpl in *.
        destruct (PTree.get) eqn:? in H.
        destruct (PTree.get) eqn:? in H.
        destruct (PTree.get) eqn:? in H.
        rewrite Heqo3.
        destruct (PTree.get) eqn:? in H.
        2:{ inversion H. }
        2:{ inversion H. }
        rewrite Heqo4.
        { left.
        split;eauto.
        destruct inv.
        unfold lookup, Enodes.lookup, lookup' in nobody_outside0.
        rewrite Heqm in nobody_outside0.
        specialize (nobody_outside0  (EApp1 e0 e1) i).
        eapply nobody_outside0.
        simpl.
        rewrite can_n1.
        rewrite can_n0.
        rewrite Heqo3.
        rewrite Heqo4.
        congruence.
        }
        {
        assert (e0 = find (uf e) e2 \/ e0 <> find (uf e) e2) by lia.
        destruct H4.
        {
          rewrite H4 in *.
          rewrite PTree.gss in H.
        assert (e1 = find (uf e) e3 \/ e1 <> find (uf e) e3) by lia.
        destruct H5.
        {
          rewrite <- H5 in *.
          rewrite PTree.gss in H.
          simpl in *.
          rewrite Heqo1.
          rewrite Heqo2.
          right.
          split;eauto.
          destruct inv.
          erewrite uf_id_outside0 in H; try lia.
          congruence.
        }
        {
          pose (nobody_outside e inv).
          unfold lookup, Enodes.lookup, lookup' in l.
          rewrite Heqm in l.
          specialize (l (EApp1 e2 e1) i).
          simpl in l.
          rewrite PTree.gso in H; eauto.
          simpl in *.
          rewrite Heqo1; eauto.
          destruct (PTree.get) eqn:? in H.
          rewrite Heqo3.
          left; split; eauto.
          subst.
          inversion H.
          subst.
          clear H.
          rewrite Heqo1 in l.
          rewrite can_n0 in l.
          rewrite Heqo3 in l.
          intuition lia.
          inversion H.
        }
        }
        {
          rewrite PTree.gso in H; eauto.
          destruct (PTree.get) eqn:? in H.
          2:{ inversion H. }
          setoid_rewrite Heqo3.
          rewrite H.
          left.
          split ;eauto.
          pose (nobody_outside e inv).
          unfold lookup, Enodes.lookup, lookup' in l.
          rewrite Heqm in l.
          specialize (l (EApp1 e0 e1) i).
          simpl in l.
          rewrite can_n1 in l.
          setoid_rewrite Heqo3 in l.
          rewrite can_n0 in l.
          specialize (l H).
          eauto.
        }
        }
        {
        assert (e0 = find (uf e) e2 \/ e0 <> find (uf e) e2) by lia.
        destruct H4.
        {
          rewrite H4 in *.
          rewrite PTree.gss in H.
        assert (e1 = find (uf e) e3 \/ e1 <> find (uf e) e3) by lia.
        destruct H5.
        {
          rewrite <- H5 in *.
          rewrite PTree.gss in H.
          simpl in *.
          rewrite Heqo1.
          right.
          split;eauto.
          destruct inv.
          erewrite uf_id_outside0 in H; try lia.
          congruence.
        }
        {
          rewrite PTree.gso in H; eauto.
          simpl in *.
          rewrite Heqo1; eauto.
          inversion H.
        }
        }
        {
          rewrite PTree.gso in H; eauto.
          destruct (PTree.get) eqn:? in H.
          setoid_rewrite Heqo2.
          rewrite H.
          left.
          split; eauto.
          pose (nobody_outside e inv).
          unfold lookup, Enodes.lookup, lookup' in l.
          rewrite Heqm in l.
          specialize (l (EApp1 e0 e1) i).
          simpl in l.
          rewrite can_n1 in l.
          setoid_rewrite Heqo2 in l.
          rewrite can_n0 in l.
          specialize (l H).
          eauto.
          inversion H.
        }
      }
    }
    {
      cleanup'.
      subst.
      destruct node; simpl in *.
      2:{
        pose (no_args_eapp1_outside e inv i e0 (max_allocated e)).
        unfold lookup, Enodes.lookup, lookup' in *.
        simpl in *.
        destruct (n2id e) eqn:? in H.
        rewrite Heqm in a.
        destruct (PTree.get) eqn:? in H.
        specialize (a H).
        cleanup'.
        erewrite (uf_id_outside) in H4; try intuition lia.
        specialize (a H).
        cleanup'.
        erewrite (uf_id_outside) in H4; try intuition lia.
      }
      {
        pose (no_args_eapp1_outside e inv i e0 (max_allocated e)).
        unfold lookup, Enodes.lookup, lookup' in *.
        simpl in *.
        destruct (n2id e) eqn:? in H.
        rewrite Heqm in a.
        destruct (PTree.get) eqn:? in H.
        destruct (PTree.get) eqn:? in H.
        specialize (a H).
        cleanup'.
        erewrite (uf_id_outside) in H4; try intuition lia.
        assert (find (uf e) e0 = find (uf e) e1 \/ find (uf e) e0 <> find (uf e) e1) by lia.
        destruct H1.
        {
          rewrite H1 in *; clear H1.
          rewrite PTree.gss in H.
          rewrite Heqo1 in a.
          assert (find (uf e) (max_allocated e) = find (uf e) e2 \/ find (uf e) (max_allocated e) <> find (uf e) e2) by lia.
          destruct H1.
          {
            (* inconsistent *)
            exfalso.
            rewrite H1 in H.
            rewrite PTree.gss in H.
            inversion H.
            clear a.
            subst.
            rewrite <- H1 in *.
            rewrite Heqm in Heqo0.
            clear H1.
            unfold add_enode,Enodes.lookup, lookup' in Heqo0.
            rewrite Heqo1 in Heqo0.
            rewrite Heqo2 in Heqo0.
            clear H.
            destruct g2; cleanup'; simpl in *.
            admit.
            admit.
        }
        {
          rewrite PTree.gso in H.
          specialize (a H).
          cleanup'.
          erewrite (uf_id_outside) in H5; try intuition lia.
          eauto.
        }
        (* assert (find (uf e) e0 = find (uf e) e1 \/ find (uf e) e0 <> find (uf e) e1) by lia.
        destruct H1.
        {
          rewrite H1 in *; clear H1.
          rewrite PTree.gss in H.
          admit.
        }
        {
          rewrite PTree.gso in H.
          specialize (a H).
          cleanup'.
          erewrite (uf_id_outside) in H5; try intuition lia.
          eauto.
        } *)
       }
       admit.
       admit.
    }
  }
  admit.
    Admitted.

  Require Import Eqdep.
  Lemma add_atom_safe : forall {t} n eq e ,
    invariant_egraph e ->
    let '(newe, _) := add_formula e (@Atom1 _ _ n t eq) in
    invariant_egraph newe.
    cbn.
    intros.
    destruct (lookup e (EAtom1 n )) eqn:?; eauto.
    econstructor.
    intros.
    pose proof @lookup_update as updf.
    specialize updf with (1:= H).
    specialize updf with (1:= Heqo).
    specialize updf with (1:= H0).
    pose proof @lookup_update as updg.
    specialize updg with (1:= H).
    specialize updg with (1:= Heqo).
    specialize updg with (1:= H1).
    destruct updf.
    {
      destruct updg.
      eapply H; eauto.
      cleanup'.
      pose H3.
      eapply eq_preserve_type in e0.
      subst.
      pose proof (@atom_correct) as atomg.
      specialize atomg with (1:= H3).
      cleanup'.
      subst.
      cbn in *.
      (* That should be absurd: eid = max allocated *)
      {
        unfold lookup,  Enodes.lookup, lookup' in H1, Heqo.
        simpl in H1,Heqo.
        unfold add_enode in H1.
        unfold lookup,  Enodes.lookup, lookup' in H1.
        destruct (n2id e) eqn:?.
        destruct (PTree.get n t1) eqn:? in H1.
        inversion Heqo.
        congruence.
        rewrite PTree.gss in H1.
        inversion H1.
        pose proof (nobody_lookupF_outside e H _ _ _ H2).
        destruct H.
        erewrite uf_id_outside0 in H5; try lia.
      }
    }
    {
      cleanup'.
      pose H2.
      eapply eq_preserve_type in e0.
      subst.
      pose proof (@atom_correct) as atomf.
      specialize atomf with (1:= H2).
      cleanup'.
      (* destruct atomf. *)
      subst.
      cbn in H0.
      unfold add_enode in H0.
      unfold lookup, Enodes.lookup, lookup' in H0, Heqo.
      cbn in H0, Heqo.
      destruct (n2id e) eqn:?.
      destruct (PTree.get n t1) eqn:? in H0.
      {
        rewrite Heqo0 in *.
        inversion H0.
        destruct updg.
        pose proof (nobody_lookupF_outside e H).
        specialize H5 with (1:= H3).
        subst.
        cbn in *.
        inversion Heqo.
        cleanup'.
        pose proof (@atom_correct) as atomg.
        specialize atomg with (1:= H3).
        cleanup'.
        subst.
        simpl.
        cbn in *.
        rewrite x2 in x6.
        inverseS x6.
        eauto.
      }
      {
        rewrite Heqo0 in *.
        rewrite PTree.gss in H0.
        inversion H0.
        destruct updg.
        pose proof (nobody_lookupF_outside e H).
        specialize H5 with (1:= H3).
        erewrite uf_id_outside in H4; eauto; lia.
        cleanup'.
        pose proof (@atom_correct) as atomg.
        specialize atomg with (1:= H3).
        cleanup'.
        subst.
        simpl.
        cbn in *.
        rewrite x2 in x6.
        inverseS x6.
        eauto.
      }
    }
    {
      cbn.
      intros.
      pose proof (nobody_outside e H).
      unfold add_enode, lookup, Enodes.lookup, lookup' in H0,H1, Heqo.
      simpl in H0.
      subst.
      destruct (n2id e) eqn:?.
      destruct (PTree.get _ _) eqn:? in H0.
      {
        simpl in *.
        cbn in H0.
        specialize (H1 a eid).
        destruct a; simpl in *.
        specialize H1 with (1:=H0).
        lia.
        specialize H1 with (1:=H0).
        lia.
      }
      {
        simpl in *.
        cbn in H0.
        specialize (H1 a eid).
        destruct a; simpl in *.
        specialize H1 with (1:=H0).
        lia.
        rewrite Heqo0 in *.
        assert (n0 = n \/ n0 <> n) by lia .
        destruct H2.
        {
          subst.
          rewrite PTree.gss in H0.
          inversion H0.
          erewrite uf_id_outside; eauto;lia.
        }
        {
          rewrite PTree.gso in H0;
          intuition lia.
        }
      }
    }
    {
      cbn.
      intros.
      pose proof (no_args_eapp1_outside e H).
      unfold add_enode, lookup, Enodes.lookup, lookup' in H0,H1, Heqo.
      simpl in H0.
      subst.
      destruct (n2id e) eqn:?.
      simpl in *.
      destruct (PTree.get _ _) eqn:? in H0.
      {
        simpl in *.
        cbn in H0.
        specialize (H1 eid e1 e2).
        specialize H1 with (1:=H0).
        lia.
      }
      {
        simpl in *.
        cbn in H0.
        specialize (H1 eid e1 e2).
        specialize H1 with (1:=H0).
        lia.
      }
    }
    {
      unfold n2idCanonical.
      cbn.
      unfold lookup, add_enode, Enodes.lookup, lookup' in *.
      destruct H.
        unfold n2idCanonical in sanely_assigned_lookup0.
      unfold lookup, add_enode, Enodes.lookup, lookup' in sanely_assigned_lookup0.
      intros.
      unfold classIsCanonical.
      cbn.
      {
        subst.
        cleanup'.
        destruct (n2id e) eqn:?.
        destruct f eqn:?;
        try auto_specialize;
        unfold classIsCanonical in sanely_assigned_lookup0;
        eauto.
        {
          simpl in *.
          specialize (sanely_assigned_lookup0 f c).
          subst f.
          simpl in *.
          destruct (PTree.get _ _) eqn:? in H.
          {
            rewrite Heqo0 in *.
            inversion Heqo.
          }
          clear Heqo.
          destruct (PTree.get _ _) eqn:? in H.
          {
          destruct (PTree.get _ _) eqn:? in H.
          rewrite Heqo in *.
          rewrite Heqo1 in *.
          specialize (sanely_assigned_lookup0 H).
          eauto.
          inversion H.
          }
          inversion H.
        }
        {
          simpl in *.
          specialize (sanely_assigned_lookup0 f c).
          subst f.
          simpl in *.
          destruct (PTree.get _ _) eqn:? in H.
          {
            rewrite Heqo0 in *.
            inversion Heqo.
          }
          clear Heqo.
          assert (n = n0 \/  n<>n0) by lia.
          destruct H0.
          {
            subst.
            rewrite PTree.gss in H.
            simpl in *.
            inversion H.
            erewrite uf_id_outside0; try lia.
            erewrite uf_id_outside0; try lia.
          }
          {
            erewrite PTree.gso in H; eauto.
          }
        }
      }
    }
    {
      cbn.
      intros.
      destruct H.
      eapply uf_id_outside0.
      lia.
    }
    {
      intros.
      cbn in *.
      change (lookupF f1
                {|
                  max_allocated := max_allocated e + 1;
                  uf := uf e;
                  n2id := add_enode (n2id e) (canonicalize e (EAtom1 n)) (max_allocated e);
                  id2s :=
                    PTree.set (max_allocated e)
                      (max_allocated e, T t,
                      (PTree.Nodes (PTree.set0 n n),
                      PTree.empty (PTree.t (eclass_id * eclass_id))))
                      (id2s e)
                |} = Some c
               ) in H0.
      change ( lookupF f2
       {|
         max_allocated := max_allocated e + 1;
         uf := uf e;
         n2id := add_enode (n2id e) (canonicalize e (EAtom1 n)) (max_allocated e);
         id2s :=
           PTree.set (max_allocated e)
             (max_allocated e, T t,
             (PTree.Nodes (PTree.set0 n n),
             PTree.empty (PTree.t (eclass_id * eclass_id))))
             (id2s e)
       |} = Some c) in H1.
      pose proof (@found_high_in_updated _ _ _ _ _ _ H H0).
      pose proof (@found_high_in_updated _ _ _ _ _ _ H H1).
      destruct H2; destruct H3; cleanup'; try lia.
      eapply wt_egraph; eauto.
      {
        destruct f1; destruct f2; cleanup';
        cbn in *.
        inversion H6.
        inversion H6.
        inversion H6.
        inversion H5; inversion H4.
        subst.
        congruence.
      }
    }
    {
        intros.
        destruct H.
        simpl in *.
        assert ( c < max_allocated e \/ c = max_allocated e) by  lia.
        destruct H.
        erewrite wf_uf0; lia.
        specialize (uf_id_outside0 c).
        rewrite uf_id_outside0.
        lia.
        lia.
    }
    Qed.

 (* Require Import Coq.Program.Equality. *)

  Ltac cleanup := cbn in *;intros;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: _ <-> _ |- _ => destruct H
  | H: exists _, _  |- _ => destruct H
  | H: True  |- _ => clear H
  | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
  | H : ?P, H' : ?P |- _ =>
    let t := type of P in
    assert_succeeds(constr_eq t Prop);
    clear H'
  end.

  Lemma lookupF_eqf : forall {t} (f g : Formula t) e i,
    eqf f g = true ->
    lookupF f e = Some i ->
    lookupF g e = Some i.
    induction f.
    -
     destruct g; cbn.
      {
        intros.
        destruct (lookupF _ _) eqn:? in H0.
        2:{ inversion H0. }
        destruct (lookupF _ _) eqn:? in H0.
        2:{ inversion H0. }
        eapply Bool.andb_true_iff in H.
        cleanup.
        pose H.
        eapply eq_preserve_type in e2.
        inversion e2.
        subst.
        repeat auto_specialize.
        rewrite IHf1.
        rewrite IHf2.
        eauto.
      }
      { intros.  inversion H.  }
    -
     destruct g; cbn.
      (* { intros.  inversion H. } *)
      { intros.  inversion H.  }
      {
        intros.
        destruct t0.
        destruct t1.
        cbn in *.
        destruct (dt_eq' T0 T1) eqn:?; subst.
        eapply Pos.eqb_eq in H.
        subst.
        eauto.
        inversion H.
      }
  Qed.

  Lemma lookup_update_app1 :
  forall {t'} (f'  : Formula t') {t1 t3}
   newe
   (f1 : Formula t3) (f2 : Formula t1)
   e1 e3
   eid0 {new_id2s},
    (* lookupF (App2 f1 f2 f3) newe = None ->  *)
    lookupF f1 newe = Some e1 ->
    lookupF f2 newe = Some e3 ->
    invariant_egraph newe ->
    lookupF f' {| max_allocated := max_allocated newe + 1;
                 uf := uf newe;
                 n2id :=  add_enode (n2id newe) (EApp1 e1 e3) (max_allocated newe);
                 id2s := new_id2s |}
    = Some eid0 ->
    lookupF f' newe = Some eid0 \/
    (exists  (f'1 : Formula (t1 ~> t')) (f'2 : Formula t1)  ,
      lookupF f'1 newe = Some e1 /\
      lookupF f'2 newe = Some e3 /\
      eqf f' (App1 f'1 f'2) = true /\
      eid0 = max_allocated newe).
      Admitted.
      (* induction f'.
      2:{
        intros.
        cbn in *.
        left.
        unfold lookup.
        unfold add_enode in H2.
        cbn in *; eauto.
      }
      {
        intros.
        cbn in H2.
        specialize (IHf'1) with (1:= H).
        specialize (IHf'1) with (1:= H0).
        specialize (IHf'1) with (1:= H1).
        (* specialize (IHf'1) with (1:= H2). *)
        specialize (IHf'2) with (1:= H).
        specialize (IHf'2) with (1:= H0).
        specialize (IHf'2) with (1:= H1).
        (* specialize (IHf'2) with (1:= H2). *)
        repeat auto_specialize.
        cbn.
        destruct (lookupF f'1 _) eqn:? in H2.
        2:{
          inversion H2.
        }
        destruct (lookupF f'2 _) eqn:? in H2.
        2:{
          inversion H2.
        }
        repeat auto_specialize.
        destruct IHf'1.
        rewrite H3.
        destruct IHf'2.
        rewrite H4.
        {
          unfold update_map in H2.
          cbn in H2.
          subst.
          destruct (_&&_) eqn:? in H2.
          cbn in H2.
          pose proof (lookupF_canonical newe ) as canonicalLookup.
          auto_specialize.
          destruct H1.
          eapply Bool.andb_true_iff in Heqb.
          cleanup'.
          eapply Nat.eqb_eq in H1.
          eapply Nat.eqb_eq in H5.
          pose (canonicalLookup _ f1 e1) as e1_c.
          pose (canonicalLookup _ f2 e3) as e3_c.
          pose (canonicalLookup _ f'1 n) as e_c.
          pose (canonicalLookup _ f'2 n0) as e0_c.
          do 4 auto_specialize.
          rewrite e1_c in H1.
          rewrite e_c in H1.
          rewrite e3_c in H5.
          rewrite e0_c in H5.
          subst.
          pose proof (wt_egraph0 _ _ _ _ _ H H3) as luf1.
          pose proof (wt_egraph0 _ _ _ _ _ H0 H4) as luf2.
          cleanup'.
          subst.
          right.
          eexists; eexists.
          split.
          exact H3.
          split.
          exact H4.
          split.
          rewrite !eqf_refl.
          eauto.
          inversion H2.
          eauto.
          eauto.
        }
        {
          cleanup.
          rename H7 into reskj.
          unfold update_map in H2.
          subst.
          match type of Heqo0 with
          | lookupF ?a ?b = Some ?c =>
            assert (lookupF (App1 x x0) b = Some c)
          end.
          eapply lookupF_eqf; eauto.
          destruct (_ && _) eqn:? in H2.
          (* Destruction of H4 leads to one similar case for the false branch.  *)
          2:{
            destruct H1.
            specialize no_args_eapp1_outside0 with (1:= H2).
            cleanup'.
            unfold classIsCanonical in uf_id_outside0.
            unfold find in H8, uf_id_outside0; subst; cbn in *.
            erewrite uf_id_outside0 with (a := max_allocated newe) in H8; lia.
          }
          pose proof (lookupF_canonical newe ) as canonicalLookup.
          specialize (canonicalLookup H1).
          eapply Bool.andb_true_iff in Heqb.
          destruct Heqb.
          eapply Nat.eqb_eq in H8, H9.
          pose (canonicalLookup _ f2 e3) as e3_c.
          auto_specialize.
          rewrite e3_c in H9.
          pose proof (nobody_lookupF_outside newe H1 _ _ _ H0).
          destruct H1.
          unfold classIsCanonical in uf_id_outside0.
          unfold find in H9, uf_id_outside0.
          erewrite uf_id_outside0 in H9; cbn; try lia.
        }
        {
          cleanup.
          rename H6 into reskj.
          subst.
          match type of Heqo with
          | lookupF ?a ?b = Some ?c =>
            assert (lookupF (App1 x x0) b = Some c)
          end.
          eapply lookupF_eqf; eauto.
          destruct (_ && _) eqn:? in H2.
          (* Destruction of H4 leads to one similar case for the false branch.  *)
          2:{
            destruct H1.
            specialize no_args_eapp1_outside0 with (1:= H2).
            cleanup'.
            unfold classIsCanonical in uf_id_outside0.
            unfold find in H1, uf_id_outside0; subst; cbn in *.
            erewrite uf_id_outside0 with (a := max_allocated newe) in H1; lia.
          }
          pose proof (lookupF_canonical newe ) as canonicalLookup.
          specialize (canonicalLookup H1).
          eapply Bool.andb_true_iff in Heqb.
          destruct Heqb.
          eapply Nat.eqb_eq in H7, H8.
          pose (canonicalLookup _ f1 e1) as e1_c.
          auto_specialize.
          rewrite e1_c in H7.
          pose proof (nobody_lookupF_outside newe H1 _ _ _ H3).
          destruct H1.
          unfold classIsCanonical in uf_id_outside0.
          unfold find in H7, uf_id_outside0.
          erewrite uf_id_outside0 in H7; cbn; try lia.
        }
      }
      Qed. *)


  Lemma add_app1_safe: forall {t t1} e
  (f1 : Formula (t1 ~> t))
   (f2 : Formula t1)
    e1 e3 {new_id2s},
    invariant_egraph e ->
    lookupF f1 e = Some e1 ->
    lookupF f2 e = Some e3 ->
    invariant_egraph
      {| max_allocated := max_allocated e + 1;
         uf := uf e;
         n2id := add_enode (n2id e) (EApp1 e1 e3) (max_allocated e);
         id2s := new_id2s |}.
    Admitted.
    (* intros.
    econstructor.
    intros.
    pose proof @lookup_update_app1 as updf.
    (* specialize updf with (1:= H3). *)
    specialize updf with (1:= H0).
    specialize updf with (1:= H1).
    (* specialize updf with (1:= H2). *)
    specialize updf with (1:= H).
    specialize updf with (1:= H2).
    pose proof @lookup_update_app1 as updg.
    (* specialize updg with (1:= H3). *)
    specialize updg with (1:= H0).
    specialize updg with (1:= H1).
    (* specialize updg with (1:= H2). *)
    specialize updg with (1:= H).
    specialize updg with (1:= H3).
    destruct updf.
    {
      destruct updg.
      eapply H; eauto.
      cleanup'.
      pose proof (nobody_lookupF_outside _ H) as nobody_outside0.
      specialize (nobody_outside0) with (1:= H4).
      lia.
    }
    {
      cleanup'.
      pose H6.
      eapply eq_preserve_type in e0.
      subst.
      destruct updg.
      {
         pose proof (nobody_lookupF_outside _ H) as nobody_outside0.
         specialize (nobody_outside0) with (1:= H7).
         lia.
      }
      {
        cleanup.
        transitivity (interp_formula ctx (App1 x x0)).
        eapply eq_correct.
        eauto.
        transitivity (interp_formula ctx (App1 x1 x2 )).
        2:{
          symmetry.
          eapply eq_correct.
          eauto.
        }
        simpl.
        assert (interp_formula ctx x = interp_formula ctx x1).
        eapply H; eauto.
        assert (interp_formula ctx x0 = interp_formula ctx x2).
        eapply H; eauto.
        rewrite H11.
        rewrite H12.
        eauto.
      }
    }
    {
      cbn.
      intros.
      destruct a.
      cbn in *.
      destruct (_ && _) eqn:? in H2.
      inversion H2; subst; lia.
      destruct H.
      repeat auto_specialize.
      unfold find in no_args_eapp1_outside0.
      cleanup'.
      lia.
      destruct H.
      repeat auto_specialize.
      lia.
    }
    {
      unfold n2idCanonical.
      cbn.
      intros.

      destruct (_ && _) eqn:?.
      {
        eapply Bool.andb_true_iff in Heqb.
        cleanup'.
        eapply Nat.eqb_eq in H4.
        eapply Nat.eqb_eq in H3.
        unfold find in *.
        pose proof (@lookupF_canonical _ H  _ _ _ H0).
        pose proof (@lookupF_canonical _ H  _ _ _ H1).
        rewrite H5 in H3.
        rewrite H6 in H4.
        rewrite <- H3.
        rewrite <- H4.
        pose proof (nobody_lookupF_outside _ H).
        split; erewrite H7; eauto; lia.
      }
      subst.
      destruct H.
      unfold n2idCanonical in sanely_assigned_lookup0.
      cleanup'.
      try auto_specialize;
      unfold classIsCanonical in sanely_assigned_lookup0;
      eauto.
      specialize (no_args_eapp1_outside0 _ _ _ H2).
      cleanup'.
      rewrite H.
      rewrite H3.
      cbn; lia.
    }
    {
      unfold n2idCanonical.
      cbn.
      intros.
      destruct f.
      destruct (_ && _) eqn:?.
      {
        inversion H2.
        subst.
        cbn.
        destruct H.
        specialize (uf_id_outside0 (max_allocated e)).
        unfold classIsCanonical in *.
        cbn in *.
        unfold find in uf_id_outside0.
        erewrite uf_id_outside0; try lia.
      }
      {
        unfold classIsCanonical in *.
        cbn in *.
        destruct H.
        unfold n2idCanonical in *.
        specialize (sanely_assigned_lookup0 _ _ H2).
        eauto.
      }
      {
        unfold classIsCanonical in *.
        cbn in *.
        destruct H.
        unfold n2idCanonical in *.
        specialize (sanely_assigned_lookup0 _ _ H2).
        eauto.
      }
    }
    {
      cbn.
      intros.
      destruct H.
      eapply uf_id_outside0.
      lia.
    }
    {
      intros.
      cbn in *.
      pose proof (@found_high_in_updated _ _ _ _ _ _ H H2).
      pose proof (@found_high_in_updated _ _ _ _ _ _ H H3).
      destruct H4; destruct H5; cleanup'; try lia.
      eapply wt_egraph; eauto.
      {
        destruct f0; destruct f3; cleanup';
        cbn in *.
        2:{ inversion H6. }
        2:{ inversion H7. }
        2:{ inversion H7. }
        inversion H8; inversion H10.
        subst.
        destruct H.
        pose proof (@wt_egraph0 _ _ _ _ _ H7 H5).
        inversion H.
        eauto.
      }
    }
{
        intros.
        destruct H.
        simpl in *.
        assert ( c < max_allocated e \/ c = max_allocated e) by  lia.
        destruct H.
        erewrite wf_uf0; lia.
        specialize (uf_id_outside0 c).
        rewrite uf_id_outside0.
        lia.
        lia.
    }
    Qed. *)

    (* Another exam exercise:
     In this case we need to be careful to not make a statement too general
     that's something to have the student look for as well. *)
  Theorem lookup_already_there' :
    forall t  (f : Formula t) (e : egraph)  (e2 : eclass_id),
    lookupF f e = Some e2 ->
    add_formula e f = (e, e2).
    induction f.
    {
      intros.
      cbn in H.
      destruct (lookupF _ _) eqn:? in H.
      2:{ inversion H.  }
      destruct (lookupF _ _) eqn:? in H.
      2:{ inversion H.  }
      cbn.
      destruct (add_formula _ _) eqn:?.
      pose proof (IHf1 _ _ Heqo).
      assert (e0 = e4) by congruence.
      assert (e = e3) by congruence.
      subst.
      destruct (add_formula e3 f2) eqn:?.
      pose proof (IHf2 _ _ Heqo0).
      cleanup'.
      assert (e0 = e1) by congruence.
      assert (e = e3) by congruence.
      subst.
      subst.
      rewrite H.
      eauto.
    }
    {
      intros.
      cbn in *.
      rewrite H.
      eauto.
    }
    Qed.

  Lemma add_formula_safe : forall {t} (f : term t) e ,
    invariant_egraph e ->
    let '(newe, newal) := add_formula e f in
    invariant_egraph newe /\
    lookupF f newe = Some newal /\
    (forall t' (g : Formula t') old,
      (lookupF g e = Some old ->
       lookupF g newe = Some old) ).
       (* Admitted. *)
    induction f.
    2:{
      intros.
      pose proof @add_atom_safe.
      destruct (add_formula e0 _) eqn:?.
      repeat auto_specialize.
      specialize (H0 _ n e).
      rewrite Heqp in H0.
      eauto.
      remember (Atom1 n t0 e).
      cbn in *.
      assert (lookupF f e1 = Some e2).
      subst f.
      cbn in *.
      destruct (lookup e0 _) eqn:? in Heqp.
      {
      inversion Heqp.
      subst.
      eauto.
      }
      {
      inversion Heqp.
      subst.
      cbn.
      unfold lookup, Enodes.lookup, lookup' in Heqo |-*.
      simpl in *.
      clear Heqp.
      unfold add_enode.
      unfold lookup, Enodes.lookup, lookup'.
      destruct (n2id e0).
      destruct (PTree.get _ _) eqn:? in Heqo.
      inversion Heqo.
      rewrite Heqo0.
      rewrite PTree.gss.
      simpl.
      destruct H.
      erewrite uf_id_outside0   by lia.
      eauto.
      }
      split; eauto.
      split; eauto.
      intros.
      subst.
      simpl in *.
      destruct (lookup e0 _) eqn:? in Heqp.
      {
        inversion Heqp.
        subst; eauto.
      }
      {
        inversion Heqp.
        subst.
        cbn in H1.
        pose proof @lookup_add_not_there.
        assert (lookup e0 (EAtom1 n ) = None).
        unfold lookup.
        cbn in *; eauto.
        epose proof (H3 _ _ _ _ _ _ H H4 H2 ).
        eauto.
      }
    }
    {
      intros.
      pose proof (IHf1 _ H ).
      destruct (add_formula e f1) eqn:?.
      cleanup'.
      pose proof (IHf2 _ H0).
      destruct (add_formula e0 f2) eqn:?.
      cleanup'.
      cleanup'.
      cbn - [eqf lookupF].
      rewrite Heqp.
      rewrite Heqp0.
      (* destruct (lookupF (App1 f1 f2) _) eqn:?; eauto. *)
      destruct (lookup e2 (EApp1 e1 e3)) eqn:?; eauto.
      2:{
        split.
        {
          pose lookupF_canonical.
          specialize c with (2:= H4).
          specialize (c H3).
          rewrite c.
          specialize H5 with (1:= H1).
          pose lookupF_canonical.
          specialize c0 with (2:= H5).
          specialize (c0 H3).
          rewrite c0.
          pose proof @add_app1_safe; eauto.
        }
        split.
        {
          cbn.
          simpl in *.
          epose proof (@lookup_add_not_there _ f2 e2 (EApp1 e1 e3 ) e3 _ H3 Heqo H4).
          epose proof (@lookup_add_not_there _ f1 e2 (EApp1 e1 e3 ) e1 _ H3 Heqo (H5 _ _ _ H1)).
          rewrite H7.
          rewrite H6.
          unfold lookup, Enodes.lookup, lookup', add_enode in Heqo |-*.
          simpl.
          destruct (n2id e2) eqn:?.
          pose proof (H5 _ _ _ H1).
          pose proof (@lookupF_canonical _ H3 _ _ _ H8) as n_cano.
          pose proof (@lookupF_canonical _ H3 _ _ _ H4) as n0_cano.
          rewrite n_cano, n0_cano; eauto.
          simpl in *.
          unfold lookup, Enodes.lookup, lookup', add_enode in Heqo |-*.
          erewrite n_cano in Heqo.
          destruct (PTree.get _ _) eqn:? in Heqo.
          rewrite Heqo0 in *.
          erewrite n0_cano in Heqo.
          destruct (PTree.get _ _) eqn:? in Heqo.
          inversion Heqo.
          rewrite Heqo1.
          rewrite PTree.gss.
          rewrite PTree.gss.
          simpl.
          destruct H3.
          erewrite uf_id_outside0   by lia.
          intuition lia.
          rewrite Heqo0.
          rewrite PTree.gss.
          rewrite PTree.gss.
          simpl.
          destruct H3.
          erewrite uf_id_outside0   by lia.
          intuition lia.
        }
        {
          intros.
          pose proof  (H2 _ _ _ H6) as gint1.
          pose proof  (H5 _ _ _ gint1) as gint2.
          epose proof (@lookup_add_not_there _ g e2 (EApp1 e1 e3 ) old _ H3 Heqo gint2).
          eauto.
        }
      }
      {
        split.
        {
          pose proof @add_app1_safe; eauto.
        }
        split.
        {
          cbn.
          rewrite H4.
          pose proof (H5 _ _ _ H1).
          rewrite H6.
          eauto.
        }
        {
          intros.
          eapply H5.
          eapply H2.
          eauto.
        }
      }
    }
    Qed.

    Fixpoint substF {t t'} (e : egraph) (f : Formula t)
    (from : eclass_id)
    (to : Formula t') : Formula t.
    unshelve refine (let sub := _ in _).
    2:{
      destruct f.
      {
        pose (substF _ _ e f1 from to) as f'1 .
        pose (substF _ _ e f2 from to) as f'2 .
        exact (App1 f'1 f'2).
      }
      {
        exact (Atom1 n t0 e0).
      }
    }
    cbn in sub.
    destruct (dt_eq' t' t).
        {
          subst.
          destruct (lookupF sub e) .
          {
            destruct (Pos.eqb e0 from).
            {
              exact to.
            }
            exact sub.
          }
          {
            exact sub.
          }
        }
        {
          exact sub.
        }
    Defined.

    Lemma merge_helper : forall e,
    invariant_egraph e ->
    forall newe {t} (f1 : Formula t) (f2 : Formula t)
    (e1 e2 : eclass_id),
    lookupF f1 e = Some e1 ->
    lookupF f2 e = Some e2 ->
    merge e e1 e2 = newe ->
    forall  {t'} (f : Formula t') (e3 : eclass_id),
    lookupF f newe = Some e3 ->
    lookupF (substF e f e1 f2) e = Some e3.
    Admitted.
    (* intros.
    revert dependent f2.
    revert dependent f1.
    revert dependent e1.
    revert dependent e2.
    revert dependent e3.
    revert dependent f.
    induction f.
    {
      intros.
      (* pose proof H3 as init. *)
      simpl in H3.
      destruct (lookupF _ _) eqn:? in H3.
      2:{ inversion H3. }
      destruct (lookupF _ _) eqn:? in H3.
      2:{ inversion H3. }

      repeat auto_specialize.
      subst.

      (* H3 represente la classe dans l'egraph merge *)
      cbn in *.
      destruct (dt_eq' t td).
      2:{
        simpl.
        rewrite IHf1.
        rewrite IHf2.
        pose proof (@lookupF_canonical e H ) as H2.
        unfold merge,lookup, merge_n2id, Enodes.lookup, lookup' in H3 .
        simpl in H3.
        destruct (n2id e) eqn:? in H3.
        (* rewrite Heqm.
        simpl.

        (* erewrite (H2 _ _ _ IHf2) in H3;eauto. *)
        (* 2:{ inversion H3.  } *)
        pose proof (@lookupF_canonical _ H _ _ _ IHf1) as n_cano.
        pose proof (@lookupF_canonical _ H _ _ _ IHf2) as n2_cano.
        pose proof (@lookupF_canonical _ H _ _ _ H0) as n3_cano.
        pose proof (@lookupF_canonical _ H _ _ _ H1) as n4_cano.
        rewrite n3_cano in H3 .
        rewrite n4_cano in H3.
        rewrite n3_cano in H3.
        rewrite n2_cano.
        rewrite n_cano.
         *)
        (* destruct (Nat.eq_dec _ _); inversion H3; subst; eauto. *)
        assert (lookupF (App1 (substF e f1 e1 f3) (substF e f2 e1 f3)) e = Some e1).
        cbn.
        rewrite IHf1.
        rewrite IHf2.

        unfold merge,lookup, merge_n2id, Enodes.lookup, lookup' in H3 |-*.
        rewrite Heqm.
        simpl.
        destruct (PTree.get _ _) eqn:? in H3.
        2:{ inversion H3. }
        destruct (PTree.get _ _) eqn:? in H3.
        2:{ inversion H3. }
        simpl. unfold union,find in *|-.
        admit.
         (* rewrite n_cano.
        rewrite n2_cano.
        eauto. *)
        destruct H.
        specialize (wt_egraph0 _ _ _ _ _ H4 H0).
        contradiction n; eauto.
      }
      {
        destruct e5.
        cbn in *.
        rewrite IHf1, IHf2.
        pose proof (@lookupF_canonical e H ) as H2.
        epose (H2 _ _  _ IHf2).
        admit.
         (* in H3;eauto.
        destruct (n2id _ _) eqn:? in H3.
        2:{ inversion H3.  }
        {
          pose proof (@lookupF_canonical _ H _ _ _ IHf1) as n_cano.
          rewrite n_cano in Heqo1.
          destruct (Nat.eq_dec _ _) eqn:? in H3.
          subst.
          rewrite Heqo1.
          rewrite Heqs.
          inversion H3; subst; eauto.
          inversion H3; subst; eauto.
          rewrite Heqo1.
          rewrite Heqs.
          simpl.
          rewrite IHf1.
          rewrite IHf2.
          eauto.
        } *)
      }
    }
  {
      intros.
      (* pose proof H3 as init. *)
      simpl in H3.
      simpl.
      subst.

      (* H3 represente la classe dans l'egraph merge *)
      simpl in *.
      destruct t0.
      cbn.
      destruct (dt_eq' t T0).
      2:{
        simpl.
        (* unfold lookup, Enodes.lookup, lookup', merge, merge_n2id in *. *)
        simpl in *.
        eauto.
        destruct (n2id e ) eqn:? in H3;
        unfold lookup;
        cbn.
        rewrite Heqm.
        (* 2:{ inversion H3.  }
        destruct (Nat.eq_dec _ _ );
        inversion H3; subst; eauto. *)
        assert (lookupF (Atom1 n {| T:=T0; state:=state0 |} e0) e = Some e1) .
        cbn; unfold lookup; cbn; eauto.
        unfold Enodes.lookup, lookup'.
        rewrite Heqm.
        admit.
        destruct H.
        specialize (wt_egraph0 _ _ _ _ _  H2 H0).
        contradiction n0; eauto.
      }
      {
        destruct e4.
        cbn in *.
        unfold lookup,Enodes.lookup, lookup',merge  in *.
        simpl in*.
        destruct (n2id e) eqn:?.
        unfold lookup in *.

        unfold merge_n2id, lookup,Enodes.lookup, lookup',merge  in *.
        admit.
        (* 2:{ inversion H3.  }
        {
          cbn in *.
          rewrite Heqo.
          destruct (Nat.eq_dec _ _) eqn:? in H3.
          rewrite Heqs.
          inversion H3; subst; eauto.
          rewrite Heqs.
          simpl.
          inversion H3; subst; eauto.
        } *)
      }
    } *)
       (* Qed. *)

    Lemma subst_helper :
    forall {t'} (f : Formula t'),
    forall {t} (f1 : Formula t) (f2 : Formula t) e (e1 : eclass_id),
    invariant_egraph e ->
    interp_formula ctx f1 = interp_formula ctx f2 ->
    lookupF f1 e = Some e1 ->
    interp_formula ctx f = interp_formula ctx (substF e f e1 f2).
    Ltac t := subst; simpl; eauto.
    Admitted.
    (* induction f.
    - intros.
      repeat auto_specialize.
      simpl.
      rewrite  IHf1, IHf2.
      simpl.
      destruct (dt_eq' t0 td) eqn:?.
      2:{
        simpl.
        eauto.
      }
      destruct e0.
      simpl.
      remember (eq_rect_r  _ _ _ ).
      cbn in Heqy.
      remember (y f3).
      subst y.
      destruct (lookupF _ _) eqn:? in Heqf; try solve[ t ].
      destruct (lookupF _ _) eqn:? in Heqf; try solve[ t ].
      destruct (n2id _ _) eqn:? in Heqf; try solve [ t ].
      destruct (Nat.eq_dec _ _) eqn:? in Heqf; try solve [ t ].
      subst.
      rewrite <- H0.
      destruct H.
      erewrite (correct0 _ f0 (App1 (substF e f1 e1 f3) (substF e f2 e1 f3))).
      eauto.
      eauto.
      simpl.
      rewrite Heqo, Heqo0.
      eauto.
    -
      intros.
      simpl.
      destruct t0.
      cbn in *.
      destruct (dt_eq' t T0) eqn:?.
      2:{
        simpl.
        eauto.
      }
      destruct e2.
      remember (eq_rect_r _  _ _).
      remember (y f2).
      subst y.
      cbn in *.
      unfold lookup in *.
      cbn in *.
      destruct (n2id _ _) eqn:? in Heqf; try solve [ t ].
      destruct (Nat.eq_dec _ _) eqn:? in Heqf; try solve [ t ].
      subst.
      rewrite <- H0.
      destruct H.
      erewrite (correct0 _ f1 (Atom1 n {| T:= t; state := state0 |} e)).
      eauto.
      eauto.
      simpl.
      unfold lookup; cbn.
      eauto.
    Qed. *)

Lemma apply_add_formula : forall {t} (f : Formula t) e newe,
    invariant_egraph e ->
    (fst (add_formula e f)) = newe ->
    invariant_egraph newe.
    pose proof @add_formula_safe.
    intros.
    repeat auto_specialize.
    specialize (H _ f).
    destruct (add_formula e f) eqn:?;
    cleanup'; eauto.
    cbn in H1; subst; eauto.
Qed.
Theorem apply_merge : forall {t} (e newe: egraph) (f g : Formula t),
    invariant_egraph e ->
    interp_formula ctx f = interp_formula ctx g ->
    (fst (fst (mergeF e f g)) = newe) ->
    invariant_egraph newe.
    pose proof @merge_preserve.
    intros.
    repeat auto_specialize.
    destruct (mergeF _ _ _) eqn:?;
    cleanup'; eauto.
    cbn in H2; subst; eauto.
    destruct p.
    eauto.
Qed.

  Definition app_d {quantifiermap1 :list (type )}
  (l1 : DeepList quantifiermap1)

  {quantifiermap2 :list (type )}
  (l2 : DeepList quantifiermap2)
: DeepList (quantifiermap1 ++ quantifiermap2).
  induction l1.
  2:{
    simpl.
    eauto.
  }
  {
    simpl.
    econstructor.
    eauto.
    eauto.
  }
  Defined.

  Definition deep_rev {quantifiermap' :list (type )} (l : DeepList quantifiermap')
: DeepList (rev quantifiermap').
  induction l.
  2:{
    simpl.
    econstructor.
  }
  -
    simpl.
    eapply add_end.
    eauto.
    eauto.
    Defined.


  Definition nth_deep {quantifiermap'} n t (pf : nth_error quantifiermap' n = Some t)
      (l : DeepList quantifiermap') : t_denote (typemap := typemap)t.
  generalize dependent quantifiermap'.
  induction n.
  -
    intros.
    destruct quantifiermap'.
    inversion pf.
    simpl in *.
    inversion pf.
    subst.
    inversion l.
    exact v.
  -
    intros.
    destruct quantifiermap'.
    inversion pf.
    cbn in  pf.
    eapply IHn.
    exact pf.
    inversion l. exact cdr.
  Defined.


End Pattern.
  (* The DeepList represents an instantiation of quantifiers, from the context,
     the values are Formulas from the context? *)
  Inductive DeepList : list (type ) -> Type :=
    | DCons : forall (t : type )
              (v : t_denote (typemap := typemap) t)
              {tcdr : list (type )} (cdr : DeepList tcdr),
      DeepList (t :: tcdr)
    | DNil : DeepList nil.

  (* Directly brought from Coq to avoid opacity issues *)
  Definition app_assoc' (A : Type) (l m n : list A):  l ++ m ++ n = (l ++ m) ++ n :=
  list_ind (fun l0 : list A => l0 ++ m ++ n = (l0 ++ m) ++ n)
    (let H : n = n := eq_refl in
     (let H0 : m = m := eq_refl in
    (let H1 : A = A := eq_refl in
       (fun (_ : A = A) (_ : m = m) (_ : n = n) => eq_refl) H1) H0) H)
    (fun (a : A) (l0 : list A) (IHl : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
     let H : l0 ++ m ++ n = (l0 ++ m) ++ n := IHl in
     (let H0 : a = a := eq_refl in
      (let H1 : A = A := eq_refl in
       (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
        eq_trans
          (f_equal (fun f : list A -> list A => f (l0 ++ m ++ n)) eq_refl)
          (f_equal (cons a) H4)) H1) H0) H) l.

  Definition app_nil_r' :=
    fun (A : Type) (l : list A) =>
    list_ind (fun l0 : list A => l0 ++ nil = l0)
     (let H : A = A := eq_refl in (fun _ : A = A => eq_refl) H)
  (fun (a : A) (l0 : list A) (IHl : l0 ++ nil = l0) =>
   let H : l0 ++ nil = l0 := IHl in
   (let H0 : a = a := eq_refl in
        (let H1 : A = A := eq_refl in
     (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ nil = l0) =>
      eq_trans (f_equal (fun f : list A -> list A => f (l0 ++ nil)) eq_refl)
        (f_equal (cons a) H4)) H1) H0) H) l.

Require Coq.Lists.List. Import List.ListNotations.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.PropExtensionality.

Ltac propintu := intros; apply propositional_extensionality; intuition idtac.
Module PropLemmas.
  Lemma eq_True: forall (P: Prop), P -> P = True. Proof. propintu. Qed.
  Lemma and_True_l: forall (P: Prop), (True /\ P) = P. Proof. propintu. Qed.
  Lemma and_True_r: forall (P: Prop), (P /\ True) = P. Proof. propintu. Qed.
  Lemma eq_eq_True: forall (A: Type) (a: A), (a = a) = True. Proof. propintu. Qed.
End PropLemmas.


Section WithLib.
  Context (word: Type)
          (ZToWord: Z -> word)
          (unsigned: word -> Z)
          (wsub: word -> word -> word)
          (wadd: word -> word -> word)
          (wopp: word -> word).

  Context (wadd_0_l: forall a, wadd (ZToWord 0) a = a)
          (wadd_0_r: forall a, wadd a (ZToWord 0) = a)
          (wadd_comm: forall a b, wadd a b = wadd b a)
          (wadd_assoc: forall a b c, wadd a (wadd b c) = wadd (wadd a b) c)
          (wadd_opp: forall a, wadd a (wopp a) = ZToWord 0).

  (* Preprocessing: *)
  Context (wsub_def: forall a b, wsub a b = wadd a (wopp b)).

  (* With sideconditions: *)
  Context (unsigned_of_Z: forall a, 0 <= a < 2 ^ 32 -> unsigned (ZToWord a) = a).

  Context (mem: Type)
          (word_array: word -> list word -> mem -> Prop)
          (sep: (mem -> Prop) -> (mem -> Prop) -> (mem -> Prop)).

  Context (sep_comm: forall P Q: mem -> Prop, sep P Q = sep Q P).

  Ltac pose_list_lemmas :=
    pose proof (@List.firstn_cons word) as firstn_cons;
    pose proof (@List.skipn_cons word) as skipn_cons;
    pose proof (@List.app_comm_cons word) as app_cons;
    pose proof (@List.firstn_O word) as firstn_O;
    pose proof (@List.skipn_O word) as skipn_O;
    pose proof (@List.app_nil_l word) as app_nil_l;
    pose proof (@List.app_nil_r word) as app_nil_r.

  Ltac pose_prop_lemmas :=
    pose proof PropLemmas.and_True_l as and_True_l;
    pose proof PropLemmas.and_True_r as and_True_r;
    pose proof PropLemmas.eq_eq_True as eq_eq_True.

  Definition lipstick {A:Type} {a:A} := a.

  Lemma simplification1: forall (a: word) (w1_0 w2_0 w1 w2: word) (vs: list word)
                               (R: mem -> Prop) (m: mem) (cond0_0 cond0: bool)
        (f g: word -> word) (b: word)
        (HL: length vs = 3%nat)
        (H : sep (word_array a
          (List.firstn
             (Z.to_nat (unsigned (wsub (wadd a (ZToWord 8)) a) / 4))
             ((if cond0_0 then [w1_0] else if cond0 then [w2_0] else List.firstn 1 vs) ++
              [w1] ++ List.skipn 2 vs) ++
           [w2] ++
           List.skipn
             (S (Z.to_nat (unsigned (wsub (wadd a (ZToWord 8)) a) / 4)))
             ((if cond0_0 then [w1_0] else if cond0 then [w2_0] else List.firstn 1 vs) ++
              [w1] ++ List.skipn 2 vs))) R m),
      f (wadd b a) = g b /\
      sep R (word_array a [List.nth 0 vs (ZToWord 0); w1; w2]) m = True /\
      f (wadd b a) = f (wadd a b).
  Proof.
    intros.

    pose_list_lemmas.
    pose_prop_lemmas.

    intros.
    specialize (eq_eq_True word).

    (* Make problems simpler by only considering one combination of the booleans,
       but it would be nice to treat all of them at once *)
    replace cond0_0 with false in * by admit.
    replace cond0 with false in * by admit.

    (* Make problem simpler by not requiring side conditions: since we know the
       concrete length of vs, we can destruct it, so firstn and skipn lemmas can
       be on cons without sideconditions rather than on app with side conditions
       on length *)
    destruct vs as [|v0 vs]. 1: discriminate HL.
    destruct vs as [|v1 vs]. 1: discriminate HL.
    destruct vs as [|v2 vs]. 1: discriminate HL.
    destruct vs as [|v3 vs]. 2: discriminate HL.
    clear HL.
    cbn.
    (* cbn in H. <-- We don't do this cbn because now that we've done the above
       destructs, cbn can do much more than it usually would be able to do. *)

    (* Preprocessing *)
    rewrite wsub_def in *.
    clear wsub_def.
    apply PropLemmas.eq_True in H.

    (* Rewrites with sideconditions, currently also part of separate preprocessing: *)
    pose proof (unsigned_of_Z 8 ltac:(lia)) as A1.

    (* Constant propagation rules, manually chosen to make things work,
       TODO how to automate? *)
    pose proof (eq_refl : (Z.to_nat (8 / 4)) = 2%nat) as C1.

  Ltac reify_interp_roundtrip h :=
   let t := type of h in
   let tmap := extend_typemap (EGraphList.nil : EGraphList.list Type) t in
   let tname := fresh "tm" in
   pose tmap as tname;
   let cmap := extend_constmap tname (EGraphList.nil : EGraphList.list (dyn tname )) t in
   (* idtac "tmap" tmap "constmap" cmap; *)
   time let rH := reify_expr tname cmap (@EGraphList.nil type) HNil t in
   pose (interp_term tname cmap (@EGraphList.nil type) (@HNil : hlist EGraphList.nil) rH eq_refl).

  Time reify_interp_roundtrip H.
  let tH := type of H in
  assert (t = tH) .
  + Time reflexivity.
*)

Notation "'subst!' y 'for' x 'in' f" :=
  (match y with x => f end) (at level 10, f at level 200).

Ltac beta1 func arg :=
  lazymatch func with
  | (fun a => ?f) => constr:(subst! arg for a in f)
  end.

Ltac toplevel_betas t :=
  match t with
  | ?f ?a => let f' := toplevel_betas f in beta1 f' a
  | _ => t
  end.

Goal True.
  (* We can swap rhs while body keeps referring to y: *)
  lazymatch constr:(let x := 1 in x + x) with
  | (let y := ?rhs in ?body) => let r := constr:(let y := 2 in body) in pose r
  end.
  (* but we can't match on `body`:
  lazymatch constr:(let x := 1 in x + 2) with
  | (let y := ?rhs in ?body) => let r := constr:(let y := 2 in
      ltac:(lazymatch body with
            | ?a + ?b => exact (b + a)
            end)) in pose r
  end.
  *)
  (* but with higher-order matching & beta1, we can: *)
  lazymatch constr:(let x := 1 in x + 3) with
  | (let y := ?rhs in @?body y) => let r := constr:(let y := 2 in ltac:(
      let body' := beta1 body y in
      lazymatch body' with
      | ?a + ?b => exact(b + a)
      end)) in pose r
  end.
Abort.

(* Expects a constmap_ref in context, of shape
   (let tm := <typemap> in let cm := <constmap> in tt). *)
Ltac reify_q_equ t :=
  let new_cm := open_constr:(_) in
  let new_thm := open_constr:(_ : reified_q_equ) in
  let __ := lazymatch constmap_ref_get with
  | (let tmName := ?oldtypemap_u in let cmName := @?oldconstmapFun tmName in tt) =>
    open_constr:(ltac:(
      let H := fresh in
      intro H;
      let varmap := make_varmap in
      let g := lazymatch goal with |- ?g => g end in
      let tmap' := extend_typemap oldtypemap_u g in
      let types_of_varmap :=
        match type of varmap with
        | hlist ?list_types => ltac_map ltac:(reify_type tmap') list_types
        end in
      let lhs := lazymatch goal with |- ?lhs = _ => lhs end in
      let rhs := lazymatch goal with |- _ = ?rhs => rhs end in
      unify new_cm (let tmName := tmap' in ltac:(
        let lifted_oldconstmap := beta1 oldconstmapFun tmName in
        let cmap' := extend_constmap tmName varmap lifted_oldconstmap g in
        let reified_lhs := reify_expr tmap' cmap' types_of_varmap varmap lhs in
        let reified_rhs := reify_expr tmap' cmap' types_of_varmap varmap rhs in
        unify new_thm (mk_reified_q_equ types_of_varmap reified_lhs reified_rhs);
        exact (let cmName := cmap' in tt)));
      eapply H
    ) : t -> t)
  end in
  let __ := match constr:(O) with _ => constmap_ref_put new_cm end in
  new_thm.

Ltac reify_qf_equ t :=
  lazymatch reify_q_equ t with
  | @mk_reified_q_equ nil ?t ?l ?r => constr:(@mk_reified_qf_equ t l r)
  end.

(* give tactics-in-terms notations access to goal *)
Definition conjecture(P: Prop) := True.

(* hack to get goal reified *)
Ltac pose_goal_as_hyp :=
  let name := fresh "get_goal_reified_hack" in
  lazymatch goal with
  | |- ?g => assert (g = g) as name by reflexivity
  end.

(* Identify function to annotate hypotheses and the goal with their reification.
   R will be reified_q_equ or reified_qf_equ or term *)
Definition reified(P: Prop){R: Type}{r: R} := P.

Ltac reify_hyp H :=
  let t := type of H in
  lazymatch t with
  | ?A -> ?B => fail "implications not yet supported"
  | forall _, _ =>
      let r := reify_q_equ t in
      change (@reified t reified_q_equ r) in H
(*| conjecture ?P => maybe *)
  | _ = _ =>
      let r := reify_qf_equ t in
      change (@reified t reified_qf_equ r) in H
  | _ => fail "not supported"
  end.

Ltac reify_unreified_hyp :=
  match goal with
  | H: ?T |- _ =>
      lazymatch T with
      | reified _ => fail
      | _ => lazymatch type of T with
             | Prop => reify_hyp H
             end
      end
  end.

Ltac reify_hyps := repeat reify_unreified_hyp.

Lemma P_eq_True_to_P: forall (P: Prop), P = True -> P. Proof. intros. subst. exact I. Qed.

Ltac reify_goal :=
  lazymatch goal with
  | |- _ = _ => idtac
  | |- ?g => refine (P_eq_True_to_P g _)
  end;
  lazymatch goal with
  | |- ?g => let r := reify_qf_equ g in change (@reified g reified_qf_equ r)
  end.

Ltac reify_all :=
  pose_goal_as_hyp;
  constmap_ref_init;
  reify_hyps;
  reify_goal.

Definition apply_command (e : egraph) (c : command) : egraph :=
  match c with
  | mk_command CSaturateL2R (mk_reified_q_equ tvm lhsP rhsP) => saturate_LtoR tvm lhsP rhsP e
  | mk_command CAddEqu (mk_reified_qf_equ lhs rhs) => add_equ lhs rhs e
  | mk_command CAddTerm (existT _ tp t) => fst (@add_term [] HNil e tp t)
  end.

Definition apply_commands : list command -> egraph -> egraph :=
  fold_left apply_command.

(* Note: DON'T do this:

Record command_with_evidence := mk_command_with_evidence {
  get_command : command;
  actual_lemma_type : Type;
  get_evidence : actual_lemma_type;
}.

because feeding a `list command_with_evidence` to the saturation procedure is a bad idea,
because the arguments of the saturation procedure will be vm_computed.
Instead, we use two lists of equal length: One for the data to be fed to the saturation
procedure (and thus to vm_compute), and one for the data to be fed to conversion
(ie the checks that reification was done correctly).
*)

Section WithConstmap.
  Context {typemap : list Type}.
  Context (constmap: list (dyn typemap)).

  (* TODO maybe wf_term should only take the deep types of the constmap but not
     the values so that we can vm_compute it *)

  Inductive justified_command: Type :=
  | mk_justified_SaturateL2R (tvm: list type) {t: type} (lhsP rhsP : term t)
      (wf_lhsP : wf_term typemap constmap tvm lhsP = true)
      (wf_rhsP : wf_term typemap constmap tvm rhsP = true)
      (pf: generate_theorem tvm lhsP rhsP wf_lhsP wf_rhsP)
  | mk_justified_AddEqu {t: type} (lhsP rhsP : term t)
      (wf_lhsP : wf_term typemap constmap [] lhsP = true)
      (wf_rhsP : wf_term typemap constmap [] rhsP = true)
      (pf: generate_theorem [] lhsP rhsP wf_lhsP wf_rhsP)
  | mk_justified_AddTerm {tp : type} (t : term tp)
      (wf : wf_term typemap constmap [] t = true).

  Definition erase_justification (jc : justified_command) : command :=
    match jc with
    | mk_justified_SaturateL2R tvm lhsP rhsP wf_lhsP wf_rhsP pf =>
        mk_command CSaturateL2R (mk_reified_q_equ tvm lhsP rhsP)
    | mk_justified_AddEqu lhsP rhsP wf_lhsP wf_rhsP pf =>
        mk_command CAddEqu (mk_reified_qf_equ lhsP rhsP)
    | @mk_justified_AddTerm tp t wf =>
        mk_command CAddTerm (existT term tp t)
    end.

  Unset Printing Records.

  Lemma apply_commands_correct: forall (cs : list command) (jcs : list justified_command)
        (e : egraph)
        (EVM : cs = map erase_justification jcs)
        (e_pf : invariant_egraph typemap constmap e),
    invariant_egraph typemap constmap (apply_commands cs e).
  Proof.
    induction cs; intros. 1: exact e_pf.
    destruct jcs as [|evh evt]. 1: discriminate EVM.
    simpl in EVM.
    injection EVM. clear EVM. intros ET EH. subst.
    eapply IHcs. 1: reflexivity.
    destruct evh; simpl in *.
    - (* CSaturateL2R *)
      eapply saturate_L2R_correct. 1: exact e_pf. exact pf.
    - (* CAddEqu *)
      eapply merge_preserve in e_pf. 2: exact pf.
      unfold merge_terms, add_equ in *.
      destruct add_term. destruct add_term. exact e_pf.
    - (* CAddTerm *)
      eapply add_term_safe with (f := t) in e_pf.
      destruct add_term. simpl.
      eapply e_pf.
  Qed.

End WithConstmap.

Ltac ltac_erase_justification jc :=
  lazymatch jc with
  | mk_justified_SaturateL2R _ ?tvm ?lhsP ?rhsP _ _ _  =>
      constr:(mk_command CSaturateL2R (mk_reified_q_equ tvm lhsP rhsP))
  | mk_justified_AddEqu _ ?lhs ?rhs _ _ _ =>
      constr:(mk_command CAddEqu (mk_reified_qf_equ lhs rhs))
  | @mk_justified_AddTerm ?tp ?t ?wf =>
      constr:(mk_command CAddTerm (existT term tp t))
  end.

Ltac hyp_to_justified_command cm H :=
  lazymatch type of H with
  | @reified ?P ?R ?reif =>
      (* Currently, we can infer to command from the type of reif, but later,
         the argument passed to this ltac will also have to specify the command *)
      lazymatch reif with
      | mk_reified_q_equ ?tvm ?lhsP ?rhsP =>
          constr:(mk_justified_SaturateL2R cm tvm lhsP rhsP eq_refl eq_refl H)
      | mk_reified_qf_equ ?lhs ?rhs =>
          constr:(mk_justified_AddEqu cm lhs rhs eq_refl eq_refl H)
      end
  end.

Ltac ident2jc H :=
  lazymatch goal with
  | cm := _ : list (dyn _) |- _ =>
    let r := hyp_to_justified_command cm H in exact r
  end.

(* doesn't work because no access to goal
Ltac goalLHS2jc :=
  lazymatch goal with
  | cm := _ : EGraphList.list (dyn ?tm) |- @reified ?P ?R (mk_reified_qf_equ ?lhs ?rhs) =>
    exact (@mk_justified_AddTerm tm cm _ lhs eq_refl)
  end.

Ltac goalRHS2jc :=
  lazymatch goal with
  | cm := _ : EGraphList.list (dyn ?tm) |- @reified ?P ?R (mk_reified_qf_equ ?lhs ?rhs) =>
    exact (@mk_justified_AddTerm tm cm _ rhs eq_refl)
  end.
*)

Ltac erase_justifications := ltac_map ltac:(ltac_erase_justification).

(* expects a goal of the form
   reified _ -> reified _ -> ... -> _
   and intros all the reified's and returns a list of these reified's
   converted to justified commands *)
Ltac intros_reified cm acc :=
  lazymatch goal with
  | |- forall (name: @reified ?P ?R ?r), _ =>
      let __ := match constr:(O) with _ => intro name end in
      let jc := hyp_to_justified_command cm name in
      intros_reified cm (EGraphList.cons jc acc)
  | |- _ => constr:(acc)
  end.

Ltac collect_qf_equs :=
  let r := lazymatch goal with
  | cm := _ : EGraphList.list (dyn _) |- _ =>
      let __ := match constr:(O) with _ =>
        repeat match goal with
               | H: @reified _ reified_qf_equ _ |- _ => revert H
               end
      end in
      intros_reified cm (@EGraphList.nil (justified_command cm))
  end in toplevel_betas r.

Ltac collect_q_equs :=
  let r := lazymatch goal with
  | cm := _ : EGraphList.list (dyn _) |- _ =>
      let __ := match constr:(O) with _ =>
        repeat match goal with
               | H: @reified _ reified_q_equ _ |- _ => revert H
               end
      end in
      intros_reified cm (@EGraphList.nil (justified_command cm))
  end in toplevel_betas r.

Ltac ltac_app xs ys :=
  lazymatch xs with
  | ?h :: ?t => refine (cons h _); ltac_app t ys
  | nil => exact ys
  end.

(* TODO use Seq command combinator instead of (@cons command), which will allow us
   to get rid of ltac_app computations *)

Declare Custom Entry sponge_command.
Declare Scope sponge_scope.
Local Open Scope sponge_scope.

Notation "{{ x }}" := x (x custom sponge_command at level 10) : sponge_scope.
Notation "H" := (cons (ltac:(ident2jc H)) (@nil (justified_command _)))
  (in custom sponge_command at level 0, H ident, only parsing).
(* don't work because tactics in terms don't have access to goal
Notation "'goalLHS'" := (cons (ltac:(goalLHS2jc)) (@nil (justified_command _)))
  (in custom sponge_command at level 0, only parsing).
Notation "'goalRHS'" := (cons (ltac:(goalRHS2jc)) (@nil (justified_command _)))
  (in custom sponge_command at level 0, only parsing).
*)
(*
Notation "'allQfEqs'" := (ltac:(let r := collect_qf_equs in exact r))
  (in custom sponge_command at level 0, only parsing).
Notation "'allForallEqs'" := (ltac:(let r := collect_q_equs in exact r))
  (in custom sponge_command at level 0, only parsing).
*)
Notation "xs ; ys" := (ltac:(ltac_app xs ys))
  (in custom sponge_command at level 7, left associativity, only parsing).

Ltac unpack_tm_cm :=
  lazymatch goal with
  | cm: @constmap_ref (let tmName := ?tm in let cmName := @?constmapFun tmName in tt)
    |- _ => pose tm as tmName;
            let cm' := beta1 constmapFun tmName in
            pose cm' as cmName;
            clear cm
  end.

Ltac saturate_with pfs :=
  let cmds := erase_justifications pfs in
  lazymatch goal with
  | Inv : invariant_egraph ?tm ?cm ?e |- _ =>
      eapply (@apply_commands_correct tm cm cmds pfs e
                eq_refl(*<- needs to be conversion, not vm_compute *)) in Inv
  end.

Ltac prove_eq_by_sponge :=
  let FL := fresh "FL" in let FR := fresh "FR" in
  lazymatch goal with
  | SpongeInv : invariant_egraph ?tm ?cm ?e
    |- @reified ?P _ (@mk_reified_qf_equ ?tR ?lhsR ?rhsR) =>
      change P;
      eassert (@lookup_term (@EGraphList.nil type) HNil _ lhsR e = Some _) as FL
        by (vm_compute; reflexivity);
      lazymatch type of FL with
      | _ = Some ?commonId =>
          eassert (@lookup_term (@EGraphList.nil type) HNil _ rhsR e = Some _) as FR
            by (vm_compute; reflexivity);
          exact (correct SpongeInv tR lhsR rhsR commonId eq_refl eq_refl FL FR)
      end
  end.

Lemma modest_test1: forall (word : Type)
  (wadd : word -> word -> word)
  (wadd_comm : forall a b : word, wadd a b = wadd b a)
  (f : word -> word) (a b : word),
  f (wadd b a) = f (wadd a b).
Proof.
  intros.
  reify_all.
  unpack_tm_cm.
  pose empty_egraph as sponge.
  assert (invariant_egraph tm cm sponge) as SpongeInv by apply empty_invariant.
  saturate_with {{ get_goal_reified_hack ; wadd_comm }}.
  prove_eq_by_sponge.
Time Qed. (* 0.055 secs *)

End Temp.

Local Open Scope sponge_scope.

Require Coq.Lists.List. Import List.ListNotations.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.PropExtensionality.

Ltac propintu := intros; apply propositional_extensionality; intuition idtac.
Module PropLemmas.
  Lemma eq_True: forall (P: Prop), P -> P = True. Proof. propintu. Qed.
  Lemma and_True_l: forall (P: Prop), (True /\ P) = P. Proof. propintu. Qed.
  Lemma and_True_r: forall (P: Prop), (P /\ True) = P. Proof. propintu. Qed.
  Lemma eq_eq_True: forall (A: Type) (a: A), (a = a) = True. Proof. propintu. Qed.
End PropLemmas.


Section WithLib.
  Context (word: Type)
          (ZToWord: Z -> word)
          (unsigned: word -> Z)
          (wsub: word -> word -> word)
          (wadd: word -> word -> word)
          (wopp: word -> word).

  Context (wadd_0_l: forall a, wadd (ZToWord 0) a = a)
          (wadd_0_r: forall a, wadd a (ZToWord 0) = a)
          (wadd_comm: forall a b, wadd a b = wadd b a)
          (wadd_assoc: forall a b c, wadd a (wadd b c) = wadd (wadd a b) c)
          (wadd_opp: forall a, wadd a (wopp a) = ZToWord 0).

  (* Preprocessing: *)
  Context (wsub_def: forall a b, wsub a b = wadd a (wopp b)).

  (* With sideconditions: *)
  Context (unsigned_of_Z: forall a, 0 <= a < 2 ^ 32 -> unsigned (ZToWord a) = a).

  Context (mem: Type)
          (word_array: word -> list word -> mem -> Prop)
          (sep: (mem -> Prop) -> (mem -> Prop) -> (mem -> Prop)).

  Context (sep_comm: forall P Q: mem -> Prop, sep P Q = sep Q P).

  Ltac pose_list_lemmas :=
    pose proof (@List.firstn_cons word) as firstn_cons;
    pose proof (@List.skipn_cons word) as skipn_cons;
    pose proof (@List.app_comm_cons word) as app_cons;
    pose proof (@List.firstn_O word) as firstn_O;
    pose proof (@List.skipn_O word) as skipn_O;
    pose proof (@List.app_nil_l word) as app_nil_l;
    pose proof (@List.app_nil_r word) as app_nil_r.

  Ltac pose_prop_lemmas :=
    pose proof PropLemmas.and_True_l as and_True_l;
    pose proof PropLemmas.and_True_r as and_True_r;
    pose proof PropLemmas.eq_eq_True as eq_eq_True.

  Definition lipstick {A:Type} {a:A} := a.

  Lemma simplification1: forall (a: word) (w1_0 w2_0 w1 w2: word) (vs: list word)
                               (R: mem -> Prop) (m: mem) (cond0_0 cond0: bool)
        (f g: word -> word) (b: word)
        (HL: List.length vs = 3%nat)
        (H : sep (word_array a
          (List.firstn
             (Z.to_nat (unsigned (wsub (wadd a (ZToWord 8)) a) / 4))
             ((if cond0_0 then [w1_0] else if cond0 then [w2_0] else List.firstn 1 vs) ++
              [w1] ++ List.skipn 2 vs) ++
           [w2] ++
           List.skipn
             (S (Z.to_nat (unsigned (wsub (wadd a (ZToWord 8)) a) / 4)))
             ((if cond0_0 then [w1_0] else if cond0 then [w2_0] else List.firstn 1 vs) ++
                [w1] ++ List.skipn 2 vs))) R m),
        f (wadd b a) = g b /\
        sep R (word_array a [List.nth 0 vs (ZToWord 0); w1; w2]) m /\
        f (wadd b a) = f (wadd a b).
  Proof.
    intros.

    pose_list_lemmas.
    pose_prop_lemmas.
    specialize (eq_eq_True word).

    (* Make problems simpler by only considering one combination of the booleans,
       but it would be nice to treat all of them at once *)
    replace cond0_0 with false in * by admit.
    replace cond0 with false in * by admit.

    (* Make problem simpler by not requiring side conditions: since we know the
       concrete length of vs, we can destruct it, so firstn and skipn lemmas can
       be on cons without sideconditions rather than on app with side conditions
       on length *)
    destruct vs as [|v0 vs]. 1: discriminate HL.
    destruct vs as [|v1 vs]. 1: discriminate HL.
    destruct vs as [|v2 vs]. 1: discriminate HL.
    destruct vs as [|v3 vs]. 2: discriminate HL.
    clear HL.
    cbn.
    (* cbn in H. <-- We don't do this cbn because now that we've done the above
       destructs, cbn can do much more than it usually would be able to do. *)

    (* Preprocessing *)
    rewrite wsub_def in *.
    clear wsub_def.
    apply PropLemmas.eq_True in H.

    (* Rewrites with sideconditions, currently also part of separate preprocessing: *)
    pose proof (unsigned_of_Z 8 ltac:(lia)) as A1.

    (* Constant propagation rules, manually chosen to make things work,
       TODO how to automate? *)
    pose proof (eq_refl : (Z.to_nat (8 / 4)) = 2%nat) as C1.

    pose
      ( (f (wadd b a) = g b /\
         sep R (word_array a [v0; w1; w2]) m /\
         f (wadd b a) = f (wadd a b))
      = (f (wadd a b) = g b) ) as test1.

    assert test1 as test1pf. {
      subst test1.
      rewrite (wadd_comm a (ZToWord 8)) in H.
      rewrite <- (wadd_assoc (ZToWord 8) a (wopp a)) in H.
      rewrite (wadd_opp a) in H.
      rewrite (wadd_0_r (ZToWord 8)) in H.
      rewrite A1 in H.
      rewrite C1 in H.
      repeat (rewrite ?firstn_cons, ?skipn_cons, <-?app_cons, ?firstn_O, ?skipn_O,
               ?app_nil_l, ?app_nil_r in H).
      rewrite sep_comm in H.
      rewrite H.
      rewrite and_True_l.
      rewrite (wadd_comm b a).
      rewrite eq_eq_True.
      rewrite and_True_r.
      reflexivity.
    }
    clear test1pf.

    assert test1 as test1pf. {
      subst test1.

      reify_all.
      unpack_tm_cm.
      pose empty_egraph as sponge.
      assert (invariant_egraph tm cm sponge) as SpongeInv by apply empty_invariant.
      saturate_with {{ get_goal_reified_hack;wadd_comm}}.
               (* C1; A1; H;
        eq_eq_True; and_True_r; and_True_l; app_nil_r; app_nil_l; skipn_O; firstn_O;
   app_cons; skipn_cons; firstn_cons ; sep_comm; wadd_opp; wadd_assoc; wadd_0_r; wadd_0_l }}. *)

  lazymatch goal with
  | SpongeInv : invariant_egraph ?tm ?cm ?e |- _ =>
      let l := eval vm_compute in (log e) in idtac l
  end.

  lazymatch goal with
  | SpongeInv : invariant_egraph ?tm ?cm ?e
    |- @reified ?P _ (@mk_reified_qf_equ ?tR ?lhs ?rhs) =>
      change P;
      eassert (@lookup_term (@EGraphList.nil type) HNil _ lhs e = Some _) as FL
        by (vm_compute; reflexivity) (*;
      lazymatch type of FL with
      | _ = Some ?commonId =>
          eassert (@lookup_term (@EGraphList.nil type) HNil _ rhsR e = Some _) as FR
            by (vm_compute; reflexivity);
          exact (correct SpongeInv tR lhsR rhsR commonId eq_refl eq_refl FL FR)
      end *)
  end.
(* BUG: reflexivity fails, which means that saturation removed terms! *)


  (* new debug session starts here *)

    reify_all.

    lazymatch goal with
    | cm: @constmap_ref (let tmName := ?tm in let cmName := @?constmapFun tmName in tt)
      |- _ => pose tm as tmName;
              let cm' := beta1 constmapFun tmName in
              pose cm' as cmName;
              clear cm
    end.
    pose empty_egraph as sponge.
    assert (invariant_egraph tm cm sponge) as SpongeInv by apply empty_invariant.

(*
    let pfs := constr:({{ H0; C1; A1; H;
    eq_eq_True; and_True_r; and_True_l; app_nil_r; app_nil_l; skipn_O; firstn_O; app_cons; skipn_cons; firstn_cons; sep_comm; wadd_opp; wadd_assoc; wadd_comm; wadd_0_r; wadd_0_l }}) in
    let cmds := erase_justifications pfs in
    lazymatch goal with
    | Inv : invariant_egraph ?tm ?cm ?e |- _ =>
        eapply (@apply_commands_correct tm cm cmds pfs e
                  eq_refl(*<- needs to be conversion, not vm_compute *)) in Inv
    end.
*)

    let pfs := constr:({{ H0 ; wadd_comm }}) in
    let cmds := erase_justifications pfs in
    lazymatch goal with
    | Inv : invariant_egraph ?tm ?cm ?e |- _ =>
        eapply (@apply_commands_correct tm cm cmds pfs e
                  eq_refl(*<- needs to be conversion, not vm_compute *)) in Inv
    end.

    lazymatch goal with
    | Inv : invariant_egraph ?tm ?cm ?eVal |- _ =>
        set (e := eVal) in Inv
    end.
    let cm := eval unfold cm in cm in
    let r_lhs := reify_expr tm cm (@EGraphList.nil type) HNil (f (wadd b a)) in
    pose (@lookup_term (@EGraphList.nil type) HNil _ r_lhs e).
    let cm := eval unfold cm in cm in
    let r_lhs := reify_expr tm cm (@EGraphList.nil type) HNil (f (wadd a b)) in
    pose (@lookup_term (@EGraphList.nil type) HNil _ r_lhs e).
    vm_compute in o,o0.

(* Bug numero 1: la liste va trop long, off by one error, which side is the error on? *)

(* This is the list of results of matching wadd_comm, which should not be empty! *)
vm_compute in l.

    (* to see what's hidden:
    Arguments reified : clear implicits.
    Arguments constmap_ref : clear implicits.
    Set Printing Implicit. Unset Printing Records.
    { *)

    Set Ltac Backtrace.
  Abort.
End WithLib.

(* OLD CODE:

Require Import Lia.
Definition travel_value :
forall (typemap : list Type) (t : type )
 typemap_extension,
 (max_t t) <? (length typemap) = true ->
 Prod ( t_denote (typemap ++ typemap_extension) t -> t_denote typemap t)
 (  t_denote typemap t -> t_denote (typemap ++ typemap_extension) t)
 .
 induction t.
 -
  simpl.
  intros;
  split.
  eapply Nat.ltb_lt in H.
  intros.
  pose proof app_nth1.
  specialize (H0) with (1:= H).
  specialize (H0 typemap_extension unit).
  rewrite H0 in X.
  eapply X.
  intros.
  eapply Nat.ltb_lt in H.

  pose proof app_nth1.
  specialize (H0) with (1:= H).
  specialize (H0 typemap_extension unit).
  rewrite H0.
  eapply X.
 -
  simpl.
  intros.
  eapply Nat.ltb_lt in H.
  assert (max_t t2 <? length typemap = true).
  eapply Nat.ltb_lt .
  lia.
  assert (max_t t1 <? length typemap = true).
  eapply Nat.ltb_lt .
  lia.
  pose proof (IHt2 typemap_extension H0).
  pose proof (IHt1 typemap_extension H1).
  inversion X.
  inversion X0.
  split.
  intros.
  eapply x.
  eapply X1.
  eapply y0.
  eapply X2.
  intros.
  eapply y.
  eapply X1.
  eapply x0.
  eapply X2 .
Defined.

Definition upcast_value :
forall (typemap : list Type) (t : type)
 typemap_extension,
 (max_t t) <? (length typemap) = true ->
 (t_denote (typemap := typemap )t -> t_denote (typemap := typemap ++ typemap_extension) t).
  intros.
  pose travel_value.
  specialize (p typemap t typemap_extension H).
  inversion p. eapply y. eapply X.
  Defined.

Definition upcast_constmap typemap typemap_extension (constmap : list (dyn typemap)) : list (dyn (typemap ++ typemap_extension)).
  induction varmap.
  -
    exact nil.
  -
    dependent destruction a.
    pose ((max_t T0 <? (length typemap))) .
    pose(travel_value typemap T0 typemap_extension).
    destruct b eqn:?.
    2:{ exact IHvarmap. }
    exact ({| T := _; state := (sndP (p Heqb0)) state0 |}::IHvarmap).
  Defined.

Ltac ltac_diff lbig lsmall :=
  (* let __ := match O with | _ => idtac "diffcompute" lbig lsmall end in *)
  match lbig with
  | ?t :: ?q =>
  match lsmall with
  | t :: ?r =>
  (* let __ := match O with | _ => idtac "find" t q r end in *)
        ltac_diff q r
  | nil => constr:(lbig)
  | _ => fail
  end
  | nil =>
  match lsmall with
  | nil => constr:(lsmall)
  | _ => fail
  end
  end.

Ltac listFromProp' tmap acc input_prop :=
  match input_prop with
  | id_mark ?n ?x =>
    acc
  | ?a ?b  =>
    lazymatch type of b with
    | Prop =>
    let acc := listFromProp' tmap acc a in
    let acc := listFromProp' tmap acc b in
    acc
        | Type => fail
        | _ =>
    let acc := listFromProp' tmap acc a in
    let acc := listFromProp' tmap acc b in
    acc
    end
  | ?a =>
    let t := type of a in
    let deeply_represented := funToTArrow tmap t in
    let newa :=  eval cbv  [ Pos.add Pos.of_nat Pos.sub app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_value upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in (upcast_value tmap deeply_represented nil eq_refl a) in
    addList {| T := deeply_represented ; state := newa : (t_denote (typemap:= tmap) deeply_represented)|} acc
  end.

(*
Ltac reify_hyp H oldtypemap oldvarmap x :=
  idtac "start reify hyp";
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  evar (x : Type);
  let newassert := fresh "newassert" in
  let quan := get_quantifiers H in
  let quan := type_term quan in
  idtac quan;
  let t := type of H in assert t as newassert;
  reify_forall 0;
   [
  match goal with
  | [ |- ?a = ?b] =>
  idtac "start listTypes";
  let typemap := listTypesFromProp oldtm1 (a,b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  pose typemap;
  idtac typemap;
  let deepify_quant := ltac_map funToTArrow typemap quan in
  let deepify_quant := type_term deepify_quant in
  let oldvm := eval unfold oldvm in oldvm in
  idtac "deepquant" deepify_quant oldtm1 diff oldvm;
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv  [Pos.of_nat Pos.sub Pos.add app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (a, b) in
  idtac "newvarmap" varmap;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  pose varmap;
  idtac "varmap" varmap;
  let reifedA := reify_prop' deepify_quant typemap varmap a in
  pose reifedA as A;
  let reifedB := reify_prop' deepify_quant typemap varmap b in
  pose reifedB as B;
  idtac "reifed" reifedA reifedB;
  let A':= eval unfold A in A in
  let B':= eval unfold B in B in
  let c := type of A in
  match c with
  | Pattern ?rett =>
  let T := fresh "newlemma" in
  let rett := eval simpl in rett in
    pose (generate_theorem (ctx:= varmap) (typemap := typemap) rett deepify_quant nil DNil
                                A' B') as T;
  let x' := eval unfold x in x in
  unify x' T ;
  eapply H
  end
  end
 |]; clear newassert
 ;
 subst oldtm;
 subst oldvm
 . *)
Ltac eta_collapse t :=
  match t with
  | context f[fun x => ?m x] =>
    context f[m]
  end.

Axiom (MYA : Type).
Axiom (pmya : MYA -> nat).
Goal ((forall x y ,  x + pmya y = pmya y + x)  -> (forall x y, x * y = y * x) -> True ).
  intros.
  pose (nil : list Type).
  pose (nil : list (SModule (typemap := l))).
  (* reify_hyp H l l0 myth. *)
  (* assert (myth ). *)
  (* exact H. *)
    admit.
  (* reify_hyp H0 l l0 y. *)
  (* Currently works but reverses the order in which it writes the quantifiers. *)
  (* clear y. *)
    Abort.

  Definition deeplist2_from_deeplisteclass (quant : list type)
    (instantiate_quant : DeepListEclass quant) (e : egraph) : option (DeepList2 quant).
  induction quant.
  {
    exact (Some DNil2).
  }
  {
    inversion instantiate_quant.
    specialize (IHquant cdr).
    unshelve refine (let potential :=
              match v with
              | Some id => (propose_formula (t:=t) ctx e FUEL id )
              | None => head (dropNone
                  (map
                     (fun id => propose_formula (t:=t) ctx e FUEL (Pos.of_nat id))
                     (seq 0 (Pos.to_nat (max_allocated e)))))
              end in _).
    destruct IHquant.
    2:{ exact None. }
    destruct potential.
    econstructor.
    econstructor.
    rewrite H0 in f.
    exact f.
    exact d.
    exact None.
  }
  Defined.

  Definition deeplist_from_deeplist2 (quant : list (type ))
    (instantiate_quant : DeepList2 quant)  : (DeepList (typemap := typemap) quant).
  induction quant.
  {
    econstructor.
  }
  {
    inversion instantiate_quant.
    econstructor.
    eapply interp_formula; eauto.
    eauto.
  }
  Defined.


  Definition nth_deep' {quantifiermap' } n t (pf : nth_error quantifiermap' n = Some t) (l : DeepList2 quantifiermap')
   : Formula (ctx:=ctx) t.
  generalize dependent quantifiermap'.
  induction n.
  -
    intros.
    destruct quantifiermap'.
    inversion pf.
    simpl in *.
    inversion pf.
    subst.
    inversion l.
    exact v.
    (* exact (interp_formula ctx v). *)
  -
    intros.
    destruct quantifiermap'.
    inversion pf.
    cbn in  pf.
    eapply IHn.
    exact pf.
    inversion l. exact cdr.
  Defined.


End Potentials.

Require Import Coq.Program.Equality.

Lemma nth_deep2nth_deep' : forall  {typemap : list Type} quanttype ctx n t0 e0(X : DeepList2 quanttype) ,
      nth_deep n t0 e0 (deeplist_from_deeplist2 (ctx:=ctx) quanttype X )
       =
      interp_formula ctx (nth_deep' (typemap:=typemap) n t0 e0 X).
  induction quanttype.
  {
    simpl.
    intros.
    destruct n; inversion e0.
  }
  {
    induction n.
      intros.
    inversion e0.
    destruct H0.
    subst.
    destruct X eqn:?.
    2:{
      inversion e0.
    }
    simpl in e0.
    inversion X.
    inversion e0.
    subst.
    (* Here I could use my decidable equality to do that instead of Program Equality *)
    {
      dependent destruction e0.
      reflexivity.
    }
    intros.
    simpl in e0.
    (* Here it seems I would also need to lift a decidable equality... *)
    dependent destruction X.
    simpl (nth_deep' _ _ _ _).
    simpl (deeplist_from_deeplist2 _ _).
    unfold eq_rect_r, eq_rect.
    cbv [eq_sym].
    erewrite <- IHquanttype.
    reflexivity.
  }
  Defined.

  Fixpoint deep2_eqb {typemap : list Type} quanttype ctx (X Y: DeepList2 (typemap:=typemap) (ctx:= ctx) quanttype) : bool.
  dependent destruction X; dependent destruction Y.
  {
    pose (eqf v0 v).
    pose (deep2_eqb _ _ _ X Y).
    exact (b && b0).
  }
  { exact true. }
  Defined.

  Definition andb_true_iff  :=
(fun b1 b2 : bool =>
if b2 as b return (b1 && b = true <-> b1 = true /\ b = true)
then
 if b1 as b return (b && true = true <-> b = true /\ true = true)
 then
  conj (fun _ : true = true => conj eq_refl eq_refl)
    (fun H : true = true /\ true = true =>
     and_ind (fun _ _ : true = true => eq_refl) H)
 else
  conj (fun H : false = true => conj H eq_refl)
    (fun H : false = true /\ true = true =>
     and_ind (fun (H0 : false = true) (_ : true = true) => H0) H)
else
 if b1 as b return (b && false = true <-> b = true /\ false = true)
 then
  conj (fun H : false = true => conj eq_refl H)
    (fun H : true = true /\ false = true =>
     and_ind (fun (_ : true = true) (H1 : false = true) => H1) H)
 else
  conj (fun H : false = true => conj H H)
    (fun H : false = true /\ false = true =>
     and_ind (fun _ H1 : false = true => H1) H))
     : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true.

  Lemma deep2_eqb_deeplist_from {typemap : list Type} quanttype ctx (X Y: DeepList2 (typemap:=typemap) (ctx:= ctx) quanttype) :
  deep2_eqb quanttype ctx X Y = true -> deeplist_from_deeplist2 quanttype X =  deeplist_from_deeplist2 quanttype Y.
    induction X.
    {
      dependent destruction Y.
      cbn [deep2_eqb].
      unfold solution_left, eq_rect_r, eq_rect, eq_sym, f_equal.
      intros.
      eapply andb_true_iff in H.
      destruct H.
      simpl.
      unfold solution_left, eq_rect_r, eq_rect, eq_sym, f_equal.
      pose @eq_correct .
      specialize (e) with (1:= H).
      rewrite e.
      f_equal.
      eapply IHX.
      eauto.
    }
    eauto.
  Defined.


Lemma elim_quant_interp_pattern :
forall {typemap t_quantifiermap ctx t0 rett}
(ql : DeepList t_quantifiermap)
(v : Formula (typemap := typemap) (ctx:=ctx) t0)
(p : Pattern rett),
interp_pattern
  (DCons t0 (interp_formula ctx v) ql) p =
  interp_pattern ql (app_pattern v p).
  induction p .
  {
    simpl.
    erewrite IHp2.
    erewrite IHp1.
    reflexivity.
  }
  2:{
    simpl.
    reflexivity.
  }
  {
    destruct n.
    {

      simpl (app_pattern _ _).
      simpl in e.
      inversion e.
      dependent destruction e.
      unfold eq_rect_r, eq_rect, eq_sym, f_equal.
      unfold interp_pattern at 1.
      unfold Pattern_rect.
      simpl nth_deep.
      unfold eq_rect_r, eq_rect, eq_sym, f_equal.
      induction v.
      {
        simpl.
        erewrite IHv2; eauto.
        erewrite IHv1; eauto.
      }
      {
        eauto.
      }
    }
    {
      simpl in *.
      reflexivity.
    }
  }
  Qed.


Lemma elim_quant_generate_theorem :
forall {typemap quant_to_do t_quantifiermap}
(ql : DeepList t_quantifiermap)
{ctx t0 rett}
(v : Formula (typemap := typemap) (ctx:=ctx) t0)
(p pnew: Pattern rett),
  generate_theorem
    rett quant_to_do (t0 :: t_quantifiermap)
    (DCons t0 (interp_formula ctx v) ql) p pnew =
  generate_theorem
    rett quant_to_do t_quantifiermap
    ql (app_pattern v p) (app_pattern v pnew).

    intros typemap quant_to_do t_quantifiermap.
    change ((fix app (l m : list (type )) {struct l} :
           list (type ) :=
         match l with
         | nil => m
         | a :: l1 => a :: app l1 m
         end) t_quantifiermap quant_to_do) with ( t_quantifiermap ++ quant_to_do).
         revert t_quantifiermap.
    induction quant_to_do.
    2:{
      intros.
      specialize (IHquant_to_do (t_quantifiermap ++ (cons a nil))).
      specialize IHquant_to_do with (ctx:=ctx) (t0 := t0) (rett:= rett).
      specialize (IHquant_to_do) with (v:= v).
      simpl.
      Require Import Coq.Logic.FunctionalExtensionality.
      pose @forall_extensionality.
      set (eq_rect _ _ _ _ _) as p_transported.
      set (eq_rect _ _ _ _ _) as pnew_transported.
      set (eq_rect _ _ _ _ _) as app_p_transported.
      set (eq_rect _ _ _ _ _) as app_pnew_transported.
      assert ( forall (x : t_denote a),
                (fun x => generate_theorem rett quant_to_do (t0 :: t_quantifiermap ++ (cons a nil)) (DCons t0 (interp_formula ctx v) (add_end ql x)) p_transported
                  pnew_transported ) x=
                (fun x => generate_theorem rett quant_to_do (t_quantifiermap ++ (cons a nil)) (add_end ql x) (app_p_transported) (app_pnew_transported)) x).
      intros.
      erewrite IHquant_to_do.
      f_equal.
      {
        intros.
        rewrite H5.
        rewrite H6.
        reflexivity.
      }
      {
        subst app_p_transported.
        subst p_transported.
        unfold app_assoc'.
        unfold eq_rect, eq_trans, f_equal.
        remember (list_ind _ _ _ _ ).
        clear.
        revert v.
        revert p.
        revert rett.
        revert t0.
        simpl in y.
        generalize y.
        clear y.
        pose app_assoc'.
        specialize (e _ t_quantifiermap (cons a nil) quant_to_do).
        simpl in e.
        rewrite <- e.
        intros.
        dependent destruction y.
        reflexivity.
      }
      {
        subst app_pnew_transported.
        subst pnew_transported.
        unfold app_assoc'.
        unfold eq_rect, eq_trans, f_equal.
        remember (list_ind _ _ _ _ ).
        clear.
        revert v.
        revert pnew.
        revert rett.
        revert t0.
        simpl in y.
        generalize y.
        clear y.
        pose app_assoc'.

        specialize (e _ t_quantifiermap (cons a nil) quant_to_do).
        simpl in e.
        rewrite <- e.
        intros.
        dependent destruction y.
        reflexivity.
      }
      specialize (e _ _  _ H).
      apply e.
    }
    {
      intros.
      cbn [generate_theorem].
      erewrite <- elim_quant_interp_pattern.
      erewrite <- elim_quant_interp_pattern.
      eapply eqPropType.
      Require Import Coq.Logic.PropExtensionality.
      pose propositional_extensionality.
      match goal with
      | [ |- ?a = ?b] => set a; set b end.
      specialize (e P P0).
      (* Upcaster from P = P0 in Prop, to P = P0 in type*)
      eapply e.
      subst P P0.
      clear e.
      split.
      {
        intros.
        (* This was surprisingly tricky the first time *)
        assert (interp_pattern (DCons t0 (interp_formula ctx v) (eq_rect_r DeepList ql (app_nil_r' type t_quantifiermap))) p
                =
                interp_pattern (eq_rect_r DeepList (DCons t0 (interp_formula ctx v) ql) (app_nil_r' type (t0 :: t_quantifiermap))) p) .
        clear H.
        {
          f_equal.
          remember (interp_formula ctx v).
          unfold app_nil_r'.
          simpl.
          unfold eq_trans, f_equal.
          remember (list_ind _ _ _ _ ).
          generalize y.
          clear Heqy.
          clear y.
          rewrite app_nil_r'.
          intros.
          dependent destruction y.
          reflexivity.
        }
        assert (interp_pattern (DCons t0 (interp_formula ctx v) (eq_rect_r DeepList ql (app_nil_r' type t_quantifiermap))) pnew
                =
                interp_pattern (eq_rect_r DeepList (DCons t0 (interp_formula ctx v) ql) (app_nil_r' type (t0 :: t_quantifiermap))) pnew).
        {
          f_equal.
          remember (interp_formula ctx v).
          unfold app_nil_r'.
          simpl.
          unfold eq_trans, f_equal.
          remember (list_ind _ _ _ _ ).
          generalize y.
          rewrite app_nil_r'.
          intros.
          dependent destruction y0.
          reflexivity.
        }
        etransitivity .
        exact H0.
        etransitivity .
        exact H.
        eauto.
      }
      {
        intros.
        assert (interp_pattern (DCons t0 (interp_formula ctx v) (eq_rect_r DeepList ql (app_nil_r' type t_quantifiermap))) p
                =
                interp_pattern (eq_rect_r DeepList (DCons t0 (interp_formula ctx v) ql) (app_nil_r' type (t0 :: t_quantifiermap))) p) .
        clear H.
        {
          f_equal.
          remember (interp_formula ctx v).
          unfold app_nil_r'.
          simpl.
          unfold eq_trans, f_equal.
          remember (list_ind _ _ _ _ ).
          generalize y.
          clear Heqy.
          clear y.
          rewrite app_nil_r'.
          intros.
          dependent destruction y.
          reflexivity.
        }
        assert (interp_pattern (DCons t0 (interp_formula ctx v) (eq_rect_r DeepList ql (app_nil_r' type t_quantifiermap))) pnew
                =
                interp_pattern (eq_rect_r DeepList (DCons t0 (interp_formula ctx v) ql) (app_nil_r' type (t0 :: t_quantifiermap))) pnew).
        {
          f_equal.
          remember (interp_formula ctx v).
          unfold app_nil_r'.
          simpl.
          unfold eq_trans, f_equal.
          remember (list_ind _ _ _ _ ).
          generalize y.
          rewrite app_nil_r'.
          intros.
          dependent destruction y0.
          reflexivity.
        }
        etransitivity.
        symmetry;
        exact H0.
        etransitivity.
        exact H.
        eauto.
      }
    }
    Qed.
*)
