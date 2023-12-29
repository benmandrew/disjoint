Require Import FunInd.
Require Import FunctionalExtensionality.
Require Import PeanoNat.
Require Import Specif.

Require Import Program.

Inductive expr : Set :=
  | e_n : nat -> expr
  | e_skip : expr
  | e_deref : nat -> expr
  | e_assgn : nat -> expr -> expr
  | e_seq : expr -> expr -> expr.

Fixpoint loc (e : expr) : nat -> bool :=
  fun l' =>
  match e with
  | e_n _ => false
  | e_skip => false
  | e_deref l => l =? l'
  | e_assgn l e => if l =? l' then true else loc e l'
  | e_seq e1 e2 => if loc e1 l' then true else loc e2 l'
  end.

Definition subset (s0 s1 : nat -> bool) : Prop :=
  forall l, s0 l = true -> s1 l = true.

(* Partial store supporting decidable disjoint union *)
Module S.
  Definition t := nat -> option nat.

  Definition empty : t := fun _ => None.

  Definition remove (s : t) (l : nat) : t :=
    fun l' => if l =? l' then None else s l'.

  Definition add (s : t) (l : nat) (n : nat) : t :=
    fun l' => if l =? l' then Some n else s l'.

  Definition disjoint_dec (s0 s1 : t) : Set :=
    forall l, { s0 l = None } + { s1 l = None }.

  Definition disjoint_dec_l (s0 s1 : t) l : Set :=
    { s0 l = None } + { s1 l = None }.

  (* Definition disjoint_union :
      forall s0 s1, (disjoint_dec s0 s1) -> nat -> option nat.
    refine (
      fun s0 s1 pf l =>
      match s0 l as v0, s1 l as v1 with
      | Some v0, Some v1 => _
      | Some v, None => Some v
      | None, Some v => Some v
      | None, None => None
      end).
    auto.
  Defined. *)

    (*  return
      ({v0' = None} + {v1' = None}) -> option nat *)

  Lemma lem : forall (v0 v1 : nat),
    {Some v0 = None} + {Some v1 = None} -> False.
  Proof.
    intros. destruct H; discriminate.
  Qed.

  (* (s0 s1 : t) (pf : disjoint_dec s0 s1) (l : nat) *)

  Definition disjoint_union :
      forall s0 s1, (disjoint_dec s0 s1) -> nat -> option nat.
    refine (
      fun s0 s1 pf l =>
      (match s0 l as v0', s1 l as v1' return
        {v0' = None} + {v1' = None} -> option nat
      with
      | Some v0, Some v1 => fun pf' => match lem v0 v1 pf' with end
      | Some v, None => fun _ => Some v
      | None, Some v => fun _ => Some v
      | None, None => fun _ => None
      end) _).
    destruct (pf l); auto.
  Defined.
    
End S.

Axiom functional_extensionality :
  forall {X Y : Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

Inductive transition : expr -> S.t -> expr -> S.t -> Prop :=
  | t_deref : forall e0 s0 e1 s1 l n,
      e0 = e_deref l ->
      e1 = e_n n ->
      Some n = s0 l ->
      s0 = s1 ->
      transition e0 s0 e1 s1
  | t_assgn1 : forall e0 s0 e1 s1 l n,
      e0 = e_assgn l (e_n n) ->
      e1 = e_skip ->
      s1 = S.add s0 l n ->
      (exists n', s0 l = Some n') ->
      transition e0 s0 e1 s1
  | t_assgn2 : forall e0 s0 e1 s1 l e0' e1',
      e0 = e_assgn l e0' ->
      e1 = e_assgn l e1' ->
      transition e0' s0 e1' s1 ->
      transition e0 s0 e1 s1
  | t_seq1 : forall e0 s0 e1 s1,
      e0 = e_seq e_skip e1 ->
      s0 = s1 ->
      transition e0 s0 e1 s1
  | t_seq2 : forall e0 s0 e1 s1 e0' e1' e'',
      e0 = e_seq e0' e'' ->
      e1 = e_seq e1' e'' ->
      transition e0' s0 e1' s1 ->
      transition e0 s0 e1 s1.

Notation "[ e0 , s0 ] '~>' [ e1 , s1 ]" := (transition e0 s0 e1 s1) (at level 20).
Notation "[ e0 , s0 ] = [ e1 , s1 ]" := (e0 = e1 /\ s0 = s1) (at level 20).
Notation "f + g | pf" := (S.disjoint_union f g pf) (at level 20).

Lemma one_step_determinacy_expr : forall e s e0 s0 e1 s1,
  [e, s] ~> [e0, s0] -> [e, s] ~> [e1, s1] -> [e0, s0] = [e1, s1].
Proof.
  intros e s.
  induction e; intros e' s' e'' s'' Hl Hr;
  inversion Hl; inversion Hr; try discriminate; subst.
  - rewrite H in H7. inversion H7. rewrite H2 in H1.
    rewrite <- H1 in H9. inversion H9. constructor; reflexivity.
  - rewrite H in H7. inversion H7. constructor; reflexivity.
  - inversion H; inversion H7; subst. inversion H9; discriminate.
  - inversion H; inversion H6; subst. inversion H1; discriminate.
  - inversion H; inversion H6; subst.
    apply (IHe e1' s' e1'0 s'') in H1.
    + inversion H1; subst. constructor; reflexivity.
    + assumption.
  - inversion H; subst. inversion H5. constructor; reflexivity.
  - inversion H; subst. inversion H5; subst. inversion H7; discriminate.
  - inversion H; inversion H6; subst. inversion H1; discriminate.
  - inversion H; subst. inversion H6; subst.
    apply (IHe1 e1' s' e1'0 s'') in H1.
    + inversion H1; subst. constructor; reflexivity.
    + assumption.
Qed.

Lemma store_get_disjoint : forall (s s' : S.t) l pf n,
  Some n = s l -> Some n = (s + s' | pf) l.
Proof.
  intros.
  unfold S.disjoint_union.
  destruct (pf l).
  - rewrite e in H. discriminate.
  - rewrite <- H. rewrite e. reflexivity.
Qed.

Lemma store_add_disjoint :
  forall s s' l (pf : S.disjoint_dec s s') (pf0 : s' l = None) n,
  { pf' | (S.add s l n + s' | pf') = S.add (s + s' | pf) l n }.
Proof.
  intros.
  cut (S.disjoint_dec (S.add s l n) s').
  - intros pf'. exists pf'.
    unfold S.disjoint_union.
    unfold S.add.
    unfold S.disjoint_union.
    apply functional_extensionality; intro.
    case_eq (Nat.eqb l x); intro.
    + apply Nat.eqb_eq in H. subst.
      rewrite pf0. reflexivity.
    + case_eq (s x); case_eq (s' x); intros; try reflexivity.
      destruct (pf x).
      * rewrite e in H1. discriminate.
      * rewrite e in H0. discriminate.
  - unfold S.disjoint_dec. intros.
    destruct (pf l0);
    case_eq (Nat.eqb l l0); intros.
    * apply Nat.eqb_eq in H. subst. right. assumption.
    * left. unfold S.add. rewrite H. assumption.
    * right. assumption.
    * right. assumption.
Qed.

Lemma irrelevant_store_can_be_added : forall e s e1 s1 s0 pf0 pf1,
  [e, s] ~> [e1, s1] -> [e, s + s0 | pf0] ~> [e1, s1 + s0 | pf1].
Proof.
  intros.
  induction H; subst.
  - apply (t_deref _ _ _ _ l n); try reflexivity.
    destruct (pf0 l).
    { rewrite e in H1. discriminate. }
    + unfold S.disjoint_union. rewrite <- H1. rewrite e. reflexivity.
  - apply (t_assgn1 _ _ _ _ l n); try reflexivity; destruct H2 as [n' H2].
    unfold S.disjoint_union.
    + unfold S.add. unfold S.disjoint_union.
      apply functional_extensionality. intros.
      destruct_with_eqn (Nat.eqb l x).
      destruct_with_eqn (s0 x).









    (* destruct (pf0 l); destruct (pf1 l);
    case_eq (Nat.eqb l x); intro.
    + unfold S.add in e0. rewrite Nat.eqb_refl in e0. discriminate.
    + unfold S.add in e0. rewrite Nat.eqb_refl in e0. discriminate.
    + apply Nat.eqb_eq in H. subst. rewrite e0. reflexivity.
    + case (s1 x); case (s0 x); intros.
      * case_eq (Nat.eqb l n0); intros.
        --apply Nat.eqb_eq in H0. subst. rewrite e. *)




  (* - apply (t_deref _ _ _ _ l n); try reflexivity.
    specialize (H0 l). destruct H0 as [Hs0|Hs1].
    + apply (store_get_disjoint s2 s0 l n); assumption.
    + apply (S.dom_eq_get s2 l false) in Hs1.
      rewrite <- H2 in Hs1. discriminate.
  - apply (t_assgn1 _ _ _ _ l n); try reflexivity.
    specialize (H0 l). destruct H0 as [Hs0|Hs1].
    + apply store_add_disjoint. assumption.
    + unfold S.dom in Hs1. unfold in Hs1. unfold S.add in Hs1.
      rewrite (Nat.eqb_refl l) in Hs1. inversion Hs1.
  - apply (t_assgn2 _ _ _ _ l e0' e1'); try reflexivity.
    apply IHtransition in H0. assumption.
  - apply (t_seq1 _ _ _ _); try reflexivity.
  - apply (t_seq2 _ _ _ _ e0' e1' e''); try reflexivity.
    apply IHtransition in H0. assumption. *)
Qed.

Lemma irrelevant_store_can_be_removed : forall e s s0 e1 s1,
  [e, s + s0] ~> [e1, s1] ->
  (subset (loc e) (S.dom s)) ->
  exists s', [e, s] ~> [e1, s'] /\ s1 = s' + s0.
Proof.
  intros. remember (s + s0) as s2 in H. induction H; subst.
  - exists s. split; try reflexivity.
    apply (t_deref _ _ _ _ l n); try reflexivity.
    unfold subset in H0. specialize (H0 l).




    (* + rewrite H. rewrite H1. apply (t_deref (e_deref l) s (e_n n) s l n); try reflexivity.
      cut (S.dom s l = true).
      *intros.
        apply S.dom_eq_get in H4. destruct H4.
        rewrite H4. *)
Admitted.
