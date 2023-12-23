Require Import FunInd.
Require Import FunctionalExtensionality.
Require Import Nat.
Require Import Specif.

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

Module S.
  Definition t := nat -> option nat.

  Definition empty : t := fun _ => None.

  Definition get (s : t) l := s l.

  Definition remove (s : t) (l : nat) : t :=
    fun l' => if l =? l' then None else get s l'.

  Definition add (s : t) (l : nat) (n : nat) : t :=
    fun l' => if l =? l' then Some n else get s l'.

  Definition dom (s : t) : nat -> bool :=
    fun l => match get s l with
      | None => false
      | Some _ => true
      end.

  Lemma get_eq_dom : forall s l v,
    get s l = v ->
    dom s l = (match v with None => false | Some _ => true end).
  Proof.
    intros. unfold dom. subst. reflexivity.
  Qed.

  Lemma dom_eq_get : forall s l b,
    dom s l = b ->
    (match b with false => get s l = None | true => exists v, get s l = Some v end).
  Proof.
    intros. unfold dom in H. unfold get in H. case (s l) eqn:H1 in H; subst.
    - exists n. unfold get. assumption.
    - assumption.
  Qed.

  Lemma disjoint_absurd : forall s0 s1 l v0 v1,
    get s0 l = Some v0 ->
    get s1 l = Some v1 ->
    dom s0 l = false \/ dom s1 l = false -> False.
  Proof.
    intros. destruct H1.
    - apply get_eq_dom in H. rewrite H in H1. inversion H1.
    - apply get_eq_dom in H0. rewrite H0 in H1. inversion H1.
  Qed.

  Definition disjoint_union (s0 s1 : t) : nat -> option nat :=
    fun l =>
    match get s0 l, get s1 l with
    | Some v0, Some v1 => None
    | Some v, None => Some v
    | None, Some v => Some v
    | None, None => None
    end.
End S.

Notation "f + g" := (S.disjoint_union f g).

Inductive transition : expr -> S.t -> expr -> S.t -> Prop :=
  | t_deref : forall e0 s0 e1 s1 l n,
      e0 = e_deref l ->
      e1 = e_n n ->
      Some n = S.get s0 l ->
      s0 = s1 ->
      transition e0 s0 e1 s1
  | t_assgn1 : forall e0 s0 e1 s1 l n,
      e0 = e_assgn l (e_n n) ->
      e1 = e_skip ->
      s1 = S.add s0 l n ->
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

Lemma one_step_determinacy_expr : forall e s e0 s0 e1 s1,
  [e, s] ~> [e0, s0] -> [e, s] ~> [e1, s1] -> [e0, s0] = [e1, s1].
Proof.
  intros e s.
  induction e; intros e' s' e'' s'' Hl Hr;
  inversion Hl; inversion Hr; try discriminate; subst.
  - rewrite H in H7. inversion H7. rewrite H2 in H1.
    rewrite <- H1 in H9. inversion H9. constructor; reflexivity.
  - rewrite H in H6. inversion H6. constructor; reflexivity.
  - inversion H; inversion H6; subst. inversion H8; discriminate.
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

Lemma store_get_disjoint : forall s s' l n,
  Some n = S.get s l -> S.dom s' l = false -> Some n = S.get (s + s') l.
Proof.
  intros.
  apply (S.dom_eq_get s' l false) in H0.
  unfold S.get. unfold S.disjoint_union.
  rewrite <- H. rewrite H0. reflexivity.
Qed.

(* Requires function extensionality to show equality of stores *)
Lemma store_add_disjoint : forall s s' l n,
  S.dom s' l = false -> S.add s l n + s' = S.add (s + s') l n.
Proof.
  intros.
  apply (S.dom_eq_get s' l false) in H.
  unfold S.add. unfold S.disjoint_union.
Admitted.

Lemma irrelevant_store_can_be_added : forall e s e1 s1 s0,
  [e, s] ~> [e1, s1] ->
  (forall l, S.dom s0 l = false \/ S.dom s1 l = false) ->
  [e, s + s0] ~> [e1, s1 + s0].
Proof.
  intros.
  induction H; subst.
  - apply (t_deref _ _ _ _ l n); try reflexivity.
    specialize (H0 l). destruct H0 as [Hs0|Hs1].
    + apply (store_get_disjoint s2 s0 l n); assumption.
    + apply (S.dom_eq_get s2 l false) in Hs1.
      rewrite <- H2 in Hs1. discriminate.
  - apply (t_assgn1 _ _ _ _ l n); try reflexivity.
    specialize (H0 l). destruct H0 as [Hs0|Hs1].
    +
Admitted.

Lemma nat_eqb_refl : forall x, (x =? x) = true.
Proof.
  intros. induction x.
  - unfold Nat.eqb. reflexivity.
  - unfold Nat.eqb. apply IHx.
Qed.

Lemma irrelevant_store_can_be_removed : forall e s s0 e1 s1,
  [e, s + s0] ~> [e1, s1] ->
  (subset (loc e) (S.dom s)) ->
  exists s', [e, s] ~> [e1, s'] /\ s1 = s' + s0.
Proof.
  intros. induction H.
  - exists s. split.
    + rewrite H. rewrite H1. apply (t_deref (e_deref l) s (e_n n) s l n); try reflexivity.
      cut (S.dom s l = true).
      *intros.
        apply S.dom_eq_get in H4. destruct H4.
        rewrite H4.
Admitted.
