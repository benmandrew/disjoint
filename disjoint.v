Require Import FunInd.

Inductive expr : Set :=
  | e_n : nat -> expr
  | e_skip : expr
  | e_deref : nat -> expr
  | e_assgn : nat -> expr -> expr
  | e_seq : expr -> expr -> expr.

Module Store.
  Definition t := nat -> option nat.

  Definition empty : t := fun l => None.

  Definition get (s : t) x := s x.

  Definition remove (s : t) (l : nat) : t :=
    fun l' => if Nat.eqb l l' then None else get s l'.

  Definition add (s : t) (l : nat) (n : nat) : t :=
    fun l' => if Nat.eqb l l' then Some n else get s l'.
End Store.

Inductive transition e0 s0 e1 s1 : Prop :=
  | t_deref : forall l n,
      e0 = e_deref l ->
      e1 = e_n n ->
      Some n = Store.get s0 l ->
      s0 = s1 ->
      transition e0 s0 e1 s1
  | t_assgn1 : forall l n,
      e0 = e_assgn l (e_n n) ->
      e1 = e_skip ->
      s1 = Store.add s0 l n ->
      transition e0 s0 e1 s1
  | t_assgn2 : forall l e0' e1',
      e0 = e_assgn l e0' ->
      e1 = e_assgn l e1' ->
      transition e0' s0 e1' s1 ->
      transition e0 s0 e1 s1
  | t_seq1 :
      e0 = e_seq e_skip e1 ->
      s0 = s1 ->
      transition e0 s0 e1 s1
  | t_seq2 : forall e0' e1' e'',
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
  induction e;
  intros e' s' e'' s'' Hl Hr;
  inversion Hl; inversion Hr; try discriminate.
  - split.
    + rewrite H0. rewrite H4. f_equal. rewrite H in H3. inversion H3.
    rewrite <- H8 in H5. rewrite <- H1 in H5. inversion H5. reflexivity.
    + rewrite H2 in H6. exact H6.
  - split.
    + rewrite H0. rewrite H3. reflexivity.
    + inversion H. inversion H2. rewrite H6 in H8. rewrite H7 in H9. inversion H9.
      rewrite <- H8 in H4. rewrite H10 in H1. rewrite <- H1 in H4. symmetry. exact H4.
  - inversion H. inversion H2. rewrite H7 in H9. rewrite <- H9 in H4. inversion H4; discriminate.
  - inversion H. inversion H2. rewrite H9 in H7. rewrite <- H7 in H1. inversion H1; discriminate.
  - inversion H. inversion H2. rewrite <- H7 in H1. rewrite <- H9 in H4.
    apply (IHe e1' s' e1'0 s'') in H1.
    + inversion H1. rewrite H5 in H0. rewrite H6 in H8. rewrite H8 in H0. rewrite H0. rewrite H3.
      rewrite H10. auto.
    + assumption.
  - inversion H. inversion H1. rewrite <- H5. rewrite H7.
    rewrite H2 in H0. rewrite H0. auto.
  - inversion H. inversion H1. rewrite H5 in H7. rewrite <- H7 in H3. inversion H3; discriminate.
  - inversion H. inversion H2. rewrite H7 in H5. rewrite <- H5 in H1. inversion H1; discriminate.
  - inversion H. inversion H2. rewrite <- H6 in H1. rewrite <- H8 in H4.
    apply (IHe1 e1' s' e1'0 s'') in H1.
    + inversion H1. rewrite H5 in H0. rewrite H7 in H9. rewrite H9 in H0. rewrite H0. rewrite H3.
      rewrite H10. auto.
    + assumption.
Qed.
