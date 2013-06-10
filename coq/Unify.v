Require Import Coq.Arith.EqNat.
Require Import Cases.
Require Import Util.
Require Import Term.
Require Import Subs.
Require Import Match.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.
Import StdEnv.

Fixpoint unify p q : option term :=
  match (p, q) with
    | (tvar v, q) => Some q
    | (p, tvar v) => Some p
    | (const c1, const c2) => if beq_id c1 c2
                              then Some (const c1)
                              else None
    | (empty, empty) => Some empty
    | (p1 :: p2, q1 :: q2) =>
      r1 <- unify p1 q1;
      r2 <- unify p2 q2;
      Some (r1 :: r2)
    | (_, _) => None
  end.
Notation "p ^ q" := (unify p q).

Lemma unify_tmatch_left : forall p q r,
  p ^ q = Some r ->
  wf p = true ->
  exists a, r / p = Some a.
Proof.
  intros. generalize dependent r. generalize dependent q.
  induction p.
  Case "p = tvar".
    intros. simpl. eauto.
  Case "p = const".
    destruct q; intros; try discriminate.
    SCase "q = tvar".
      simpl in H. inversion H. simpl. rewrite beq_id_refl. eauto.
    SCase "q = const".
      simpl in H. destruct (beq_id i i0) eqn:I; inversion H.
      simpl. rewrite beq_id_refl. eauto.
  Case "p = empty".
    destruct q; intros; try discriminate.
    SCase "q = tvar".
      simpl in H. inversion H. simpl. eauto.
    SCase "q = empty".
      inversion H. simpl. eauto.
  Case "p = cons".
    intros.
    rename H0 into WF. rewrite wf_cons_iff in WF.
      inversion WF as (WF1 & WF2 & D).
    destruct q; intros; try discriminate.
    SCase "q = tvar".
      apply wf_true in WF1. inversion WF1 as (a & A).
      apply wf_true in WF2. inversion WF2 as (b & B).
      simpl in H. inversion H. simpl.
      rewrite A. rewrite B. simpl.
      rewrite fvar_disjoint_union in D; eauto.
      rewrite disjoint_iff in D. exact D.
    SCase "q = cons".
      simpl in H.
      destruct (p1 ^ q1) eqn:U1; destruct (p2 ^ q2) eqn:U2; try discriminate H.
      rename t into t1; rename t0 into t2.
      assert (E1: exists a1, t1 / p1 = Some a1) by (eapply IHp1; eauto).
      assert (E2: exists a2, t2 / p2 = Some a2) by (eapply IHp2; eauto).
      inversion E1 as (a1 & A1).
      inversion E2 as (a2 & A2).
      simpl in H. inversion H. simpl.
      rewrite A1. rewrite A2. simpl.
      rewrite fvar_disjoint_union in D; eauto.
      rewrite disjoint_iff in D. exact D.
Qed.

Lemma unify_tmatch_right : forall p q r,
  p ^ q = Some r ->
  wf q = true ->
  exists a, r / q = Some a.
Proof.
  intros. generalize dependent r. generalize dependent p.
  induction q.
  Case "q = tvar".
    intros. simpl. eauto.
  Case "q = const".
    destruct p; intros; try discriminate.
    SCase "p = tvar".
      simpl in H. inversion H. simpl. rewrite beq_id_refl. eauto.
    SCase "p = const".
      simpl in H. destruct (beq_id i0 i) eqn:I; inversion H.
      simpl. apply beq_id_true in I. rewrite I. rewrite beq_id_refl. eauto.
  Case "q = empty".
    destruct p; intros; try discriminate.
    SCase "p = tvar".
      simpl in H. inversion H. simpl. eauto.
    SCase "p = empty".
      inversion H. simpl. eauto.
  Case "q = cons".
    intros.
    rename H0 into WF. rewrite wf_cons_iff in WF.
      inversion WF as (WF1 & WF2 & D).
    destruct p; intros; try discriminate.
    SCase "p = tvar".
      apply wf_true in WF1. inversion WF1 as (a & A).
      apply wf_true in WF2. inversion WF2 as (b & B).
      simpl in H. inversion H. simpl.
      rewrite A. rewrite B. simpl.
      rewrite fvar_disjoint_union in D; eauto.
      rewrite disjoint_iff in D. exact D.
    SCase "p = cons".
      simpl in H.
      destruct (p1 ^ q1) eqn:U1; destruct (p2 ^ q2) eqn:U2; try discriminate H.
      rename t into t1; rename t0 into t2.
      assert (E1: exists a1, t1 / q1 = Some a1) by (eapply IHq1; eauto).
      assert (E2: exists a2, t2 / q2 = Some a2) by (eapply IHq2; eauto).
      inversion E1 as (a1 & A1).
      inversion E2 as (a2 & A2).
      simpl in H. inversion H. simpl.
      rewrite A1. rewrite A2. simpl.
      rewrite fvar_disjoint_union in D; eauto.
      rewrite disjoint_iff in D. exact D.
Qed.

Lemma tmatch__unify : forall p q a b,
  a * p = b * q -> exists r, p ^ q = Some r.
Proof.
  intros.
  generalize dependent q.
  induction p; destruct q; try discriminate; simpl; try eauto.
  Case "consts".
    intros. inversion H. rewrite beq_id_refl. eauto.
  Case "conss".
    intros.
    inversion H.
    apply IHp1 in H1. inversion H1 as (r1 & R1).
    apply IHp2 in H2. inversion H2 as (r2 & R2).
    rewrite R1. rewrite R2. simpl. eauto.
Qed.

Definition ununifyable p q :=
  match unify p q with
    | Some _ => false
    | None => true
  end.
