Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Cases.
Require Import Patt.
Require Import EnvModule.

Module TermImpl <: TERM.
  Definition term := Patt.term.
End TermImpl.

Module StdEnv := ENV(TermImpl).
Import StdEnv.

Definition try_lookup (v : var) (e : env) : patt :=
  match lookup v e with
    | None => pvar v
    | Some t => term_to_patt t
  end.

Fixpoint subs (e : env) (p : patt) : patt :=
  match p with
    | pvar v => try_lookup v e
    | pnode n ps => pnode n (map (subs e) ps)
  end.

Notation "e * p" := (subs e p).

Lemma lookup_eqv : forall (v : var) (e1 e2 : env),
  lookup v e1 = lookup v e2 -> try_lookup v e1 = try_lookup v e2.
Proof.
  intros. unfold try_lookup. rewrite H. reflexivity.
Qed.

Lemma env_eqv_subs : forall (e1 e2 : env) (p : patt),
  e1 ~= e2 -> e1 * p = e2 * p.
Proof.
  intros. induction p.
  Case "var v". simpl. unfold env_eqv in H.
    apply lookup_eqv. apply H.
  Case "node n nil". reflexivity.
  Case "node n (p :: ps)". simpl. rewrite IHp.
  inversion IHp0. rewrite H1. reflexivity.
Qed.

Lemma mtEnv_subs_l : forall (p : patt), mtEnv * p = p.
Proof.
  intros. induction p; try reflexivity.
  Case "node n (p :: ps)". inversion IHp0.
    simpl. rewrite IHp. rewrite H0. rewrite H0. reflexivity.
  Qed.

Lemma mem__subs_closed : forall (v : var) (e : env),
  mem v e -> closed (e * (pvar v)).
Proof.
  intros. simpl.
  unfold mem in H. unfold bmem in H.
  unfold try_lookup. destruct (lookup v e).
  Case "v in e".
    apply term_to_patt_closed. inversion H.
Qed.

Lemma closed_subs : forall (p : patt) (e : env),
  closed p -> e * p = p.
Proof.
  intros. induction p.
  Case "var". inversion H.
  Case "node n nil". reflexivity.
  Case "node n (p :: ps)". simpl in *.
    inversion H; clear H.
    apply IHp in H0; clear IHp. rewrite H0.
    apply IHp0 in H1; clear IHp0. inversion H1.
      rewrite H2. rewrite H2. reflexivity.
Qed.

Lemma try_lookup_not_member : forall (v : vid) (e : env),
  ~ (mem v e) -> try_lookup v e = pvar v.
Proof.
  intros. assert (G : lookup v e = None).
    apply lookup_not_member. exact H.
  unfold try_lookup. rewrite G. reflexivity.
Qed.

Lemma compose_try_lookup_l : forall (e1 e2 e12 : env) (v : vid),
  mem v e1 ->
  e1 & e2 = Some e12 ->
  try_lookup v e12 = try_lookup v e1.
Proof.
  intros. apply lookup_eqv.
  apply compose_lookup_l with (e2 := e2); assumption.
Qed.

Lemma compose_try_lookup_r : forall (e1 e2 e12 : env) (v : vid),
  mem v e2 ->
  compose_env e1 e2 = Some e12 ->
  try_lookup v e12 = try_lookup v e2.
Proof.
  intros. apply lookup_eqv.
  apply compose_lookup_r with (e1 := e1); assumption.
Qed.

Lemma env_subs_comm : forall (e1 e2 e12 : env) (p : patt),
  e1 & e2 = Some e12 ->
  e12 * p = e1 * (e2 * p).
Proof.
  intros. induction p.
  Case "var v".
    destruct (bmem v e1) eqn:V1; destruct (bmem v e2) eqn:V2;
      try apply bmem_true in V1; try apply bmem_true in V2.
    SCase "v in e1, e2".
      assert (C : e1 & e2 = None).
      apply compose_overlap with (v := v). exact V1. exact V2.
      rewrite C in H. inversion H.
    SCase "v in e1, not in e2".
      simpl. apply bmem_false in V2.
      assert (L2 : try_lookup v e2 = pvar v).
        apply try_lookup_not_member. exact V2.
      assert (L12 : try_lookup v e12 = try_lookup v e1).
        apply compose_try_lookup_l with (e2 := e2). exact V1. exact H.
      rewrite L2. rewrite L12. simpl. reflexivity.
    SCase "v in e2, not in e1".
      simpl. apply bmem_false in V1.
      assert (L12 : try_lookup v e12 = try_lookup v e2).
        apply compose_try_lookup_r with (e1 := e1). exact V2. exact H.
      assert (G : closed (try_lookup v e2)).
        apply mem__subs_closed. exact V2.
      apply closed_subs with (e := e1) in G.
      rewrite G. rewrite L12. reflexivity.
    SCase "v not in e1, e2".
      simpl. apply bmem_false in V1. apply bmem_false in V2.
      assert (L12 : try_lookup v e12 = try_lookup v e2).
        apply lookup_eqv.
        apply compose_not_member with (e1 := e1). exact V1. exact H.
      assert (L2 : try_lookup v e2 = pvar v).
        apply try_lookup_not_member. exact V2.
      assert (L1 : try_lookup v e1 = pvar v).
        apply try_lookup_not_member. exact V1.
      rewrite L12. rewrite L2. simpl. rewrite L1. reflexivity.
  Case "node n nil".
    reflexivity.
  Case "node n (t :: ts)".
    simpl. rewrite IHp.
    inversion IHp0. rewrite H1.
    reflexivity.
Qed.
