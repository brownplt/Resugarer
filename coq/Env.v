Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Cases.

Module Type VALUE.
  Parameter val : Type.
  Parameter var : Type.
  Parameter beq_var : var -> var -> bool.

  Parameter beq_var_refl : forall (v : var),
    beq_var v v = true.
  Parameter beq_var_sym : forall (x y : var),
    beq_var x y = beq_var y x.
  Parameter beq_var_trans : forall (x y z : var),
    beq_var x y = true -> beq_var y z = true -> beq_var x z = true.
End VALUE.

Module ENV (Import Value : VALUE).

  Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.

  Definition beq_var_eq v1 v2 := beq_var v1 v2 = true.
  Lemma beq_var_eq_refl : forall v, beq_var_eq v v. 
    Proof. apply beq_var_refl. Qed.
  Lemma beq_var_eq_sym : forall v1 v2, beq_var_eq v1 v2 -> beq_var_eq v2 v1.
    Proof. intros. unfold beq_var_eq. rewrite beq_var_sym. auto. Qed.
  Lemma beq_var_eq_trans : forall v1 v2 v3, beq_var_eq v1 v2 -> beq_var_eq v2 v3 -> beq_var_eq v1 v3.
    Proof. unfold beq_var_eq; intros. apply beq_var_trans with v2; auto. Qed.
  Add Relation var beq_var_eq
  reflexivity proved by beq_var_eq_refl
  symmetry proved by beq_var_eq_sym
  transitivity proved by beq_var_eq_trans
    as Beq_var.

  Instance Beq_var_Setoid : Setoid var :=
    {equiv := beq_var_eq; setoid_equiv := Beq_var}.

  Require Import Coq.Logic.Decidable.
  Lemma beq_var_eq_dec : forall v1 v2, decidable (v1 == v2).
  Proof. unfold decidable. intros. destruct (beq_var v1 v2) eqn:v1v2. 
    left; auto. rewrite <- Bool.not_true_iff_false in v1v2. right; auto.
  Qed.

  Inductive env :=
  | mtEnv : env
  | bind : var -> val -> env -> env.

  Fixpoint lookup (v : var) (e : env) : option val :=
    match e with
      | mtEnv => None
      | bind v' t e =>
        if beq_var v v'
          then Some t
          else lookup v e
    end.

  Definition bmem (v : var) (e : env) : bool :=
    match lookup v e with
      | None => false
      | Some _ => true
    end.

  Definition mem (v : var) (e : env) : Prop :=
    bmem v e = true.

(*
  Definition env_eqv (e1 e2 : env) :=
    forall (v : var), lookup v e1 = lookup v e2.

  Lemma env_eqv_refl : forall e, env_eqv e e. 
  Proof. unfold env_eqv. reflexivity. Qed.
  Lemma env_eqv_sym : forall e f, env_eqv e f -> env_eqv f e.
  Proof. unfold env_eqv. intros. symmetry; auto. Qed.
  Lemma env_eqv_trans : forall e f g, env_eqv e f -> env_eqv f g -> env_eqv e g.
  Proof. unfold env_eqv. intros. rewrite H; auto. Qed.

  Add Relation env env_eqv
  reflexivity proved by env_eqv_refl
  symmetry proved by env_eqv_sym
    transitivity proved by env_eqv_trans
    as Env_eqv.

  Instance env_eqv_Setoid : Setoid env :=
    {equiv := env_eqv; setoid_equiv := Env_eqv}.

  Add Parametric Morphism : lookup with signature (equiv ==> equiv ==> eq) as Lookup_beq_var.
  Proof.
    intros. generalize dependent x0; induction y0; intros x0 H0; rewrite H0; auto.
    simpl. destruct (beq_var x v) eqn:xv; destruct (beq_var y v) eqn:yv;
    try change (x == v) in xv; try change (y == v) in yv; try rewrite <- Bool.not_true_iff_false in *;
    try change (y =/= v) in yv; try change (x =/= v) in xv; auto. 
    rewrite <- xv in yv. 
    symmetry in H; contradiction. rewrite <- yv in xv; contradiction.
    apply IHy0. reflexivity.
  Qed.

  Add Parametric Morphism : bmem with signature (equiv ==> equiv ==> eq) as bmem_beq_var.
  Proof.
    unfold bmem. intros. rewrite H. rewrite H0. reflexivity.
  Qed.

  Add Parametric Morphism : mem with signature (equiv ==> equiv ==> eq) as mem_beq_var.
  Proof.
    unfold mem; intros; rewrite H; rewrite H0; reflexivity.
  Qed.

*)

  Add Parametric Morphism : lookup with signature (equiv ==> eq ==> eq) as Lookup_beq_var.
  Proof.
    intros. induction y0; auto.
    simpl. destruct (beq_var x v) eqn:xv; destruct (beq_var y v) eqn:yv;
    try change (x == v) in xv; try change (y == v) in yv; try rewrite <- Bool.not_true_iff_false in *;
    try change (y =/= v) in yv; try change (x =/= v) in xv; auto. 
    rewrite <- xv in yv.
    symmetry in H; contradiction. rewrite <- yv in xv; contradiction.
  Qed.

  Add Parametric Morphism : bmem with signature (equiv ==> eq ==> eq) as bmem_beq_var.
  Proof.
    unfold bmem. intros. rewrite H. reflexivity.
  Qed.

  Add Parametric Morphism : mem with signature (equiv ==> eq ==> eq) as mem_beq_var.
  Proof.
    unfold mem; intros; rewrite H; reflexivity.
  Qed.




  Fixpoint disjoint (e1 e2 : env) : bool :=
    match e1 with
      | mtEnv => true
      | bind v _ e1 => negb (bmem v e2) && disjoint e1 e2
    end.

  (* Juxtposition *)
  Fixpoint concat (e1 e2 : env) : env :=
    match e1 with
      | mtEnv => e2
      | bind v t e => bind v t (concat e e2)
    end.
  Notation "e1 ++ e2" := (concat e1 e2).

  (* Disjoint union *)
  Definition union (e1 e2 : env) : option env :=
    if disjoint e1 e2
      then Some (e1 ++ e2)
      else None.
  Notation "x & y" := (union x y) (at level 60).


(*******************)
(*** Easy Lemmas ***)
(*******************)

  Lemma mem_mtEnv : forall (v : var), ~ (mem v mtEnv).
  Proof. intros. unfold mem. simpl. exact (Bool.diff_false_true). Qed.

  Lemma mem_bind : forall (v v' : var) (t : val) (e : env),
    mem v e -> mem v (bind v' t e).
  Proof.
    intros.
    unfold mem in H. unfold mem.
    unfold bmem in H. unfold bmem.
    unfold lookup in H. unfold lookup.
    destruct (beq_var v v').
      reflexivity.
      exact H.
  Qed.

  Lemma mem_bind_same : forall (v v' : var) (t : val) (e : env),
    v == v' -> mem v (bind v' t e).
  Proof.
    intros. unfold mem. rewrite H. unfold bmem. simpl. rewrite beq_var_refl; auto.
  Qed.

  Lemma mem_bind_diff : forall (v v' : var) (t : val) (e : env),
    v =/= v' -> mem v (bind v' t e) -> mem v e.
  Proof.
    intros. unfold mem in *. unfold bmem in *. simpl in H0.
    destruct (beq_var v v') eqn:vv'. contradiction. auto.
  Qed.

  Lemma bmem_true : forall (v : var) (e : env),
    bmem v e = true -> mem v e.
  Proof. intros. unfold mem. exact H. Qed.

  Lemma bmem_false : forall (v : var) (e : env),
    bmem v e = false -> ~ (mem v e).
  Proof.
    intros. unfold mem. destruct (bmem v e).
    inversion H.
    exact Bool.diff_false_true.
  Qed.

  Lemma lookup_bind_eq : forall (v : var) (t : val) (e : env),
    lookup v (bind v t e) = Some t.
  Proof.
    intros. unfold lookup. rewrite beq_var_refl. reflexivity.
  Qed.

  Lemma lookup_bind_eqv : forall (v v' : var) (t : val) (e : env),
    v == v' -> lookup v (bind v' t e) = Some t.
  Proof.
    intros. unfold lookup.
    rewrite H. reflexivity.
  Qed.

  Lemma lookup_bind_diff : forall (v v' : var) (t : val) (e : env),
    v =/= v' -> lookup v (bind v' t e) = lookup v e.
  Proof.
    intros. unfold lookup. destruct (beq_var v v') eqn:vv'. 
    change (v == v') in vv'; contradiction. reflexivity.
  Qed.

  Lemma disjoint_mtEnv_l : forall e, disjoint mtEnv e = true.
  Proof. reflexivity. Qed.

  Lemma disjoint_mtEnv_r : forall e, disjoint e mtEnv = true.
  Proof. intros. induction e; auto. Qed.

  Lemma disjoint_bind_r : forall v t e1 e2,
    disjoint (bind v t e1) e2 = negb (bmem v e2) && disjoint e1 e2.
  Proof. auto. Qed.

  Lemma disjoint_bind_l : forall e1 v t e2,
    disjoint e1 (bind v t e2) = negb (bmem v e1) && disjoint e1 e2.
  Proof.
    intros.
    induction e1 as [|v1 t1 e1].
    Case "e1 = mtEnv".
      reflexivity.
    Case "e1 = bind v1 t1 e1".
      simpl. rewrite IHe1.
      assert (L: forall u v t e,
        negb (bmem u (bind v t e)) = negb (beq_var u v) && negb (bmem u e)).
      intros. rewrite <- negb_orb.
        unfold bmem, lookup.
        destruct (beq_var u v0); simpl; reflexivity.
      rewrite L. rewrite L. rewrite beq_var_sym.
      assert (Z: forall a b c d, a && b && (c && d) = a && c && (b && d)).
        intros. destruct a, b, c, d; reflexivity.
      apply Z.
  Qed.

  Lemma disjoint_sym : forall e1 e2, disjoint e1 e2 = disjoint e2 e1.
  Proof.
    intros.
    induction e1 as [|v1 t1 e1]; intros.
    Case "mtEnv".
      rewrite disjoint_mtEnv_r. reflexivity.
    Case "e1 = bind v1 t1 e1".
      rewrite disjoint_bind_l, disjoint_bind_r, IHe1.
      reflexivity.
  Qed.

  Lemma disjoint_overlap : forall v e1 e2,
    mem v e1 -> mem v e2 -> disjoint e1 e2 = false.
  Proof.
    intros. induction e1 as [|v1 t1 e1].
    Case "e1 = mtEnv". inversion H.
    Case "e1 = bind v1 t1 e1". simpl.
      destruct (bmem v1 e2) eqn:M; try reflexivity. unfold mem in H0.
      destruct (beq_var_eq_dec v v1).
      SCase "v == v1".
        rewrite H1 in *. rewrite H0 in M. inversion M.
      SCase "v != v1".
        apply mem_bind_diff in H. apply IHe1 in H. simpl. exact H.
        exact H1.
  Qed.

  Lemma disjoint_false : forall e1 e2,
    disjoint e1 e2 = false -> e1 & e2 = None.
  Proof. intros. unfold union. rewrite H. reflexivity. Qed.

  Lemma disjoint_true : forall e1 e2,
    disjoint e1 e2 = true -> e1 & e2 = Some (e1 ++ e2).
  Proof. intros. unfold union. rewrite H. reflexivity. Qed.

  Lemma disjoint_iff : forall e1 e2,
    disjoint e1 e2 = true <-> exists e12, e1 & e2 = Some e12.
  Proof.
    intros. split.
    Case "disjoint".
      intros. apply disjoint_true in H.
      exists (e1 ++ e2). exact H.
    Case "not disjoint".
      intros. inversion H. unfold union in H0.
      destruct (disjoint e1 e2); auto. inversion H0.
  Qed.


(*********************)
(*** Concat Lemmas ***)
(*********************)


  Lemma concat_mtEnv_l : forall e, mtEnv ++ e = e.
  Proof. reflexivity. Qed.

  Lemma concat_mtEnv_r : forall e, e ++ mtEnv = e.
  Proof. intros. induction e; simpl; try rewrite IHe; auto. Qed.

  Lemma lookup_concat_mem : forall v e1 e2,
    mem v e1 -> lookup v (e1 ++ e2) = lookup v e1.
  Proof.
    intros. induction e1 as [|v1 t1 e1].
    Case "e1 = mtEnv". contradict H. apply mem_mtEnv.
    Case "e1 = bind v1 t1 e1".
      simpl. unfold mem, bmem, lookup in H.
      destruct (beq_var v v1); try auto.
  Qed.
  Hint Resolve lookup_concat_mem.

  Lemma lookup_concat_not_mem : forall (v : var) (e1 e2 : env),
    ~ (mem v e1) -> lookup v (e1 ++ e2) = lookup v e2.
  Proof.
    intros. generalize dependent e2. induction e1 as [|v1 t1 e1].
    Case "mtEnv".
      intros. simpl. reflexivity.
    Case "bind v1 t1 e1".
      intros. unfold mem in *. unfold bmem in *. simpl in *.
      destruct (beq_var v v1).
      SCase "v == v1". tauto.
      SCase "v /= v1".
        apply IHe1. exact H.
  Qed.
  Hint Resolve lookup_concat_not_mem.

  Lemma lookup_not_mem : forall (v : var) (e : env),
    ~ (mem v e) <-> lookup v e = None.
  Proof.
    intros; split. intros.
    destruct (lookup v e) eqn:ve; auto. unfold mem in H. unfold bmem in H.
    rewrite ve in H. tauto.
    intro; intro. unfold mem, bmem in H0.
    destruct (lookup v e). inversion H. inversion H0.
  Qed.
  Hint Resolve lookup_not_mem.


(********************)
(*** Union Lemmas ***)
(********************)

  Lemma union_mtEnv_l : forall (e : env), mtEnv & e = Some e.
  Proof. reflexivity. Qed.

  Lemma union_mtEnv_r : forall (e : env), e & mtEnv = Some e.
  Proof.
    intros. induction e.
    Case "mtEnv". reflexivity.
    Case "bind v t e". unfold union.
      rewrite disjoint_mtEnv_r. rewrite concat_mtEnv_r. reflexivity.
  Qed.

  Lemma union_overlap : forall (e1 e2 : env) (v : var),
    mem v e1 -> mem v e2 -> e1 & e2 = None.
  Proof.
    intros. apply disjoint_false.
    apply disjoint_overlap with (v:=v); auto.
  Qed.

  Ltac elim_bmems :=
    repeat match goal with
             | [ H : bmem _ _ = true |- _ ]  => apply bmem_true in H
             | [ H : bmem _ _ = false |- _ ] => apply bmem_false in H
           end.
  
  Lemma env_comm : forall (e1 e2 e12 : env),
    disjoint e1 e2 = true -> forall v, lookup v (e1 ++ e2) = lookup v (e2 ++ e1).
  Proof.
    intros. rename H into D12.
    assert (D21: disjoint e2 e1 = true) by
      (rewrite disjoint_sym; assumption).
    assert (D12' := D12).
    apply disjoint_true in D12. apply disjoint_true in D21.
    destruct (e2 & e1) as [e21|] eqn:E21; try inversion D21.
    (* Prove e1 ++ e2 == e2 ++ e1 *)
    destruct (bmem v e1) eqn:M1; destruct (bmem v e2) eqn:M2; elim_bmems.
    Case "v in e1, e2".
      assert (C: disjoint e1 e2 = false).
        apply disjoint_overlap with (v:=v); auto.
      rewrite D12' in C; inversion C.
    Case "v in e1, not in e2".
      assert (L1: lookup v (e1 ++ e2) = lookup v e1) by auto.
      assert (L2: lookup v (e2 ++ e1) = lookup v e1) by auto.
      rewrite L1; rewrite L2; reflexivity.
    Case "v in e2, not in e1".
      assert (L1: lookup v (e1 ++ e2) = lookup v e2) by auto.
      assert (L2: lookup v (e2 ++ e1) = lookup v e2) by auto.
      rewrite L1; rewrite L2; reflexivity.
    Case "v not in e1, e2".
      assert (L12: lookup v (e1 ++ e2) = lookup v e2) by auto.
      assert (L21: lookup v (e2 ++ e1) = lookup v e1) by auto.
      assert (L1: lookup v e1 = None) by (apply lookup_not_mem; auto).
      assert (L2: lookup v e2 = None) by (apply lookup_not_mem; auto).
      rewrite L12, L21, L1, L2. reflexivity.
  Qed.

  (* needed? *)
  Lemma env_comm2 : forall (e1 e2 e12 : env),
    e1 & e2 = Some e12 -> exists e21,
      e2 & e1 = Some e21 /\
      forall v, lookup v e12 = lookup v e21.
  Proof.
    intros.
    assert (D12: disjoint e1 e2 = true) by
      (apply disjoint_iff; exists e12; assumption).
    assert (D21: disjoint e2 e1 = true) by
      (rewrite disjoint_sym; assumption).
    assert (G: forall v, lookup v (e1 ++ e2) = lookup v (e2 ++ e1)).
      apply env_comm. constructor. assumption.
    exists (e2 ++ e1). split.
      apply disjoint_true in D21; assumption.
      apply disjoint_true in D12.
      rewrite D12 in H; inversion H; assumption.
  Qed.

(*
  Lemma env_comm : forall (e1 e2 e12 : env),
    disjoint e1 e2 = true -> e1 ++ e2 == e2 ++ e1.
  Proof.
    intros. rename H into D12.
    assert (D21: disjoint e2 e1 = true) by
      (rewrite disjoint_sym; assumption).
    assert (D12' := D12).
    apply disjoint_true in D12. apply disjoint_true in D21.
    destruct (e2 & e1) as [e21|] eqn:E21; try inversion D21.
    (* Prove e1 ++ e2 == e2 ++ e1 *)
    intro.
    destruct (bmem v e1) eqn:M1; destruct (bmem v e2) eqn:M2; elim_bmems.
    Case "v in e1, e2".
      assert (C: disjoint e1 e2 = false).
        apply disjoint_overlap with (v:=v); auto.
      rewrite D12' in C; inversion C.
    Case "v in e1, not in e2".
      assert (L1: lookup v (e1 ++ e2) = lookup v e1) by auto.
      assert (L2: lookup v (e2 ++ e1) = lookup v e1) by auto.
      rewrite L1; rewrite L2; reflexivity.
    Case "v in e2, not in e1".
      assert (L1: lookup v (e1 ++ e2) = lookup v e2) by auto.
      assert (L2: lookup v (e2 ++ e1) = lookup v e2) by auto.
      rewrite L1; rewrite L2; reflexivity.
    Case "v not in e1, e2".
      assert (L12: lookup v (e1 ++ e2) = lookup v e2) by auto.
      assert (L21: lookup v (e2 ++ e1) = lookup v e1) by auto.
      assert (L1: lookup v e1 = None) by (apply lookup_not_mem; auto).
      assert (L2: lookup v e2 = None) by (apply lookup_not_mem; auto).
      rewrite L12, L21, L1, L2. reflexivity.
  Qed.

  (* needed? *)
  Lemma env_comm2 : forall (e1 e2 e12 : env),
    e1 & e2 = Some e12 -> exists e21, e2 & e1 = Some e21 /\ e12 == e21.
  Proof.
    intros.
    assert (D12: disjoint e1 e2 = true) by
      (apply disjoint_iff; exists e12; assumption).
    assert (D21: disjoint e2 e1 = true) by
      (rewrite disjoint_sym; assumption).
    assert (G: e1 ++ e2 == e2 ++ e1) by
      (apply env_comm in D12; assumption).
    exists (e2 ++ e1). split.
      apply disjoint_true in D21; assumption.
      apply disjoint_true in D12.
      rewrite D12 in H; inversion H; assumption.
  Qed.
*)
End ENV.