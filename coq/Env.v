Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Cases.

Module Type VALUE.
  Parameter val : Type.
End VALUE.

Module Type VARIABLE.
  Parameter var : Type.
  Parameter beq_var : var -> var -> bool.

  Parameter beq_var_refl : forall (v : var),
    beq_var v v = true.
  Parameter beq_var_sym : forall (x y : var),
    beq_var x y = beq_var y x.
  Parameter beq_var_trans : forall (x y z : var),
    beq_var x y = true -> beq_var y z = true -> beq_var x z = true.
End VARIABLE.

Module ENV (Import Value : VALUE) (Import Var : VARIABLE).

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

  Definition mem (v : var) (e : env) : bool :=
    match lookup v e with
      | None => false
      | Some _ => true
    end.

  Add Parametric Morphism : lookup with signature (equiv ==> eq ==> eq) as Lookup_beq_var.
  Proof.
    intros. induction y0; auto.
    simpl. destruct (beq_var x v) eqn:xv; destruct (beq_var y v) eqn:yv;
    try change (x == v) in xv; try change (y == v) in yv; try rewrite <- Bool.not_true_iff_false in *;
    try change (y =/= v) in yv; try change (x =/= v) in xv; auto. 
    rewrite <- xv in yv.
    symmetry in H; contradiction. rewrite <- yv in xv; contradiction.
  Qed.

  Add Parametric Morphism : mem with signature (equiv ==> eq ==> eq) as mem_beq_var.
  Proof.
    unfold mem. intros. rewrite H. reflexivity.
  Qed.


  Fixpoint disjoint (e1 e2 : env) : bool :=
    match e1 with
      | mtEnv => true
      | bind v _ e1 => negb (mem v e2) && disjoint e1 e2
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

  Lemma mem_mtEnv : forall (v : var), mem v mtEnv = false.
  Proof. intros. unfold mem. simpl. reflexivity. Qed.

  Lemma mem_bind : forall (v v' : var) (t : val) (e : env),
    mem v e = true -> mem v (bind v' t e) = true.
  Proof.
    intros.
    unfold mem in H. unfold mem.
    unfold lookup in H. unfold lookup.
    destruct (beq_var v v').
      reflexivity.
      exact H.
  Qed.

  Lemma mem_bind_same : forall (v v' : var) (t : val) (e : env),
    v == v' -> mem v (bind v' t e) = true.
  Proof.
    intros. rewrite H. unfold mem. simpl. rewrite beq_var_refl; auto.
  Qed.

  Lemma mem_bind_diff : forall (v v' : var) (t : val) (e : env),
    v =/= v' -> mem v (bind v' t e) = true -> mem v e = true.
  Proof.
    intros. unfold mem in *. simpl in H0.
    destruct (beq_var v v') eqn:vv'. contradiction. auto.
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
    disjoint (bind v t e1) e2 = negb (mem v e2) && disjoint e1 e2.
  Proof. auto. Qed.

  Lemma disjoint_bind_l : forall e1 v t e2,
    disjoint e1 (bind v t e2) = negb (mem v e1) && disjoint e1 e2.
  Proof.
    intros.
    induction e1 as [|v1 t1 e1].
    Case "e1 = mtEnv".
      reflexivity.
    Case "e1 = bind v1 t1 e1".
      simpl. rewrite IHe1.
      assert (L: forall u v t e,
        negb (mem u (bind v t e)) = negb (beq_var u v) && negb (mem u e)).
      intros. rewrite <- negb_orb.
        unfold mem, lookup.
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
    mem v e1 = true -> mem v e2 = true -> disjoint e1 e2 = false.
  Proof.
    intros. induction e1 as [|v1 t1 e1].
    Case "e1 = mtEnv". inversion H.
    Case "e1 = bind v1 t1 e1". simpl.
      destruct (mem v1 e2) eqn:M; try reflexivity.
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

  Lemma lookup_concat : forall v e1 e2,
    lookup v (e1 ++ e2) = if mem v e1 then lookup v e1 else lookup v e2.
  Proof.
    intros. generalize dependent e2. induction e1 as [ | v1 t1 e1].
    Case "e1 = mtEnv".
      intros. reflexivity.
    Case "e1 = bind v1 t1 e1".
      intros. simpl.
      unfold mem, lookup in *.
      destruct (beq_var v v1); auto.
  Qed.
  Hint Resolve lookup_concat.

  Lemma lookup_concat_mem : forall v e1 e2,
    mem v e1 = true -> lookup v (e1 ++ e2) = lookup v e1.
  Proof. intros. rewrite lookup_concat. rewrite H. reflexivity. Qed.
  Hint Resolve lookup_concat_mem.
  
  Lemma lookup_concat_not_mem : forall v e1 e2,
    mem v e1 = false -> lookup v (e1 ++ e2) = lookup v e2.
  Proof. intros. rewrite lookup_concat. rewrite H. reflexivity. Qed.
  Hint Resolve lookup_concat_not_mem.

  Lemma lookup_union : forall v a b c,
    a & b = Some c ->
    lookup v c = if mem v a then lookup v a else lookup v b.
  Proof.
    intros. unfold union in H.
    destruct (disjoint a b); inversion H.
    rewrite lookup_concat. reflexivity.
  Qed.

  Lemma lookup_not_mem : forall (v : var) (e : env),
    mem v e = false <-> lookup v e = None.
  Proof.
    intros; split. intros.
    destruct (lookup v e) eqn:ve; auto. unfold mem in H. unfold mem in H.
    rewrite ve in H. discriminate H.
    intro. unfold mem.
    destruct (lookup v e); [inversion H | reflexivity].
  Qed.
  Hint Resolve lookup_not_mem.

  Lemma lookup_mem : forall (v : var) (a : env),
    mem v a = true <-> exists b, lookup v a = Some b.
  Proof.
    intros. unfold mem. destruct (lookup v a).
    split; eauto.
    split; intros; inversion H; discriminate.
  Qed.

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
    mem v e1 = true -> mem v e2 = true -> e1 & e2 = None.
  Proof.
    intros. apply disjoint_false.
    apply disjoint_overlap with (v:=v); auto.
  Qed.
  
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
    destruct (mem v e1) eqn:M1; destruct (mem v e2) eqn:M2.
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

(* Compose *)


(* Composition *)

  Lemma lookup__mem : forall v e t,
    lookup v e = Some t -> mem v e = true.
  Proof. intros. unfold mem. rewrite H; auto. Qed.

  Lemma not_lookup__not_mem : forall v e,
    lookup v e = None -> mem v e = false.
  Proof. intros. unfold mem. rewrite H; auto. Qed.

  Lemma union_mem : forall v a b c,
    a & b = Some c ->
    mem v c = true -> mem v a = true \/ mem v b = true.
  Proof.
    intros.
    repeat (rewrite lookup_mem in *).
    inversion H0. destruct (lookup v a) as [t|] eqn:L.
      left. exists t. auto.
      right. rewrite <- lookup_not_mem in L.
        rewrite lookup_union with (a:=a) (b:=b) in H1.
        rewrite L in H1. rewrite H1. eauto. auto.
  Qed.

  Lemma union_mem_left : forall v a b c,
    a & b = Some c ->
    mem v a = true ->
    lookup v c = lookup v a.
  Proof.
    intros. rewrite lookup_union with (a:=a) (b:=b).
    rewrite H0. reflexivity. assumption.
  Qed.
  Hint Resolve union_mem_left.

  Lemma union_mem_right : forall v a b c,
    a & b = Some c ->
    mem v b = true ->
    lookup v c = lookup v b.
  Proof.
    intros. rewrite lookup_union with (a:=a) (b:=b); auto.
    destruct (mem v a) eqn:D; auto.
    rewrite union_overlap with (v:=v) in H; inversion H; auto.
  Qed.
  Hint Resolve union_mem_right.

End ENV.