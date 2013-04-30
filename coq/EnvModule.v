Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
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

  Definition bmem (v : var) (e : env) : bool :=
    match lookup v e with
      | None => false
      | Some _ => true
    end.

  Add Parametric Morphism : bmem with signature (equiv ==> equiv ==> eq) as bmem_beq_var.
  Proof.
    unfold bmem. intros. rewrite H. rewrite H0. reflexivity.
  Qed.

  Definition mem (v : var) (e : env) : Prop :=
    bmem v e = true.

  Add Parametric Morphism : mem with signature (equiv ==> equiv ==> eq) as mem_beq_var.
  Proof.
    unfold mem; intros; rewrite H; rewrite H0; reflexivity.
  Qed.

(* Compose two environments. Fail if they overlap. *)
  Fixpoint compose_env (e1 e2 : env) {struct e1} : option env :=
    match e1 with
      | mtEnv => Some e2
      | bind v t e1 =>
        if bmem v e2
          then None
          else match compose_env e1 e2 with
                 | None => None
                 | Some e => Some (bind v t e)
               end
    end.

  (* Disjoint union *)
  Notation "x & y" := (compose_env x y) (at level 60).



  (* Juxtposition *)
  Fixpoint concat (e1 e2 : env) : env :=
    match e1 with
      | mtEnv => e2
      | bind v t e => bind v t (concat e e2)
    end.
  Notation "e1 ++ e2" := (concat e1 e2).

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

  Lemma lookup_bind_same : forall (v v' : var) (t : val) (e : env),
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


(*********************)
(*** Concat Lemmas ***)
(*********************)


  Lemma lookup_concat_member : forall (v : var) (e1 e2 : env) (x : val),
    lookup v e1 = Some x -> lookup v (e1 ++ e2) = Some x.
  Proof.
    intros. generalize dependent e2. induction e1 as [|v1 t1 e1].
    Case "mtEnv".
      simpl in H. inversion H.
    Case "bind v1 t1 e2".
      intros. simpl in *. destruct (beq_var v v1).
      SCase "v == v1". exact H.
      SCase "v /= v1". apply IHe1. exact H.
  Qed.

  Lemma lookup_concat_not_member : forall (v : var) (e1 e2 : env),
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

  Lemma lookup_mem : forall e v, (exists t, lookup v e = Some t) <-> mem v e.
  Proof. unfold mem. unfold bmem. intros; destruct (lookup v e) eqn:ve; auto.
    split; eauto. 
    split; intro; eauto. inversion H. inversion H0. inversion H.
  Qed.

  Lemma lookup_not_member : forall (v : var) (e : env),
    ~ (mem v e) <-> lookup v e = None.
  Proof.
    intros; split. intros.
    destruct (lookup v e) eqn:ve; auto. unfold mem in H. unfold bmem in H.
    rewrite ve in H. tauto.
    intro; intro. rewrite <- lookup_mem in H0. inversion H0.
    rewrite H1 in H. inversion H.
  Qed.

  Lemma concat_comm_equiv : forall e1 e2 e12, e1 & e2 = Some e12 -> (e1 ++ e2) == (e2 ++ e1).
  Proof.
    cut (forall e1 e2, (exists e12, e1 & e2 = Some e12) -> (e1 ++ e2) == (e2 ++ e1)).
    intros. assert (exists e, e1 & e2 = Some e) by (exists e12; auto). apply H; auto.
    intros.
    induction e1. 
    Case "e1 = mtEnv". simpl; intro. symmetry.
    destruct (lookup v e2) eqn:ve2. 
    apply lookup_concat_member with _ _ mtEnv _ in ve2; auto.
    apply lookup_concat_not_member. apply lookup_not_member. auto.
    Case "e1 <> mtEnv".
    inversion_clear H as (e12 & H1). simpl in H1.
    destruct (bmem v e2) eqn:ve2; try discriminate.
    destruct (e1 & e2) eqn:e12'; try discriminate. clear H1.
    assert (exists e12, Some e = Some e12) by (exists e; auto). 
    apply IHe1 in H. intro. simpl. rewrite H. 
    destruct (beq_var_eq_dec v1 v). repeat rewrite H0 in *. 
    rewrite lookup_concat_not_member. rewrite lookup_bind_same; reflexivity.
    apply bmem_false; auto.
    assert (beq_var v1 v = false) by (apply Bool.not_true_iff_false; auto).
    rewrite H1.
    destruct (lookup v1 e2) eqn:v1e2. 
    repeat erewrite lookup_concat_member; eauto.
    repeat (rewrite lookup_concat_not_member; simpl); try apply lookup_not_member; try rewrite H1; auto.
  Qed.


(**************************)
(*** Composition Lemmas ***)
(**************************)



  Lemma compose_mtEnv_l : forall (e : env), mtEnv & e = Some e.
  Proof. reflexivity. Qed.

  Lemma compose_mtEnv_r : forall (e : env), e & mtEnv = Some e.
  Proof.
    intros. induction e.
    Case "mtEnv". reflexivity.
    Case "bind v t e". simpl. rewrite IHe. reflexivity.
  Qed.

  Lemma bind_compose :
    forall (v : var) (t : val) (e1 e2 e12: env),
      (bind v t e1) & e2 = Some e12 ->
      exists e12', e1 & e2 = Some e12' /\ e12 = bind v t e12'.
  Proof.
    intros. simpl in H.
    destruct (bmem v e2).
    Case "true". inversion H.
    Case "false". destruct (e1 & e2); inversion H.
    SCase "Some e". exists e; split; auto.
  Qed.


  Lemma beq_var_mem : forall (v1 v2 : var) (e : env),
    v1 == v2 -> (mem v1 e <-> mem v2 e).
  Proof.
    intros. rewrite H. split; auto.
  Qed.

  Lemma compose_overlap : forall (e1 e2 : env) (v : var),
    mem v e1 -> mem v e2 -> e1 & e2 = None.
  Proof.
    intros.
    induction e1 as [ | v1 t e1].
    Case "mtEnv". simpl in *. inversion H.
    Case "bind v1 t1 e1". simpl.
      destruct (bmem v1 e2) eqn:M; try reflexivity. unfold mem in H0. 
      destruct (e1 & e2); try reflexivity.
      destruct (beq_var_eq_dec v v1).
    SCase "v == v1".
      repeat rewrite H1 in *. rewrite H0 in M; inversion M. 
    SCase "v != v1".
      apply (mem_bind_diff v v1 t e1 H1) in H. apply IHe1 in H. inversion H.
  Qed.

  Lemma compose_overlap_2 : forall e1 e2,
    e1 & e2 = None -> (exists v, mem v e1 /\ mem v e2).
  Proof.
    induction e1; intros. inversion H.
    simpl in H. destruct (bmem v e2) eqn:ve2.
    exists v. split; unfold mem; unfold bmem; simpl; try rewrite beq_var_refl; auto.
    destruct (e1 & e2) eqn:e12. inversion H. apply IHe1 in e12. inversion e12 as (x & H1 & H2). 
    exists x; split; auto. apply mem_bind; auto.
  Qed.

  Lemma compose_overlap_3 : forall e1 e2 e12,
    e1 & e2 = Some e12 -> ~ exists v, mem v e1 /\ mem v e2.
  Proof.
    intros. intro. inversion H0 as (v & H1 & H2). assert (H3 := compose_overlap _ _ _ H1 H2).
    inversion H. rewrite H3 in H5; inversion H5.
  Qed.

  Lemma compose_not_member : forall (e1 e2 e12 : env) (v : var),
    e1 & e2 = Some e12 ->
    ~ (mem v e1) ->
    lookup v e12 = lookup v e2.
  Proof.
    intros.
    generalize dependent e12.
    induction e1 as [ | v1 t e1]; intros.
    Case "mtEnv".
      simpl in H. inversion H. reflexivity.
    Case "bind v1 t e1".
      assert (~ mem v e1). intro; apply H0. apply mem_bind; auto.
      simpl in H. destruct (bmem v1 e2) eqn:v1e2; try discriminate.
      destruct (e1 & e2); try discriminate.
      inversion_clear H. simpl. destruct (beq_var v v1) eqn:vv1.
      unfold mem in H0. unfold bmem in H0. simpl in H0. rewrite vv1 in H0. tauto. 
      apply IHe1; auto.
  Qed.
  Hint Resolve compose_not_member.

  Lemma lookup_mtEnv : forall (v : var), lookup v mtEnv = None.
  Proof. intros. compute. reflexivity. Qed.

  Hint Resolve lookup_not_member.

  Lemma not_mem_compose : forall (v : var) (e1 e2 e12 : env),
    e1 & e2 = Some e12 ->
    ~ (mem v e1) ->
    ~ (mem v e2) ->
    ~ (mem v e12).
  Proof.
    intros.
    assert (L12 : lookup v e12 = lookup v e2); eauto.
    assert (L2 : lookup v e2 = None); apply lookup_not_member; auto.
    unfold mem, bmem. rewrite L12, L2. auto.
  Qed.
  Hint Resolve not_mem_compose.

  Lemma compose_lookup_l : forall (e1 e2 e12 : env) (v : var),
    mem v e1 ->
    e1 & e2 = Some e12 ->
    lookup v e12 = lookup v e1.
  Proof.
    intros.
    generalize dependent e2. generalize dependent e12.
    induction e1 as [ | v1 t e1].
    Case "mtEnv".
      apply mem_mtEnv in H. inversion H.
    Case "bind v1 t1 e1". intros.
      apply bind_compose in H0.
      elim H0; intros; rename x into e; clear H0.
      inversion_clear H1. subst.
      destruct (beq_var_eq_dec v v1).
    SCase "v == v1".
      repeat rewrite H1. repeat rewrite lookup_bind_same; reflexivity.
    SCase "v /= v1".
      repeat rewrite lookup_bind_diff; auto.
      apply IHe1 with (e2 := e2); auto.
      apply mem_bind_diff with (v' := v1) (t := t); auto. 
  Qed.
  Hint Resolve compose_lookup_l.

  Lemma compose_lookup_r : forall (e1 e2 e12 : env) (v : var),
    mem v e2 ->
    e1 & e2 = Some e12 ->
    lookup v e12 = lookup v e2.
  Proof.
    intros.
    generalize dependent e2. generalize dependent e12.
    induction e1 as [ | v1 t e1].
    Case "mtEnv". intros.
      inversion H0. reflexivity.
    Case "bind v1 t e1". intros.
      destruct (beq_var_eq_dec v v1).
    SCase "v == v1". 
      assert (C : mem v (bind v1 t e1)).
      apply mem_bind_same; auto.
      apply compose_overlap
        with (e1:=bind v1 t e1) (e2:=e2) (v:=v) in C; auto.
      rewrite C in H0; inversion H0.
    SCase "v /= v1".
      apply bind_compose in H0.
      inversion_clear H0 as (e & H2 & H3); subst.
      rewrite lookup_bind_diff; auto.
  Qed.
  Hint Resolve compose_lookup_r.

  Lemma env_comm : forall (e1 e2 e12 e21 : env),
    e1 & e2 = Some e12 -> e2 & e1 = Some e21 -> e12 == e21.
  Proof. 
    intros e1 e2 e12 e21 H12 H21 v.
    destruct (bmem v e1) eqn:M1; destruct (bmem v e2) eqn:M2;
      try apply bmem_true in M1; try apply bmem_true in M2.
    Case "v in e1, e2".
      assert (C : e1 & e2 = None).
      apply compose_overlap with (v := v). exact M1. exact M2.
      rewrite C in H12. inversion H12.
    Case "v in e1, not in e2".
      transitivity (lookup v e1). eauto. symmetry; eauto.
    Case "v in e2, not in e1".
      transitivity (lookup v e2). eauto. symmetry; eauto.
    Case "v not in e1, e2".
      apply bmem_false in M1.
      apply bmem_false in M2.
      assert (M12 : ~ mem v e12); eauto. apply lookup_not_member in M12.
      assert (M21 : ~ mem v e21); eauto. apply lookup_not_member in M21.
      rewrite M12, M21; reflexivity.
  Qed.
  
  Lemma env_join_concat : forall e1 e2 e12, 
    e1 & e2 = Some e12 -> e12 = e1 ++ e2.
  Proof.
    induction e1. intros. inversion H. subst; auto.
    intros. simpl in *.
    destruct (bmem v e2); try discriminate.
    destruct (e1 & e2) eqn:e12'.
    apply IHe1 in e12'. subst. inversion H; auto. inversion H.
  Qed.  

  Lemma env_comm_2 : forall (e1 e2 e12 : env),
    e1 & e2 = Some e12 -> exists e21, e2 & e1 = Some e21 /\ e12 == e21.
  Proof.
    intros. assert (H0 := H). assert (H1 := H).
    apply env_join_concat in H0. 
    apply concat_comm_equiv in H.
    destruct (e2 & e1) eqn:e21. 
    apply env_join_concat in e21. exists e. split; subst; auto. 
    apply compose_overlap_2 in e21. inversion e21 as (x & H2 & H3). assert (H' := compose_overlap _ _ _ H3 H2).
    rewrite H1 in H'. inversion H'.
  Qed.

End ENV.
