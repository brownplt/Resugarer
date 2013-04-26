Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Cases.

(*
Definition var := nat.
Definition beq_var := beq_nat.

Lemma beq_var_refl : forall (v : var), beq_var v v = true.
Proof. intros. rewrite (beq_nat_refl v). reflexivity. Qed.

Lemma beq_var_true : forall x y : var, beq_var x y = true -> x = y.
Proof. intros. apply beq_nat_true. assumption. Qed.
*)

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

  Fixpoint insert_binding (v : var) (t : val) (e : env) : option env :=
    match e with
      | mtEnv => Some (bind v t mtEnv)
      | bind v' t' e' =>
        if beq_var v v'
          then None
          else match insert_binding v t e' with
                 | None => None
                 | Some e' => Some (bind v' t' e')
               end
    end.

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

  Definition env_eqv (e1 e2 : env) :=
    forall (v : var), lookup v e1 = lookup v e2.

  Notation "e1 ~= e2" := (env_eqv e1 e2) (at level 40).

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
    beq_var v v' = true -> mem v (bind v' t e).
  Proof.
    intros. unfold mem. unfold bmem. unfold lookup.
    rewrite H. reflexivity.
  Qed.

  Lemma mem_bind_diff : forall (v v' : var) (t : val) (e : env),
    beq_var v v' = false -> mem v (bind v' t e) -> mem v e.
  Proof.
    intros. unfold mem in *. unfold bmem in *. unfold lookup in *.
    rewrite H in H0. exact H0.
  Qed.

  Lemma mem_bind_same' : forall (v : var) (t : val) (e : env),
    mem v (bind v t e).
  Proof.
    intros. unfold mem. unfold bmem. simpl.
    rewrite beq_var_refl. reflexivity.
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

  Lemma lookup_bind : forall (v : var) (t : val) (e : env),
    lookup v (bind v t e) = Some t.
  Proof.
    intros. unfold lookup.
    rewrite beq_var_refl. reflexivity.
  Qed.

  Lemma lookup_bind_same : forall (v v' : var) (t : val) (e : env),
    beq_var v v' = true -> lookup v (bind v' t e) = Some t.
  Proof.
    intros. unfold lookup.
    rewrite H. reflexivity.
  Qed.

  Lemma lookup_bind_diff : forall (v v' : var) (t : val) (e : env),
    beq_var v v' = false -> lookup v (bind v' t e) = lookup v e.
  Proof.
    intros. unfold lookup.
    rewrite H. reflexivity.
  Qed.

  Lemma eqv_refl : forall (e : env), e ~= e.
    Proof. intros. unfold "_ ~= _". reflexivity. Qed.


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
      SCase "v == v1".
        elim H. constructor.
      SCase "v /= v1".
        apply IHe1. exact H.
  Qed.

  Lemma lookup_mem : forall e v, (exists t, lookup v e = Some t) <-> mem v e.
  Proof. unfold mem. unfold bmem. intros; destruct (lookup v e) eqn:ve; auto.
    split; auto. intro; exists v0; auto.
    split; intro; auto. inversion H. inversion H0. inversion H.
  Qed.

  Lemma lookup_beq_var : forall e v1 v2, beq_var v1 v2 = true ->
    lookup v1 e = lookup v2 e.
  Proof.
    induction e; intros; auto. simpl.
    destruct (beq_var v1 v) eqn:v1v. destruct (beq_var v2 v) eqn:v2v.
    auto. rewrite beq_var_sym in H. assert (H' := beq_var_trans _ _ _ H v1v). 
    rewrite v2v in *. inversion H'.
    destruct (beq_var v2 v) eqn:v2v. 
    assert (H' := beq_var_trans _ _ _ H v2v). rewrite v1v in H'.
    inversion H'.
    apply IHe. auto.
  Qed.


  Lemma temp : forall v1 v2 v3, beq_var v1 v2 = true -> 
    beq_var v1 v3 = beq_var v2 v3.
  Proof.
    intros. destruct (beq_var v1 v3) eqn:v13. symmetry; apply beq_var_trans
    with v1; auto. rewrite beq_var_sym; auto.
    destruct (beq_var v2 v3) eqn:v23; auto.
    assert (H' := beq_var_trans v1 v2 v3 H v23). rewrite H' in v13;
    inversion v13.
  Qed. 

  Lemma concat_comm_equiv : forall e1 e2, 
    (exists e12, e1 & e2 = Some e12) -> (e1 ++ e2) ~= (e2 ++ e1).
  Proof.
    intros.
    induction e1; simpl. 
    Case "e1 = mtEnv". intro. 
    destruct (lookup v e2) eqn:ve2. apply lookup_concat_member with _
    _ mtEnv _ in ve2. symmetry; auto.
    induction e2. auto. simpl in *.
    destruct (beq_var v v0). inversion ve2. apply IHe2. 
    exists e2; auto. auto.
    Case "e1 <> mtEnv".
    inversion_clear H as (e12 & H1). simpl in H1.
    destruct (bmem v e2) eqn:ve2. inversion H1.
    intro. destruct (e1 & e2) eqn:e12'; try discriminate.
    assert (exists e12, Some e = Some e12) by (exists e; auto). 
    apply IHe1 in H. 
    induction e2. simpl in *. destruct (beq_var v1 v); auto.
    simpl in *. 
    assert (beq_var v v2 = false). unfold bmem in ve2.
    simpl in ve2. destruct (beq_var v v2); auto.
    destruct (beq_var v1 v) eqn:v1v.
    destruct (beq_var v1 v2) eqn:v1v2. 
    apply beq_var_trans with v _ _ in v1v2. rewrite H0 in v1v2;
    inversion v1v2. rewrite <- v1v; apply beq_var_sym.
    assert (~ mem v1 e2). intro. unfold mem in H2. 
    unfold bmem in ve2. unfold lookup in ve2. rewrite H0 in ve2. 
    fold lookup in ve2. destruct (lookup v e2) eqn:ve2'. inversion ve2.
    apply bmem_true in H2. rewrite <- lookup_mem in H2. 
    inversion H2. rewrite lookup_beq_var with _ _ v in H3. 
    rewrite ve2' in H3. inversion H3. auto.
    apply lookup_concat_not_member with _ _ (bind v v0 e1) in
    H2. rewrite H2.
    simpl. rewrite v1v. auto.
    destruct (beq_var v1 v2) eqn:v1v2.


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
    intros. unfold compose_env in H. fold compose_env in H.
    destruct (bmem v e2).
    Case "true". inversion H.
    Case "false". destruct (e1 & e2).
    SCase "Some e". exists e. split.
      reflexivity.
      inversion H. reflexivity.
    SCase "None". inversion H.
  Qed.

  Lemma beq_var_mem : forall (v1 v2 : var) (e : env),
    beq_var v1 v2 = true -> (mem v1 e <-> mem v2 e).
  Proof.
    assert (F : forall (v1 v2 : var) (e : env),
      beq_var v1 v2 = true -> mem v1 e -> mem v2 e).
    Case "Prove one direction".
      intros.
      induction e as [|v t e].
      SCase "mtEnv".
        contradict H0. apply mem_mtEnv.
      SCase "bind v t e".
        destruct (beq_var v v1) eqn:V.
        SSCase "v == v1".
          apply mem_bind_same. rewrite beq_var_sym.
          apply beq_var_trans with (y := v1).
            exact V. exact H.
        SSCase "v /= v1".
          rewrite beq_var_sym in V.
          apply mem_bind_diff with (t := t) (e := e) in V.
            apply IHe in V. apply mem_bind. exact V.
          exact H0.
    Case "Given F". split.
      SCase "Foward".
        apply F. exact H.
      SCase "Reverse".
        rewrite beq_var_sym in H.
        apply F. exact H.
  Qed.

  Lemma compose_overlap : forall (e1 e2 : env) (v : var),
    mem v e1 -> mem v e2 -> e1 & e2 = None.
  Proof.
    intros.
    induction e1 as [ | v1 t e1].
    Case "mtEnv". simpl in *. inversion H.
    Case "bind v1 t1 e1". intros.
      unfold compose_env.
      destruct (bmem v1 e2) eqn:M; try reflexivity.
      fold compose_env.
      destruct (e1 & e2); try reflexivity.
      destruct (beq_var v v1) eqn:V.
    SCase "v == v1".
      apply beq_var_mem with (e := e2) in V.
      rewrite V in H0. unfold mem in H0.
      rewrite M in H0. inversion H0.
    SCase "v != v1".
      apply (mem_bind_diff v v1 t e1) in V.
      apply IHe1 in V; inversion V.
      exact H.
  Qed.

  Lemma compose_not_member : forall (e1 e2 e12 : env) (v : var),
    ~ (mem v e1) ->
    e1 & e2 = Some e12 ->
    lookup v e12 = lookup v e2.
  Proof.
    intros.
    generalize dependent e12.
    induction e1 as [ | v1 t e1]; intros.
    Case "mtEnv".
      simpl in H0. inversion H0. reflexivity.
    Case "bind v1 t e1". intros.
      apply bind_compose in H0.
      elim H0; intros; rename x into e; clear H0.
      inversion_clear H1. subst.
      destruct (beq_var v v1) eqn:V.
    SCase "v == v1".
      elim H. apply mem_bind_same. exact V.
    SCase "v /= v1".
      rewrite lookup_bind_diff.
      apply IHe1; clear IHe1.
      intro. elim H. apply mem_bind. exact H1.
      exact H0.
      exact V.
  Qed.
  Hint Resolve compose_not_member.

  Lemma lookup_mtEnv : forall (v : var), lookup v mtEnv = None.
  Proof. intros. compute. reflexivity. Qed.

  Lemma lookup_not_member : forall (v : var) (e : env),
    ~ (mem v e) -> lookup v e = None.
  Proof.
    intros.
    assert (e & mtEnv = Some e).
    rewrite compose_mtEnv_r. reflexivity.
    assert (lookup v e = lookup v mtEnv).
    apply compose_not_member with (e1 := e). exact H. exact H0.
    rewrite H1. rewrite lookup_mtEnv. reflexivity.
  Qed.
  Hint Resolve lookup_not_member.

  Lemma not_mem_compose : forall (v : var) (e1 e2 e12 : env),
    e1 & e2 = Some e12 ->
    ~ (mem v e1) ->
    ~ (mem v e2) ->
    ~ (mem v e12).
  Proof.
    intros.
    assert (L12 : lookup v e12 = lookup v e2); eauto.
    assert (L2 : lookup v e2 = None); auto.
    unfold mem, bmem. rewrite L12, L2. discriminate.
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
      destruct (beq_var v v1) eqn:V.
    SCase "v == v1".
      rewrite (lookup_bind_same v v1 t e1 V).
      rewrite (lookup_bind_same v v1 t e V).
      reflexivity.
    SCase "v /= v1".
      rewrite (lookup_bind_diff v v1 t e1 V).
      rewrite (lookup_bind_diff v v1 t e V).
      apply IHe1 with (e2 := e2).
      apply mem_bind_diff with (v' := v1) (t := t).
      exact V. exact H. exact H0.
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
      destruct (beq_var v v1) eqn:V.
    SCase "v == v1".
      assert (C : mem v (bind v1 t e1)).
      apply mem_bind_same. exact V.
      apply compose_overlap
        with (e1:=bind v1 t e1) (e2:=e2) (v:=v) in C.
      rewrite C in H0; inversion H0.
      exact H.
    SCase "v /= v1".
      apply bind_compose in H0.
      elim H0; intros; rename x into e; clear H0.
      inversion_clear H1; subst.
      rewrite lookup_bind_diff.
      apply IHe1. exact H. exact H0.
      exact V.
  Qed.
  Hint Resolve compose_lookup_r.

  Lemma env_comm : forall (e1 e2 e12 e21 : env),
    e1 & e2 = Some e12 -> e2 & e1 = Some e21 -> e12 ~= e21.
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
  
  Lemma env_join_concat : forall e1 e2, 
    (exists e12, e1 & e2 = Some e12) -> e1 & e2 = Some (e1 ++ e2).
  Proof.
    induction e1. intros. inversion H. simpl in H0. 
    inversion H0. subst. auto.
    intros. inversion H. simpl in H0. simpl.
    destruct (bmem v e2). inversion H0.
    destruct (e1 & e2) eqn:e12. inversion H0. 
    assert (exists x, e1 & e2 = Some x) by (exists e; auto). 
    apply IHe1 in H1. rewrite e12 in H1. inversion H1. 
    subst. auto. inversion H0.
  Qed.

  

  Lemma env_comm_2 : forall (e1 e2 e12 : env),
    e1 & e2 = Some e12 -> exists e21, e2 & e1 = Some e21 /\ e12 ~= e21.
  Proof.
    intros. assert (exists x, e1 & e2 = Some x) by (exists e12; auto).
    apply env_join_concat in H0. rewrite H in H0. inversion H0. subst.
    destruct (e2 & e1) eqn:e21. 
    assert (exists e, e2 & e1 = Some e) by (exists e; auto). 
    apply env_join_concat in H1. exists e. split; auto.

    induction e1.
    Case "mtEnv". intros e2 e12 H. simpl in *. inversion H; subst. exists e12. 
    induction e12; split; try intro; auto. rewrite compose_mtEnv_r; auto.
    Case "non-empty env".
    induction e2.
      SCase "mtEnv". intros. simpl in H.
      destruct (e1 & mtEnv) eqn:e1mt. apply IHe1 in e1mt. 
      simpl in e1mt. inversion_clear e1mt as (e1' & H0 & H1). inversion_clear H0.
      inversion_clear H. simpl. exists (bind v v0 e1'). split; auto.
      intro. unfold lookup; destruct (beq_var v1 v); auto. inversion H.
      SCase "non-empty env". intros.
      exists (bind v1 v2 e2 ++ bind v v0 e1). simpl.
      destruct (bmem v1 (bind v v0 e1)) eqn:v1v. simpl in H.
      destruct (beq_var v v1) eqn:vv1eq. 
      apply mem_bind_same with _ _ v2 e2 in vv1eq.
      unfold mem in vv1eq. rewrite vv1eq in H. inversion H.
      destruct (bmem v (bind v1 v2 e2)) eqn:vv1. inversion H.
      


 apply bind_compose in H.
      inversion_clear H as (e12' & H1 & H2). subst. apply IHe1 in H1.
      simpl.

      destruct (e1 & bind v1 v2 e2) eqn:e1bind. apply IHe1 in e1bind.
      inversion_clear e1bind as (e21' & H1 & H2). simpl in H1.
      destruct (bmem v1 e1) eqn:v1e1. inversion H1.
      destruct (e2 & e1) eqn:e2e1. inversion H1; subst.
      assert (bind v v0 e1 & e2 = Some (bind v v0 e0)).
      simpl. destruct (bmem v e2) eqn:ve2.
      apply bmem_true in ve2; apply mem_bind with _ v1 v2 _ in ve2. 
      apply bmem_false in vv1. contradiction.
      destruct (e1 & e2) eqn:e1e2. assert (Comm := env_comm _ _ _ _ e2e1 e1e2).
      
      
    simpl in *. destruct (bmem v e2) eqn:vmem. inversion H.
    destruct (e1 & e2) eqn:e12'. inversion H; subst. 
    apply IHe1 in e12'. inversion e12' as (e21 & H1 & H2).
    induction e2.
      SCase "e2 is empty".
      simpl in *. inversion H1; subst.
      exists (bind v v0 e21); split; auto. intro. simpl. 
      destruct (beq_var v1 v); auto.
      SCase "e2 is non-empty".
      clear H. assert (bmem v e2 = false). 
      apply bmem_false in vmem. 
      assert (~ mem v e2). intro; apply vmem; apply mem_bind; auto.
      unfold mem in H. apply Bool.not_true_is_false; auto.
      apply IHe2 in H. inversion H. inversion_clear H0.

 simpl. simpl in H1.
    destruct (bmem v1 e1) eqn:v1e1. inversion H1. 
    destruct (beq_var v v1) eqn:vv1eq. 
    apply mem_bind_same with _ _ v2 e2 in vv1eq. contradiction.
    unfold bmem. simpl. rewrite beq_var_sym in vv1eq. rewrite vv1eq.
    apply bmem_false in v1e1. apply lookup_not_member in v1e1. rewrite v1e1.
    rewrite H0. f_equal.

unfold mem in vmem.
    apply Bool.not_true_is_false in vmem.
    SearchAbout mem. destruct (bmem v1 (bind v v0 e1)) eqn:v1v.
    
    destruct (bmem v1 (bind v v0 e1)) eqn:vmem2. exfalso. apply
    vmem. unfold mem. unfold bmem. simpl.
    


End ENV.