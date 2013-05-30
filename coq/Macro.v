Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Cases.
Require Import Util.
Require Import Term.
Require Import Subs.
Require Import Match.
Require Import Unify.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.
Import StdEnv.

(* TODO: Relax to say (fvar v q -> fvar v p). *)
Definition fvars_subset (q p : term) :=
  forall v, fvar v q = true -> fvar v p = true.

Inductive macro_branch :=
| branch (p q : term) : wf p = true -> wf q = true -> fvars_subset q p -> macro_branch.

Inductive raw_macro :=
| macro_mt : raw_macro
| macro_cons : macro_branch -> raw_macro -> raw_macro.

Fixpoint expand_branch m t : option term :=
  match m with
    | branch p q _ _ _ =>
      match t / p with
        | None => None
        | Some e => Some (e * q)
      end
  end.

Fixpoint unexpand_branch m s t : option term :=
  match m with
    | branch p q _ _ _ =>
      match t / q with
        | None => None
        | Some e1 =>
          match s / p with
            | None => None
            | Some e2 => Some (e2 * (e1 * p))
          end
      end
  end.

Fixpoint expand m t : option (nat * term) :=
  match m with
    | macro_mt => None
    | macro_cons b m =>
      match expand_branch b t with
        | None => match expand m t with
                    | None => None
                    | Some (n, t) => Some (S n, t)
                  end
        | Some t => Some (0, t)
      end
  end.

Fixpoint unexpand m s t n : option term :=
  match m with
    | macro_mt => None
    | macro_cons b m =>
      match n with
        | 0 => unexpand_branch b s t
        | S n => unexpand m s t n
      end
  end.

Definition disjoint_branches b b' :=
  match (b, b') with
    | (branch p _ _ _ _, branch p' _ _ _ _) =>
      ununifyable p p'
  end.

Fixpoint wfm m :=
  let wfb := fix wfb m := fun b =>
    match m with
      | macro_mt => true
      | macro_cons b' m =>
        disjoint_branches b b' && wfb m b
    end in
  match m with
    | macro_mt => true
    | macro_cons b m =>
      wfb m b && wfm m
  end.
Definition well_formed_macro m := wfm m.

(* Just for prettier proofs. *)
Fixpoint wfb m b :=
  match m with
    | macro_mt => true
    | macro_cons b' m =>
      disjoint_branches b b' && wfb m b
  end.


Lemma wfm_cons : forall b m,
  wfm (macro_cons b m) = true -> wfm m = true.
Proof.
  intros. simpl in H.
  destruct m; auto. simpl in *.
  rewrite andb_true_iff in H. inversion H. apply H1.
Qed.

Lemma wfm_cons_cons : forall b b' m,
  wfm (macro_cons b (macro_cons b' m)) = true ->
  wfm (macro_cons b m) = true.
Proof.
  intros.
  induction m as [ | b'' m]; auto.
  unfold wfm in *. fold wfb in *.
  break_andbs.
  repeat (rewrite andb_true_iff).
  repeat (split; try assumption).
Qed.

Lemma disjoint_branches_overlap : forall b b' t,
  disjoint_branches b b' = true ->
  (exists t', expand_branch b  t = Some t') ->
  (exists t', expand_branch b' t = Some t') ->
  False.
Proof.
  intros.
  destruct b as [p q wfp wfq fv].
  destruct b' as [p' q' wfp' wfq' fv'].
  unfold disjoint_branches in H.
  simpl in H0, H1. inversion_clear H0. inversion_clear H1.
  destruct (t / p) eqn:M; try discriminate.
  destruct (t / p') eqn:M'; try discriminate.
  apply tmatch_subs_eq in M. apply tmatch_subs_eq in M'.
  rewrite <- M' in M. apply tmatch__unify in M. inversion M as [r C].
  unfold ununifyable in H. destruct (p ^ p'); try discriminate.
Qed.

Lemma wfm_cons_cons_overlap : forall b b' m t,
  wfm (macro_cons b (macro_cons b' m)) = true ->
  (exists t', expand_branch b t = Some t') ->
  (exists t', expand_branch b' t = Some t') ->
  False.
Proof.
  intros.
  assert (D: disjoint_branches b b' = true).
    simpl in H. apply andb_prop in H; inversion H.
    apply andb_prop in H2; inversion H2; assumption.
  apply disjoint_branches_overlap with (b:=b) (b':=b') (t:=t);
    assumption.
Qed.

Lemma expand_cons : forall b m t n t',
  expand (macro_cons b m) t = Some (n, t') ->
  expand_branch b t = Some t' \/
    (expand_branch b t = None /\ expand m t = Some (pred n, t')).
Proof.
  intros. generalize dependent n.
  induction m as [ | b' m]; intros.
  Case "macro_mt".
    simpl in H. destruct (expand_branch b t); try discriminate.
    inversion H. left. reflexivity.
  Case "macro_cons".
    simpl in *. destruct (expand_branch b t).
    SCase "first branch".
      inversion H; subst. left. reflexivity.
    SCase "later branch".
      right. split. reflexivity.
      destruct (expand_branch b' t).
      SSCase "b' => Some (n, t')".
        inversion H. reflexivity.
      SSCase "b' => None".
        destruct (expand m t); try discriminate.
        SSSCase "m => Some (n, t')".
          destruct p. inversion H. reflexivity.
Qed.

Lemma wfm_expand : forall b m t t1 t2,
  wfm (macro_cons b m) = true ->
  expand_branch b t = Some t1 ->
  expand m t = Some t2 ->
  False.
Proof.
  intros. destruct t2 as [n2 t2]. generalize dependent n2.
  induction m; try discriminate; intros.
  (* m := (cons b (cons b' m)) *)
  rename m into b'. rename m0 into m.
  (* destruct t2 as [n t2]. *)
  apply expand_cons in H1; inversion_clear H1.
  Case "b' => Some t2".
    assert False.
      apply wfm_cons_cons_overlap with (b:=b) (b':=b') (m:=m) (t:=t);
        eauto.
    assumption.
  Case "b' => None, m => Some t2".
    inversion_clear H2 as [B' M].
    apply IHm with (n2:=pred n2).
      apply wfm_cons_cons in H. exact H.
      assumption.
Qed.

Definition env_closed a := forall v t,
  lookup v a = Some t -> closed t.

Lemma mtEnv_closed : env_closed mtEnv.
Proof.
  intros. unfold env_closed; intros. discriminate H.
Qed.

Lemma union_closed : forall a b c,
  a & b = Some c ->
  env_closed a ->
  env_closed b ->
  env_closed c.
Proof.
  unfold env_closed in *; intros a b c C Ha Hb v t L.
  rewrite lookup_union with (a:=a) (b:=b) in L; try assumption.
  destruct (mem v a).
    apply Ha in L; exact L.
    apply Hb in L; exact L.
Qed.

Definition closed_tmatch_defn t a := closed t -> env_closed a.
Lemma closed_tmatch_proof : forall t p a, t / p = Some a -> closed_tmatch_defn t a.
Proof.
  apply tmatch_ind; unfold closed_tmatch_defn; intros.
  Case "q = tvar".
    unfold env_closed; intros u t L.
    simpl in L. destruct (VarImpl.beq_var u v); inversion L.
    rewrite <- H1. exact H.
  Case "p, q = const n".
    apply mtEnv_closed.
  Case "p, q = empty".
    apply mtEnv_closed.
  Case "p, q = cons".
    apply closed_uncons in H4. inversion H4 as (Cp & Cps).
    apply H1 in Cp. apply H2 in Cps.
    apply union_closed with (a:=p_q) (b:=ps_qs); assumption.
Qed.
Lemma closed_tmatch : forall t p a,
  t / p = Some a -> closed t -> env_closed a.
Proof.
  intros.
  assert (closed_tmatch_defn t a) by
    (apply closed_tmatch_proof with (p:=p); assumption).
  unfold closed_tmatch_defn in H1. auto.
Qed.

Lemma lookup_compose : forall a b v,
  lookup v (compose a b) =
  match lookup v b with
    | None => lookup v a
    | Some t => Some (a * t)
  end.
Proof.
  intros.
  induction b as [ | u t b]; try reflexivity.
  simpl. destruct (VarImpl.beq_var v u); auto.
Qed.

Lemma try_lookup__subs : forall v a,
  try_lookup v a = a * (tvar v).
Proof. intros. reflexivity. Qed.

Lemma lens_helper : forall t p q t_p a,
  closed t ->
  (forall v, fvar v q = true -> fvar v p = true) ->
  t / p = Some t_p ->
  t_p * q / q = Some a ->
  compose t_p a == t_p.
Proof.
  intros. intro v.
  apply lookup_eqv.
  assert (E: forall v t', lookup v a = Some t' -> lookup v t_p = Some t').
    intros.
    apply lookup_subs_tmatch_eq with (ap_p:=a) (p:=q); intros; try assumption.
    rewrite <- fvar_mem with (p:=t) (q:=p); try assumption.
    apply H0. exact H4.
  assert (Ct_p := H1). apply closed_tmatch in Ct_p; auto.
  assert (Ca: env_closed a).
    unfold env_closed in *. intros va ta La.
    apply Ct_p with (v:=va). apply E. exact La.
  rewrite lookup_compose.
  destruct (lookup v a) as [t'|] eqn:L.
  Case "v in a".
    assert (Ct' := L). apply Ca in Ct'. rewrite closed_subs; try assumption.
    rewrite E with (t':=t'); try assumption. reflexivity.
  Case "v not in a".
    reflexivity.
Qed.

Lemma beq_var_false : forall u v,
  beq_var u v = false -> u =/= v.
Proof.
  intros u v H C.
  simpl in C. unfold beq_var_eq in C. unfold VarImpl.beq_var in C.
  rewrite H in C. discriminate C.
Qed.

Lemma mem_compose : forall v a b,
  mem v (compose a b) = true -> mem v a = true \/ mem v b = true.
Proof.
  intros.
  induction b; auto.
  destruct (beq_var v v0) eqn:EQ.
  Case "v == v0".
    rewrite mem_bind_same. right; reflexivity. apply EQ.
  Case "v =/= v0".
    simpl in H. apply mem_bind_diff in H.
    SCase "Main proof".
      apply IHb in H. inversion H.
      SSCase "v in a".
        left; assumption.
      SSCase "v in b".
        right. apply mem_bind_diff with (v':=v0) (t:=v1).
          apply beq_var_false; assumption.
        rewrite mem_bind; auto. rewrite mem_bind; auto.
    SCase "Side condition".
      apply beq_var_false; assumption.
Qed.

Lemma simple_lens_1 : forall m t t',
  closed t ->
  expand_branch m t = Some t' ->
  unexpand_branch m t t' = Some t.
Proof.
  intros m t t' C H.
  destruct m as [p q WFp WFq FV].
  simpl in *. destruct (t / p) as [t_p|] eqn:TP; inversion_clear H.
  destruct (t_p * q / q) eqn:TPQ.
  Case "Prove the equivalence".
    rewrite compose_subs_eq.
    assert (E: compose t_p e == t_p).
      apply lens_helper with (t:=t) (p:=p) (q:=q); assumption.
    rewrite E. rewrite tmatch_subs_eq with (p:=t); auto.
  Case "Contradiction : t_p * q / q exists".
    rewrite wf_tmatch_iff in WFq. inversion WFq.
    rewrite H in TPQ. discriminate TPQ.
Qed.

Lemma simple_lens_2 : forall m s t t',
  closed t ->
  unexpand_branch m s t = Some t' ->
  expand_branch m t' = Some t.
Proof.
  intros m s t t' C H.
  destruct m as [p q WFp WFq FV].
  simpl in *. destruct (t / q) as [t_q|] eqn:TQ; try discriminate.
  destruct (s / p) as [s_p|] eqn:SP; try discriminate.
  destruct (t' / p) eqn:TP.
  Case "Prove the equivalence".
    inversion H as [T'].
    rewrite compose_subs_eq in T'.
    rewrite <- T' in TP.
    apply subs_tmatch_eq in TP.
    rewrite <- TP.
    rewrite <- compose_subs_eq.
    assert (E1: t_q * q = t).
      apply tmatch_subs_eq; assumption.
    assert (E2: s_p * t = t).
      apply closed_subs; assumption.
    rewrite E1, E2. reflexivity.
    SCase "FV condition".
      intros v M. apply mem_compose in M. inversion M.
        erewrite fvar_mem; eauto.
        rewrite FV. reflexivity. erewrite fvar_mem; eauto.
  Case "Contradiction : t' / p exists".
    inversion H as [T'].
    rewrite compose_subs_eq in T'.
    rewrite <- T' in TP.
    apply wf__tmatch with (a := compose s_p t_q) in WFp.
    inversion WFp. rewrite H0 in TP. discriminate TP.
Qed.

Lemma lens_1 : forall m t n t',
  closed t ->
  expand m t = Some (n, t') ->
  unexpand m t t' n = Some t.
Proof.
  intros. generalize dependent n.
  induction m; intros.
  Case "no branches".
    discriminate H0.
  Case "some branches".
    simpl in *.
    destruct (expand_branch m t) eqn:B.
    SCase "first branch works".
      inversion H0. rewrite H3 in *.
      apply simple_lens_1; try assumption.
    SCase "first branch fails".
      destruct (expand m0 t).
      SSCase "rest of branches work".
        destruct p. inversion H0. subst.
        apply IHm. reflexivity.
      SSCase "rest of branches fail".
        inversion H0.
Qed.

Lemma lens_2 : forall m s t n t',
  closed t ->
  unexpand m s t n = Some t' ->
  well_formed_macro m = true ->
  expand m t' = Some (n, t).
Proof.
  intros. rename H1 into WFM. generalize dependent n.
  induction m as [ | b m].
  Case "no branches".
    intros; discriminate H0.
  Case "some branches".
    intros n E.
    simpl.
    destruct n.
    SCase "first branch".
      apply simple_lens_2 in E; try assumption.
      rewrite E. reflexivity.
    SCase "not first branch".
      assert (WFM' := WFM). apply wfm_cons in WFM'.
      apply IHm in E; try assumption. rewrite E.
      destruct (expand_branch b t') eqn:Eb; try reflexivity.
      SSCase "b => Some t0".
        apply wfm_expand with (m:=m) (t2:=(n,t)) in Eb; try assumption.
          elim Eb.
Qed.
