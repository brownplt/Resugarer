Require Import Cases.
Require Import Term.
Require Import Subs.
Require Import Match.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.
Import StdEnv.

(* TODO: Relax to say (fvar v q -> fvar v p). *)
Definition fvars_subset (q p : term) :=
  forall v, fvar v q = true -> fvar v p = true.

Inductive simple_macro :=
| smacro (p q : term) : wf p = true -> wf q = true -> fvars_subset q p -> simple_macro.

Fixpoint sexpand m t : option term :=
  match m with
    | smacro p q _ _ _ =>
      match t / p with
        | None => None
        | Some e => Some (e * q)
      end
  end.

Fixpoint sunexpand m s t : option term :=
  match m with
    | smacro p q _ _ _ =>
      match t / q with
        | None => None
        | Some e1 =>
          match s / p with
            | None => None
            | Some e2 => Some (e2 * (e1 * p))
          end
      end
  end.

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

Lemma simple_lens_1 : forall m t t',
  closed t ->
  sexpand m t = Some t' ->
  sunexpand m t t' = Some t.
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

Lemma simple_lens_2 : forall m s t t',
  closed t ->
  sunexpand m s t = Some t' ->
  sexpand m t' = Some t.
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
