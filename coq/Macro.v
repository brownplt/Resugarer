Require Import Cases.
Require Import Term2.
Require Import Subs2.
Require Import Match2.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.
Import StdEnv.

(* TODO: Relax to say (fvar v q -> fvar v p). *)
Definition same_fvars (p q : term) :=
  forall v, fvar v p = fvar v q.

Inductive simple_macro :=
| smacro (p q : term) : wf p = true -> wf q = true -> same_fvars p q -> simple_macro.

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
    assert (E1: e == t_p).
      symmetry. apply subs_tmatch_eq with (p:=q).
      intros. rewrite <- fvar_mem with (p:=t) (q:=p) in H; try assumption.
      rewrite FV in H. exact H.
      assumption.
    assert (E2: t_p * p = t).
      apply tmatch_subs_eq; assumption.
    assert (E3: t_p * t = t).
      apply closed_subs; assumption.
    rewrite E1. rewrite E2. rewrite E3. reflexivity.
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
        rewrite FV. erewrite fvar_mem; eauto.
  Case "Contradiction : t' / p exists".
    inversion H as [T'].
    rewrite compose_subs_eq in T'.
    rewrite <- T' in TP.
    apply wf__tmatch with (a := compose s_p t_q) in WFp.
    inversion WFp. rewrite H0 in TP. discriminate TP.
Qed.




(* Scrap *)

Inductive expand {patt env : Type}
  {pmatch : Pmatch patt env}
  {subs : Subs patt env}
  {lensy : Lensy patt env pmatch subs}
  (m : @macro patt) (t : patt) (t' : option patt) (n : nat) :=
| expand_nil : m = mnil -> t' = None -> n = 0 ->
  expand m t t' n
| expand_car (p q : patt) (e : env) (m' : macro) :
  m = mcons p q m' -> pmatch t p = Some e -> t' = Some (subs e q) -> n = 0 ->
  expand m t t' n
| expand_cdr (p q : patt) (e : env) (m' : macro) (n' : nat) :
  m = mcons p q m' -> pmatch t p = None -> expand m' t t' n' -> n = S n' ->
  expand m t t' n.

Inductive unexpand {patt env : Type}
  {pmatch : Pmatch patt env}
  {subs : Subs patt env}
  {lensy : Lensy patt env pmatch subs}
  (m : @macro patt) (n : nat) (t : patt) (t' : option patt) :=
| unexpand_nil : m = mnil -> t' = None ->
  unexpand m t t'
| unexpand_car (p q : patt) (e : env) (m' : macro) :
  m = mcons p q m' -> pmatch t q = Some e -> t' = Some (subs e p) ->
  unexpand m t t'
| unexpand_cdr (p q : patt) (e : env) (m' : macro) :
  m = mcons p q m' -> pmatch t q = None -> unexpand m' t t' ->
  unexpand m t t'.

Theorem MacroLens : forall (m : macro) (t t' : patt),
  expand m t (Some t') -> 

Check expand_base.

| expand_rec : m = mcons p q _ -> (

Check foo.
