Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.
Require Import Cases.
Require Import Term.
Require Import Env.

Module ValueImpl <: VALUE.
  Definition val := term.
End ValueImpl.

Module VarImpl <: VARIABLE.
  Definition var := var.
  Definition beq_var := beq_var.

  Definition beq_var_refl := beq_var_refl.
  Definition beq_var_sym := beq_var_sym.
  Definition beq_var_trans := beq_var_trans.
End VarImpl.

Module StdEnv := ENV(ValueImpl)(VarImpl).
Import StdEnv.

Definition try_lookup (v : var) (e : env) : term :=
  match lookup v e with
    | None => tvar v
    | Some t => t
  end.

Fixpoint subs (e : env) (t : term) : term :=
  match t with
    | tvar v => try_lookup v e
    | node n ts => node n (map (subs e) ts)
  end.

Notation "e * p" := (subs e p).

Definition env_eqv (e1 e2 : env) :=
  forall (v : var), try_lookup v e1 = try_lookup v e2.


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


Lemma lookup_eqv : forall (v : var) (e1 e2 : env),
  lookup v e1 = lookup v e2 -> try_lookup v e1 = try_lookup v e2.
Proof.
  intros. unfold try_lookup. rewrite H. reflexivity.
Qed.
Hint Resolve lookup_eqv.

Lemma env_eqv_subs : forall (e1 e2 : env) (t : term),
  e1 == e2 -> e1 * t = e2 * t.
Proof.
  intros. induction t.
  Case "var v". simpl. unfold env_eqv in H.
    rewrite H. reflexivity.
  Case "node n nil". reflexivity.
  Case "node n (t :: ts)". simpl. rewrite IHt.
  inversion IHt0. rewrite H1. reflexivity.
Qed.

Lemma subs_mtEnv : forall (t : term), mtEnv * t = t.
Proof.
  intros. induction t; try reflexivity.
  Case "node n (t :: ts)". inversion IHt0.
    simpl. rewrite IHt. rewrite H0. rewrite H0. reflexivity.
Qed.

Lemma subs_cons : forall e n t ts,
  e * node n (t :: ts) = node n (e * t :: map (subs e) ts).
Proof. auto. Qed.

Lemma try_lookup_not_mem : forall (v : var) (e : env),
  mem v e = false -> try_lookup v e = tvar v.
Proof.
  intros. assert (G : lookup v e = None).
    apply lookup_not_mem. exact H.
  unfold try_lookup. rewrite G. reflexivity.
Qed.
Hint Resolve try_lookup_not_mem.


Fixpoint compose (e1 e2 : env) : env :=
  match e2 with
    | mtEnv => e1
    | bind v t e2 => bind v (e1 * t) (compose e1 e2)
  end.

Lemma compose_mtEnv_l : forall e, compose mtEnv e = e.
Proof.
  intros. induction e; try reflexivity.
  simpl. rewrite IHe. rewrite subs_mtEnv. reflexivity.
Qed.

Add Parametric Morphism : subs with signature (equiv ==> eq ==> eq) as Subs_morph.
Proof.
  intros. apply env_eqv_subs. assumption.
Qed.

Lemma compose_subs_eq : forall e1 e2 t,
  e1 * (e2 * t) = (compose e1 e2) * t.
Proof.
  intros.
  induction t.
  Case "t = var v".
    simpl. induction e2 as [|v2 t2 e2].
    SCase "e2 = mtEnv".
      reflexivity.
    SCase "e2 = bind v2 t2 e2".
      simpl. unfold try_lookup, lookup.
      destruct (VarImpl.beq_var v v2); auto.
  Case "t = node nil".
    reflexivity.
  Case "t = node n (t::ts)".
    simpl in *. rewrite IHt. inversion IHt0.
    rewrite H0. reflexivity.
Qed.

Lemma subs_lookup_eqv : forall a b,
  a == b <-> forall t, a * t = b * t.
Proof.
  intros. simpl. unfold env_eqv.
  split; intros.
  Case "a == b -> at = bt".
    induction t; auto.
    SCase "t = tvar v".
      simpl. apply H.
    SCase "t = node n (t::ts)".
      simpl. rewrite IHt. simpl in IHt0. inversion IHt0. rewrite H1.
      reflexivity.
  Case "at = bt -> a == b".
    specialize H with (tvar v). simpl in H. exact H.
  Qed.
