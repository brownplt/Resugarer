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

Definition try_lookup v a :=
  match lookup v a with
    | None => tvar v
    | Some p => p
  end.

Fixpoint subs a p : term :=
  match p with
    | tvar v => try_lookup v a
    | const c => const c
    | empty => empty
    | p :: ps => (subs a p) :: (subs a ps)
  end.

Notation "a * p" := (subs a p).

Definition env_eqv a b :=
  forall (v : var), try_lookup v a = try_lookup v b.


Lemma env_eqv_refl : forall a, env_eqv a a.
Proof. unfold env_eqv. reflexivity. Qed.
Lemma env_eqv_sym : forall a b, env_eqv a b -> env_eqv b a.
Proof. unfold env_eqv. intros. symmetry; auto. Qed.
Lemma env_eqv_trans : forall a b c, env_eqv a b -> env_eqv b c -> env_eqv a c.
Proof. unfold env_eqv. intros. rewrite H; auto. Qed.

Add Relation env env_eqv
  reflexivity proved by env_eqv_refl
  symmetry proved by env_eqv_sym
  transitivity proved by env_eqv_trans
    as Env_eqv.

Instance env_eqv_Setoid : Setoid env :=
  {equiv := env_eqv; setoid_equiv := Env_eqv}.


Lemma lookup_eqv : forall v a b,
  lookup v a = lookup v b -> try_lookup v a = try_lookup v b.
Proof.
  intros. unfold try_lookup. rewrite H. reflexivity.
Qed.
Hint Resolve lookup_eqv.

Lemma env_eqv_subs : forall a b p,
  a == b -> a * p = b * p.
Proof.
  intros. induction p; auto.
  Case "var v". simpl. unfold env_eqv in H.
    rewrite H. reflexivity.
  Case "p1 :: p2".
    simpl. rewrite IHp1. rewrite IHp2. reflexivity.
Qed.

Lemma subs_mtEnv : forall p, mtEnv * p = p.
Proof.
  intros. induction p; try reflexivity.
  Case "p1 :: p2".
    simpl. rewrite IHp1. rewrite IHp2. reflexivity.
Qed.

Lemma try_lookup_not_mem : forall v a,
  mem v a = false -> try_lookup v a = tvar v.
Proof.
  intros. assert (G : lookup v a = None).
    apply lookup_not_mem. exact H.
  unfold try_lookup. rewrite G. reflexivity.
Qed.
Hint Resolve try_lookup_not_mem.

Fixpoint compose (a b : env) : env :=
  match b with
    | mtEnv => a
    | bind v t b => bind v (a * t) (compose a b)
  end.

Lemma compose_mtEnv_l : forall a, compose mtEnv a = a.
Proof.
  intros. induction a; try reflexivity.
  simpl. rewrite IHa. rewrite subs_mtEnv. reflexivity.
Qed.

Add Parametric Morphism : subs with signature (equiv ==> eq ==> eq) as Subs_morph.
Proof.
  intros. apply env_eqv_subs. assumption.
Qed.

Lemma compose_subs_eq : forall a b p,
  a * (b * p) = (compose a b) * p.
Proof.
  intros.
  induction p; auto.
  Case "t = var v".
    simpl. induction b as [|v2 p2 b].
    SCase "b = mtEnv".
      reflexivity.
    SCase "b = bind v2 p2 b".
      simpl. unfold try_lookup, lookup.
      destruct (VarImpl.beq_var v v2); auto.
  Case "t = p1 :: p2".
    simpl. rewrite IHp1, IHp2. reflexivity.
Qed.

Lemma subs_lookup_eqv : forall a b,
  a == b <-> forall p, a * p = b * p.
Proof.
  intros. simpl. unfold env_eqv.
  split; intros.
  Case "a == b -> at = bt".
    induction p; auto.
    SCase "t = tvar v".
      simpl. apply H.
    SCase "t = p1 :: p2".
      simpl. rewrite IHp1, IHp2. reflexivity.
  Case "at = bt -> a == b".
    specialize H with (tvar v). simpl in H. exact H.
Qed.
