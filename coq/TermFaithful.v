Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Cases.
Require Import Term.
Require Import Env.

Unset Elimination Schemes.
Inductive lterm :=
| lvar : var -> lterm
| lnode : id -> list lterm -> lterm.
Set Elimination Schemes.

Definition lterm_rect := fun
  (P : lterm -> Type)
  (h : forall (v : var), P (lvar v))
  (g : forall (n : id), P (lnode n nil))
  (f : forall (n : id) (t : lterm) (ts : list lterm),
    P t -> P (lnode n ts) -> P (lnode n (t :: ts)))
  =>
  fix lterm_rec (t : lterm) : P t :=
  match t return P t with
    | lvar v => h v
    | lnode n ts =>
      ((fix lterms_rec (ts : list lterm) : P (lnode n ts) :=
        match ts with
          | nil => g n
          | List.cons t ts => f n t ts (lterm_rec t) (lterms_rec ts)
        end) ts)
  end.

Definition lterm_ind := fun
  (P : lterm -> Prop)
  (h : forall (v : var), P (lvar v))
  (g : forall (n : id), P (lnode n nil))
  (f : forall (n : id) (t : lterm) (ts : list lterm),
    P t -> P (lnode n ts) -> P (lnode n (t :: ts)))
  => lterm_rect P h g f.

Definition lterm_rec := fun
  (P : lterm -> Set)
  (h : forall (v : var), P (lvar v))
  (g : forall (n : id), P (lnode n nil))
  (f : forall (n : id) (t : lterm) (ts : list lterm),
    P t -> P (lnode n ts) -> P (lnode n (t :: ts)))
  => lterm_rect P h g f.

Module Type VALUE.
  Parameter val : Type.
End VALUE.

(*
Module ENV (Import Value : VALUE).

  Inductive env :=
  | mtEnv : env
  | bind : var -> val -> env -> env.

  Fixpoint lookup (v : var) (e : env) : option val :=
    match e with
      | mtEnv => None
      | bind v' t e =>
        if beq_nat v v'
          then Some t
          else lookup v e
    end.
End ENV.
*)
Module ValueM <: VALUE.
  Definition val := lterm.
End ValueM.
Module VarM <: VARIABLE.
  Definition var := var.
  Definition beq_var := beq_var.
  Definition beq_var_refl := beq_var_refl.
  Definition beq_var_sym := beq_var_sym.
  Definition beq_var_trans := beq_var_trans.
End VarM.
Module E := ENV(ValueM)(VarM).
Import E.

Fixpoint subs (e : env) (t : lterm) : lterm :=
  match t with
    | lvar v =>
      match E.lookup v e with
        | None => lvar v
        | Some t => t
      end
    | lnode n ts => lnode n (map (subs e) ts)
  end.

Fixpoint convert (t : lterm) : term :=
  let converts := fix converts (ts : list lterm) : term :=
    match ts with
      | nil => empty
      | List.cons t ts => cons (convert t) (converts ts)
    end in
  match t with
    | lvar v => tvar v
    | lnode n ts => cons (const n) (converts ts)
  end.

Fixpoint subs' (e : env) (t : term) : term :=
  match t with
    | tvar v =>
      match lookup v e with
        | None => tvar v
        | Some t => convert t
      end
    | const c => const c
    | empty => empty
    | cons p t2 => cons (subs' e p) (subs' e t2)
  end.

Lemma subs_convert_comm : forall e t,
  convert (subs e t) = subs' e (convert t).
Proof.
  intros.
  induction t; auto.
  Case "lvar v".
    intros. simpl. destruct (lookup v e); auto.
  Case "node n t::ts".
    intros. simpl in *. rewrite IHt.
    inversion IHt0. rewrite H0. reflexivity.
Qed.

Lemma convert_cons : forall n n' p ps q qs,
  convert (lnode n (p :: ps)) = convert (lnode n' (q :: qs)) ->
  n = n' /\ convert p = convert q /\ convert (lnode n ps) = convert (lnode n qs).
Proof.
  intros. inversion H. simpl. rewrite H3. auto.
Qed.

Lemma convert_inj : forall p q,
  convert p = convert q -> p = q.
Proof.
  induction p as [v | n | n p ps IHp IHps]; intros.
  Case "lvar v".
    simpl in *. destruct q; inversion H. reflexivity.
  Case "node n nil".
    destruct q; inversion H. destruct l; [reflexivity | discriminate H2].
  Case "node n t::ts".
    induction q as [ | | n' q qs _ _]; try discriminate H.
    apply convert_cons in H. inversion_clear H as (N & P & Ps).
    apply IHp in P. apply IHps in Ps.
    rewrite N. rewrite P. inversion Ps. reflexivity.
Qed.

(* Since terms behave the same way under substitution as lterms,
   we might as well use terms in place of them for convenience. *)
Lemma conversion_is_faithful: forall (p q : lterm) (e : env),
  subs e p = subs e q <-> subs' e (convert p) = subs' e (convert q).
Proof.
  intros. repeat (rewrite <- subs_convert_comm). split; intros.
  Case "->".
    rewrite H. reflexivity.
  Case "<-".
    apply convert_inj in H. exact H.
Qed.