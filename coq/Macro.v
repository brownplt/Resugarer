Require Import Term.
Require Import Subs.
Require Import Match.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.
Import StdEnv.

Inductive simple_macro :=
| smacro : term -> term -> simple_macro.

Fixpoint sexpand m t : option term :=
  match m with
    | smacro p q =>
      match t / p with
        | None => None
        | Some e => Some (e * q)
      end
  end.

Fixpoint sunexpand m s t : option term :=
  match m with
    | smacro p q =>
      match t / q with
        | None => None
        | Some e1 =>
          match s / p with
            | None => None
            | Some e2 => Some (e2 * (e1 * p))
          end
      end
  end.

(* Unproven! *)

Lemma simple_lens : forall m t t',
  closed t ->
  sexpand m t = Some t' ->
  sunexpand m t t' = Some t.
Proof.
  intros. destruct m as [p q].
  simpl in *. destruct (t / p) as [t_p|] eqn:TP; inversion_clear H0.
  destruct (t_p * q / q) eqn:TPQ.
  assert (E: e == t_p).
    apply subs_tmatch_eq in TPQ. symmetry; assumption.
    admit. (* fvars! *)
  assert (EP: e * p = t).
    rewrite E. apply tmatch_subs_eq. assumption.
  rewrite EP. f_equal. apply closed_subs; assumption.
  admit. (* well-formedness! *)
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
