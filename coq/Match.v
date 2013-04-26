Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Cases.
Require Import Patt.
Require Import Subs.
Require Import Util.
Import StdEnv.

Fixpoint pmatch (p : patt) (t : term) : option env :=
  let pmatches := fix pmatches (ps : list patt) (ts : list term)
    : option env :=
      match (ts, ps) with
        | (nil, nil) => Some mtEnv
        | (nil, _) => None
        | (_, nil) => None
        | (t :: ts, p :: ps) =>
          e1 <- pmatch p t;
          e2 <- pmatches ps ts;
          compose_env e1 e2
      end in
  match p with
    | pvar v => Some (bind v t mtEnv)
    | pnode n ps =>
      match t with
        | tnode n' ts =>
          if negb (beq_nid n n')
            then None
            else pmatches ps ts
      end
  end.

Notation "t / p" := (pmatch p t).

(*
Lemma fvar_pmatch : forall (v : vid) (t : term) (p : patt) (e : env),
  t / p = Some e -> fvar v 
*)

Definition subpattern (p q : patt) : Prop :=
  exists (e : env), e * p = q.

Notation "p <= q" := (subpattern p q).

Lemma subpattern_refl : forall (p : patt), p <= p.
Proof.
  intros. unfold subpattern. exists mtEnv. apply mtEnv_subs_l.
Qed.

Lemma pmatch_subs : forall (t : term) (p : patt) (e : env),
  t / p = Some e -> e * p = term_to_patt t.
Proof.
