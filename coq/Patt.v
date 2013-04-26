Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Cases.

Definition vid := nat.
Definition nid := nat.
Definition beq_vid := beq_nat.
Definition beq_nid := beq_nat.

Unset Elimination Schemes.
Inductive patt :=
| pvar : vid -> patt
| pnode : nid -> list patt -> patt.
Set Elimination Schemes.

Unset Elimination Schemes.
Inductive term :=
| tnode : nid -> list term -> term.
Set Elimination Schemes.

Fixpoint fvar (v : vid) (p : patt) : Prop :=
  match p with
    | pvar v' => Is_true (beq_vid v v')
    | pnode _ ps =>
      (fix fvars (ps : list patt) : Prop :=
        match ps with
          | nil => False
          | p :: ps => fvar v p \/ fvars ps
        end) ps
  end.

(*
Inductive closed : patt -> Type :=
| closed_nil (n : nid) :
    closed (pnode n nil)
| closed_cons (n : nid) (p : patt) (ps : list patt) :
    closed p ->
    closed (pnode n ps) ->
    closed (pnode n (p :: ps)).
*)

Fixpoint closed (p : patt) : Prop :=
  match p with
    | pvar _ => False
    | pnode _ ps =>
      (fix closeds (ps : list patt) : Prop :=
         match ps with
           | nil => True
           | p :: ps => closed p /\ closeds ps
         end) ps
  end.

Definition patt_ind := fun
  (P : patt -> Prop)
  (h : forall (v : vid), P (pvar v))
  (g : forall (n : nid), P (pnode n nil))
  (f : forall (n : nid) (p : patt) (ps : list patt),
    P p -> P (pnode n ps) -> P (pnode n (p :: ps)))
  =>
  fix patt_rec (p : patt) : P p :=
    match p return P p with
      | pvar v => h v
      | pnode n ps =>
        ((fix patts_rec (ps : list patt) : P (pnode n ps) :=
          match ps with
            | nil => g n
            | p :: ps => f n p ps (patt_rec p) (patts_rec ps)
          end) ps)
    end.

Definition term_ind := fun
  (P : term -> Prop)
  (g : forall (n : nid), P (tnode n nil))
  (f : forall (n : nid) (t : term) (ts : list term),
    P t -> P (tnode n ts) -> P (tnode n (t :: ts)))
  =>
  fix term_rec (t : term) : P t :=
    match t return P t with
      | tnode n ts =>
        ((fix terms_rec (ts : list term) : P (tnode n ts) :=
          match ts with
            | nil => g n
            | t :: ts => f n t ts (term_rec t) (terms_rec ts)
          end) ts)
    end.

Fixpoint term_to_patt (t : term) : patt :=
  match t with
    | tnode n ts => pnode n (map term_to_patt ts)
  end.

Lemma term_to_patt_closed : forall (t : term),
  closed (term_to_patt t).
Proof.
  intros. induction t.
  Case "node n nil". constructor.
  Case "node n (t :: ts)".
    simpl in *. split. apply IHt. apply IHt0.
Qed.
  

Lemma beq_vid_refl : forall (v : vid), beq_vid v v = true.
Proof. intros. rewrite (beq_nat_refl v). reflexivity. Qed.

Lemma beq_vid_true : forall x y : vid, beq_vid x y = true -> x = y.
Proof. intros. apply beq_nat_true. assumption. Qed.


Lemma beq_nid_refl : forall (n : nid), beq_nid n n = true.
Proof. intros. rewrite (beq_nat_refl n). reflexivity. Qed.

Lemma beq_nid_true : forall x y : nid, beq_nid x y = true -> x = y.
Proof. intros. apply beq_nat_true. assumption. Qed.