Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Cases.

(*


!!! Replaced by Patt.v !!!


*)

Definition vid := nat.
Definition nid := nat.
Definition beq_vid := beq_nat.
Definition beq_nid := beq_nat.

Unset Elimination Schemes.
Inductive term :=
| var : vid -> term
| node : nid -> list term -> term. 
Set Elimination Schemes.

Definition term_ind := fun
  (P : term -> Prop)
  (h : forall (v : vid), P (var v))
  (g : forall (n : nid), P (node n nil))
  (f : forall (n : nid) (t : term) (ts : list term),
    P t -> P (node n ts) -> P (node n (t :: ts)))
  =>
  fix term_rec (t : term) : P t :=
    match t return P t with
      | var v => h v
      | node n ts =>
        ((fix terms_rec (ts : list term) : P (node n ts) :=
          match ts with
            | nil => g n
            | t :: ts => f n t ts (term_rec t) (terms_rec ts)
          end) ts)
    end.

(*
Definition term_ind_base := fun
  (P : term -> Prop)
  (h : forall (v : vid), P (var v))
  (f : forall (n : nid) (ts : list term), Forall P ts -> P (node n ts))
  =>
  fix term_rec (p : term) : P p :=
    match p return P p with
      | var v => h v
      | node n ps =>
      f n ps ((fix terms_rec (ps : list term) : Forall P ps :=
        match ps with
          | nil => Forall_nil P
          | p :: ps => Forall_cons p (term_rec p) (terms_rec ps)
        end) ps)
    end.

Lemma term_ind
  (P : term -> Prop)
  (h : forall (v : vid), P (var v))
  (g : forall (n : nid), P (node n nil))
  (f : forall (n : nid) (t : term) (ts : list term),
    P t -> P (node n ts) -> P (node n (t :: ts)))
  : forall (t : term), P t.
Proof.
  intros. induction t using term_ind_base.
  Case "var". exact (h v).
  Case "node n ts". clear h. induction ts.
    SCase "nil". exact (g n).
    SCase "t :: ts". apply f.
      inversion H; subst. exact H2.
      inversion H; subst. exact (IHts H3).
Qed.
*)



Lemma beq_nid_refl : forall (n : nid), beq_nid n n = true.
Proof. intros. unfold beq_nid. rewrite (beq_nat_refl n). reflexivity. Qed.

Lemma beq_vid_refl : forall (v : vid), beq_vid v v = true.
Proof. intros. unfold beq_vid. rewrite (beq_nat_refl v). reflexivity. Qed.

Lemma beq_vid_true : forall x y : vid, beq_vid x y = true -> x = y.
Proof. intros. unfold beq_nid. apply beq_nat_true. assumption. Qed.

(*

Inductive fixedTerm {r : Type} :=
| fixedVar : vid -> fixedTerm
| fixedNode : nid -> list r -> fixedTerm.

Fixpoint term_fixpoint {r : Type}
  (f : fixedTerm -> r) (t : term) : r :=
  match t with
    | var v => f (fixedVar v)
    | node n ts => f (fixedNode n (map (term_fixpoint f) ts))
  end.

Fixpoint termSize2 (t : term) : nat :=
  term_fixpoint (fun (t : fixedTerm) =>
    match t with
      | fixedVar _ => 0
      | fixedNode _ ns => fold_left plus ns 0
    end) t.

Fixpoint termSize1 (t : term) : nat :=
  match t with
    | var v => 0
    | node _ ts =>
      ((fix termSizes (ts : list term) :=
        match ts with
          | nil => 0
          | t :: ts => termSizes ts + termSize1 t
        end) ts)
  end.
*)