Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Cases.

Definition var := nat.
Definition id := nat.
Definition beq_var := beq_nat.
Definition beq_id := beq_nat.

Unset Elimination Schemes.
Inductive term :=
| tvar : var -> term
| node : id -> list term -> term.
Set Elimination Schemes.

Fixpoint fvar (v : var) (t : term) : bool :=
  match t with
    | tvar v' => beq_var v v'
    | node _ ts =>
      (fix fvars (ts : list term) : bool :=
        match ts with
          | nil => false
          | t :: ts => fvar v t || fvars ts
        end) ts
  end.

Definition closed (t : term) : Prop :=
  forall (v : var), fvar v t = false.

(* Term Induction *)

Definition term_rect := fun
  (P : term -> Type)
  (h : forall (v : var), P (tvar v))
  (g : forall (n : id), P (node n nil))
  (f : forall (n : id) (t : term) (ts : list term),
    P t -> P (node n ts) -> P (node n (t :: ts)))
  =>
  fix term_rec (t : term) : P t :=
  match t return P t with
    | tvar v => h v
    | node n ts =>
      ((fix terms_rec (ts : list term) : P (node n ts) :=
        match ts with
          | nil => g n
          | t :: ts => f n t ts (term_rec t) (terms_rec ts)
        end) ts)
  end.

Definition term_ind := fun
  (P : term -> Prop)
  (h : forall (v : var), P (tvar v))
  (g : forall (n : id), P (node n nil))
  (f : forall (n : id) (t : term) (ts : list term),
    P t -> P (node n ts) -> P (node n (t :: ts)))
  => term_rect P h g f.

Definition term_rec := fun
  (P : term -> Set)
  (h : forall (v : var), P (tvar v))
  (g : forall (n : id), P (node n nil))
  (f : forall (n : id) (t : term) (ts : list term),
    P t -> P (node n ts) -> P (node n (t :: ts)))
  => term_rect P h g f.

(* Lemmas *)

Lemma beq_var_refl : forall (x : var),
  beq_var x x = true.
Proof. intro. rewrite <- beq_nat_refl. reflexivity. Qed.
Hint Resolve beq_var_refl.

Lemma beq_var_sym : forall (x y : var),
  beq_var x y = beq_var y x.
Proof. exact NPeano.Nat.eqb_sym. Qed.

Lemma beq_var_trans : forall (x y z : var),
  beq_var x y = true -> beq_var y z = true -> beq_var x z = true.
Proof.
  intros. unfold beq_var in *.
  apply beq_nat_true in H. rewrite H. exact H0.
Qed.

Lemma beq_var_true : forall x y : var, beq_var x y = true -> x = y.
Proof. intros. apply beq_nat_true. assumption. Qed.

Lemma beq_id_refl : forall (n : id), beq_id n n = true.
Proof. intros. rewrite (beq_nat_refl n). reflexivity. Qed.
Hint Resolve beq_id_refl.

Lemma beq_id_true : forall x y : id, beq_id x y = true -> x = y.
Proof. intros. apply beq_nat_true. assumption. Qed.
