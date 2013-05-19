Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.


Definition var := nat.
Definition id := nat.
Definition beq_var := beq_nat.
Definition beq_id := beq_nat.

Inductive term :=
| tvar : var -> term
| const : id -> term
| empty : term
| cons : term -> term -> term.


Fixpoint fvar v p : bool :=
  match p with
    | tvar v' => beq_var v v'
    | const c => false
    | empty => false
    | cons p ps => fvar v p || fvar v ps
  end.

Definition closed p : Prop :=
  forall (v : var), fvar v p = false.

Lemma beq_var_refl : forall (x : var),
  beq_var x x = true.
Proof. intro. rewrite <- beq_nat_refl. reflexivity. Qed.
Hint Resolve beq_var_refl.

Lemma beq_var_sym : forall (x y : var),
  beq_var x y = beq_var y x.
Proof.
  induction x; induction y; auto.
  simpl. apply IHx.
Qed.

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