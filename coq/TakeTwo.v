Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Cases.
Require Import Util.
Require Import EnvModule.


Module Term.

  Definition var := nat.
  Definition beq_var := beq_nat.
  Definition id := nat.
  Definition beq_id := beq_nat.

  Lemma beq_var_refl : forall (x : var),
    beq_var x x = true.
  Proof. intro. rewrite <- beq_nat_refl. reflexivity. Qed.

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

  Lemma beq_id_true : forall x y : id, beq_id x y = true -> x = y.
  Proof. intros. apply beq_nat_true. assumption. Qed.

  Unset Elimination Schemes.
  Inductive term :=
  | tvar : var -> term
  | node : id -> list term -> term.
  Set Elimination Schemes.

  Module TermValue <: VALUE.
    Definition val := term.
    Definition var := var.
    Definition beq_var := beq_nat.
    Definition beq_var_refl := beq_var_refl.
    Definition beq_var_sym := beq_var_sym.
    Definition beq_var_trans := beq_var_trans.
  End TermValue.

  Module Env := ENV(TermValue).
  Import Env.

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

  Fixpoint subs (e : env) (t : term) : term :=
    match t with
      | tvar v =>
        match lookup v e with
          | None => tvar v
          | Some t => t
        end
      | node n ts =>
        node n (map (subs e) ts)
    end.

  Notation "e * t" := (subs e t).

  Fixpoint tmatch (q p : term) {struct q} : option env :=
    let tmatches := fix tmatches (ps qs : list term) {struct qs} : option env :=
      match (ps, qs) with
        | (nil, nil) => Some mtEnv
        | (nil, _) => None
        | (_, nil) => None
        | (p :: ps, q :: qs) =>
          e1 <- tmatch q p;
          e2 <- tmatches ps qs;
          e1 & e2
      end in
    match q with
      | tvar v => Some (bind v p mtEnv)
      | node n qs =>
        match p with
          | tvar _ => None
          | node n' ps =>
            if negb (beq_id n n')
              then None
              else tmatches ps qs
          end
    end.

  Notation "p / q" := (tmatch q p).


  Lemma fvar_head : forall (t : term) (ts : list term) (n : id) (v : var),
    fvar v t = true -> fvar v (node n (t :: ts)) = true.
  Proof.
    intros.
    unfold fvar. apply orb_true_iff. left. fold fvar.
    assumption.
  Qed.

  Lemma fvar_tail : forall (t : term) (ts : list term) (n : id) (v :var),
    fvar v (node n ts) = true -> fvar v (node n (t :: ts)) = true.
  Proof.
    intros.
    unfold fvar. apply orb_true_iff. right. fold fvar.
    induction ts.
      simpl in H. inversion H.
      simpl in H. exact H.
  Qed.

  Lemma closed_uncons : forall (t : term) (ts : list term) (n : id),
    closed (node n (t :: ts)) -> closed t /\ closed (node n ts).
  Proof.
    intros. split; unfold closed in *;
      intro v; specialize (H v);
      unfold fvar in H; fold fvar in H;
      apply orb_false_elim in H; inversion H; assumption.
  Qed.

  Lemma closed_subs : forall (t : term) (e : env),
    closed t -> e * t = t.
  Proof.
    intros. induction t.
    Case "tvar v".
      unfold closed in H. specialize (H v).
      simpl in H. rewrite beq_var_refl in H. inversion H.
    Case "node nil".
      reflexivity.
    Case "node (t :: ts)".
      simpl.
      apply closed_uncons in H. inversion H.
      apply IHt in H0. simpl. rewrite H0.
      apply IHt0 in H1. simpl in H1. inversion H1.
        rewrite H3. rewrite H3.
      reflexivity.
  Qed.

  Lemma subs_nil : forall (e : env) (n : id),
    e * node n nil = node n nil.
  Proof. intros. reflexivity. Qed.
  
  Lemma subs_cons : forall (e : env) (t : term) (n : id) (ts : list term),
    e * (node n (t :: ts)) =
    node n (e * t :: map (subs e) ts).
  Proof. reflexivity. Qed.

  Lemma tmatch_cons : forall (n : id) (p q : term) (ps qs : list term) (a : env),
    (node n (p :: ps)) / (node n (q :: qs)) = Some a ->
    exists (b c : env),
      (p / q = Some b /\
      node n ps / node n qs = Some c /\
      Some a = b & c).
  Proof.
    intros.
    simpl in H. rewrite beq_id_refl in H. simpl in H.
    destruct (p / q) as [b|].
    Case "p / q = b".
      destruct (node n ps / node n qs) as [c|] eqn:G;
        simpl in G; rewrite beq_id_refl in G; simpl in G.
      SCase "ps / qs = c".
        exists b, c.
        split; split; try reflexivity.
        rewrite G in H. inversion H.
        reflexivity.
      SCase "ps / qs = None".
        destruct ps eqn:P; destruct qs eqn:Q;
          try inversion G; try inversion H.
        rewrite G in H. simpl in H. inversion H.
    Case "p / q = None".
      inversion H.
  Qed.
  
  Ltac break_ands :=
    repeat match goal with 
      | [ H : _ /\ _ |- _ ] => inversion H; clear H
    end.
  Ltac simpl_impls := 
    repeat match goal with
      | [ Imp : ?cond -> ?exp, Given : ?cond |- _ ] => 
        let H' := fresh "H" in 
          ((assert exp as H' by (apply Imp; exact Given)); try clear Imp)
      | [ Given : ?cond, Imp : ?cond -> ?exp |- _ ] => 
        let H' := fresh "H" in 
          ((assert exp as H' by (apply Imp; exact Given)); try clear Imp)
    end.

  Inductive TMatch (p q : term) (a : env) : Prop :=
  | TMatch_var (v : var)
    (Q : q = tvar v)
    (A : a = bind v p mtEnv) : TMatch p q a
  | TMatch_nil (n : id)
    (P : p = node n nil)
    (Q : q = node n nil)
    (A : a = mtEnv) : TMatch p q a
  | TMatch_cons (p0 q0 : term) (ps qs : list term) (n : id) (b c : env)
    (P : p = node n (p0 :: ps))
    (Q : q = node n (q0 :: qs))
    (B : p0 / q0 = Some b)
    (C : node n ps / node n qs = Some c)
    (A : Some a = b & c) : TMatch p q a.

  Lemma tmatch_ind : forall (p q : term) (a : env),
    p / q = Some a -> TMatch p q a.
  Proof.
    intros p.
    induction q as [v | n | n q qs]; intros.
    Case "q = tvar v".
      apply TMatch_var with (v := v). reflexivity.
      simpl in H. inversion H. reflexivity.
    Case "q = node n nil".
      induction p as [v | n' | n' p ps].
      SCase "p = tvar v".
        inversion H.
      SCase "p = node n' nil".
        simpl in H. destruct (beq_id n n') eqn:N.
        SSCase "n == n'".
          apply TMatch_nil with (n := n).
            apply beq_id_true in N; rewrite N; reflexivity.
          reflexivity.
          inversion H; reflexivity.
        SSCase "n /= n'".
          inversion H.
      SCase "p = node n' (p :: ps)".
        simpl in H. destruct (beq_id n n'); inversion H.
    Case "q = node n (q :: qs)".
      induction p as [v | n' | n' p ps].
      SCase "p = tvar v".
        inversion H.
      SCase "p = node n' nil".
        simpl in H. destruct (beq_id n n'); inversion H.
      SCase "p = node n' (p :: ps)".
        clear IHp; clear IHp0.
        destruct (beq_id n n') eqn:N.
        SSCase "n == n'".
          apply beq_id_true in N; symmetry in N; subst.
          apply tmatch_cons in H.
          inversion_clear H as (b & c & (B & C & A)).
          eapply TMatch_cons; eauto.
        SSCase "n /= n'".
          inversion H as [H']; rewrite N in H'; inversion H'.
  Qed.

(*
  Lemma tmatch_inv : forall (p q : term) (a : env),
    p / q = Some a ->
      (exists (v : var), q = tvar v /\ a = bind v p mtEnv) \/
      (exists (n : id), p = node n nil /\ q = node n nil) \/
      (exists (p0 q0 : term) (ps qs : list term) (n : id) (b c : env),
        p = node n (p0 :: ps) /\
        q = node n (q0 :: qs) /\
        p0 / q0 = Some b /\
        node n ps / node n qs = Some c /\
        Some a = b & c).
  Proof.
    intros. induction q as [v | n | n q qs].
    Case "q = tvar v".
      left.
      exists v. split.
        reflexivity.
        simpl in H. inversion H. reflexivity.
    Case "q = node n nil".
      right. left.
      induction p as [v | n' | n' p ps].
      SCase "p = tvar v".
        inversion H.
      SCase "p = node n' nil".
        simpl in H. destruct (beq_id n n') eqn:N.
        SSCase "n == n'".
          apply beq_id_true in N.
          exists n. split; rewrite N; reflexivity.
        SSCase "n /= n'".
          inversion H.
      SCase "p = node n' (p :: ps)".
        simpl in H. destruct (beq_id n n'); inversion H.
    Case "q = node n (q :: qs)".
      right. right.
      clear IHq; clear IHq0.
      induction p as [v | n' | n' p ps].
      SCase "p = tvar v".
        inversion H.
      SCase "p = node n' nil".
        simpl in H. destruct (beq_id n n'); inversion H.
      SCase "p = node n' (p :: ps)".
        clear IHp; clear IHp0.
        destruct (beq_id n n') eqn:N.
        SSCase "n == n'".
          apply beq_id_true in N; symmetry in N; subst.
          apply tmatch_cons in H.
          inversion_clear H as (b & c & H0).
          exists p, q, ps, qs, n, b, c. auto.
        SSCase "n /= n'".
          inversion H as [H']; rewrite N in H'; inversion H'.
  Qed.
*)

  Lemma subs_tmatch_comm : forall (p q : term) (a p_q ap_q a_pq : env),
    (forall (x : var), mem x a -> fvar x q = true) ->
    (a * p) / q = Some ap_q ->
    p / q = Some p_q ->
    a & p_q = Some a_pq ->
    a_pq ~= ap_q.
  Proof.
    intros p q a p_q ap_q a_pq M AP_Q PQ A_PQ.
    assert (H := tmatch_ind p q p_q). simpl_impls.
    inversion_clear H0.
    Case "q = tvar v".
      subst. simpl in *. inversion AP_Q. subst. SearchAbout compose_env.
      unfold compose_env in A_PQ.

    generalize dependent p.
    induction q as [v | n | n q qs ]; intros p AP_Q PQ.
    Case "q = var v".
      simpl in *.
      inversion AP_Q; clear AP_Q. inversion PQ; clear PQ. subst.
      admit.
    Case "q = node n nil". (* implies p = node n nil, a = mtEnv *)
      induction p.
      SCase "p = tvar".
        inversion PQ.
      SCase "p = node n nil".
        simpl in M. destruct a as [|v t a].
        SSCase "a = mtEnv". (* trivial *)
          simpl in *. rewrite AP_Q in PQ.
          inversion PQ; inversion A_PQ; subst.
          apply eqv_refl.
        SSCase "a = bind v t a". (* impossible *)
          assert (C: mem v (bind v t a)).
            apply mem_bind_same'.
          apply M in C. inversion C.
      SCase "p = node n (p :: ps)".
        clear IHp; clear IHp0.
        simpl in PQ.
        destruct (negb (beq_id n n0)); inversion PQ.
    Case "q = node n (q :: qs)".
      induction p as [v' | n' | n' p ps]. (* p = node n (p :: ps) *)
      SCase "p = tvar".
        simpl in PQ. inversion PQ.
      SCase "p = node n' nil".
        simpl in PQ. destruct (negb (beq_id n n')); inversion PQ.
      SCase "p = node n' (p :: ps)".
        clear IHp; clear IHp0.
        rewrite subs_cons in AP_Q.
        destruct (beq_id n n') eqn:N.
        SSCase "n == n'".
          apply beq_id_true in N; subst.
          apply tmatch_cons in PQ. inversion PQ. 
          apply tmatch_cons in AP_Q.
        SSCase "n /= n'".
          simpl in PQ. rewrite N in PQ. inversion PQ.
  Qed.

  Lemma prime : forall (p q r : term) (a b c : env),
    (a * p) / q = Some b -> p / q = Some c -> b * r = a * (c * r).
  Proof.
    intros.

  (* false *)
  (*
  Lemma subs_assoc : forall (t : term) (e1 e2 : env),
    (e2 ++ e1) * t = e1 * (e2 * t).
  Proof.
    intros. induction t.
    Case "tvar". simpl.
      destruct (lookup v e2) eqn:V.
        apply lookup_concat_member with (e2 := e1) in V. rewrite V.
  *)      

  Lemma match_subs : forall (p q : term) (v : var) (e : env),
    p / q = Some e -> e * q = p.
  Proof.
    intros.

End Term.