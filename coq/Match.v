Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.
Require Import Cases.
Require Import Util.
Require Import Env.
Require Import Term.
Require Import Subs.

  Import StdEnv.
(*
  Module TermValue <: VALUE.
    Definition val := term.
    Definition var := var.
    Definition beq_var := beq_nat.
    Definition beq_var_refl := beq_var_refl.
    Definition beq_var_sym := beq_var_sym.
    Definition beq_var_trans := beq_var_trans.
  End TermValue.

  Module TVEnv := ENV(TermValue).
  Import TVEnv.
  Definition x := mtEnv.
*)

(*
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
*)

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

  Lemma fvar_uncons : forall v n t ts,
    fvar v (node n (t :: ts)) = true ->
    fvar v t = true \/ fvar v (node n ts) = true.
  Proof.
    intros. simpl in H.
    destruct (fvar v t).
      left; reflexivity.
      right. simpl in H.
        destruct (fvar v (node n ts)) eqn:FV.
          reflexivity.
          simpl in FV. rewrite H in FV. inversion FV.
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
  Ltac break_exists :=
    repeat match goal with
      | [ H : exists x, _ |- _] => elim H; intros; clear H
    end.

  Lemma tmatch_ind : forall (P : term -> term -> env -> Prop),
    (forall p v, P p (tvar v) (bind v p mtEnv)) ->
    (forall n, P (node n nil) (node n nil) mtEnv) ->
    (forall n p q ps qs p_q ps_qs e,
      p / q = Some p_q ->
      node n ps / node n qs = Some ps_qs ->
      P p q p_q ->
      P (node n ps) (node n qs) ps_qs ->
      p_q & ps_qs = Some e ->
      P (node n (p :: ps)) (node n (q :: qs)) e) ->
    forall p q e, p / q = Some e -> P p q e.
  Proof.
    intros P Hvar Hnil Hcons p q e. generalize dependent p.
    generalize dependent e.
    induction q as [v | n | n q qs]; intros e p H.
    Case "q = tvar v".
      inversion H; apply Hvar.
    Case "q = node n nil".
      induction p as [v | n' | n' p ps]; try inversion H.
      SCase "p = node n' nil".
        destruct (beq_id n n') eqn:N; simpl in H1; inversion H1.
        apply beq_id_true in N. rewrite N. apply Hnil.
      SCase "p = node n' (p::ps)".
        simpl in H. destruct (negb (beq_id n n')); inversion H.
    Case "q = node n (q::qs)".
      induction p as [v | n' | n' p ps].
      SCase "p = tvar v". inversion H.
      SCase "p = node n' nil".
        simpl in H. destruct (beq_id n n'); inversion H.
      SCase "p = node n' (p :: ps)".
        clear IHp; clear IHp0.
        destruct (beq_id n n') eqn:N.
        SSCase "n == n'".
          apply beq_id_true in N. subst.
          apply tmatch_cons in H.
          inversion_clear H as (b & c & (B & C & A)).
          eapply Hcons; eauto.
        SSCase "n /= n'".
          inversion H as [H']; rewrite N in H'; inversion H'.
  Qed.

(*
  Fixpoint restrict e p :=
    match e with
      | mtEnv => mtEnv
      | bind v t e =>
        if fvar v p
          then bind v t (restrict e p)
          else restrict e p
    end.

  Lemma subs_restrict : forall e t,
    e * t = (restrict e t) * t.
  Proof.
    intros. generalize dependent e.
    induction t as [v | n | n t ts IHt IHts]; auto.
    Case "t = tvar v".
      induction e as [ | ve te e]; auto.
      simpl. destruct (beq_var_eq_dec ve v) as [Eq|Eq].
      SCase "v == ve".
        simpl in Eq.
        apply beq_var_true in Eq. rewrite Eq.
        unfold try_lookup. rewrite beq_var_refl.
        repeat (rewrite lookup_bind_eq).
        reflexivity.
      SCase "v /= ve".
        assert (H: beq_var ve v = false).
          simpl in Eq. unfold beq_var_eq in Eq.
          apply not_true_is_false in Eq. assumption.
        rewrite H.
        simpl in IHe. rewrite <- IHe.
        unfold try_lookup. rewrite lookup_bind_diff. reflexivity.
        symmetry; assumption.
    Case "t = node n t::ts".
      intros. simpl. f_equal. f_equal.
      rewrite IHt. admit.
      f_equal. admit.
  Qed.

  Lemma map_subs_restrict : forall e ts n,
    map (subs e) ts = map (subs (restrict e (node n ts))) ts.
  Proof.
    admit. Qed.
*)

  Lemma lookup__mem : forall v e t,
    lookup v e = Some t -> mem v e.
  Proof. intros. unfold mem, bmem. rewrite H; auto. Qed.

  Lemma union_mem : forall v a b c,
    a & b = Some c ->
    mem v c -> mem v a \/ mem v b.
  Proof.
    intros v a; revert v. induction a as [ | u t a].
    Case "a = mtEnv".
      intros; rewrite union_mtEnv_l in H; inversion H; auto.
    Case "a = bind u t a".
      intros.
      destruct (beq_var v u) eqn:Eq.
      apply beq_var_true in Eq. rewrite Eq.
      left. apply mem_bind_same. reflexivity.
      replace (mem v (bind u t a)) with (mem v a).
      assert (exists c', a & b = Some c'). apply disjoint_iff. 
      unfold union in H. destruct (disjoint (bind u t a) b) eqn:utab.
      simpl in utab. apply andb_true_iff in utab; tauto. inversion H.
      inversion_clear H1 as (c' & H1').
      apply IHa with (c := c'); auto.
      unfold union in H.
      destruct (disjoint (bind u t a) b) eqn:utab; try discriminate.
      inversion H; subst c; clear H. unfold union in H1'.
      destruct (disjoint a b) eqn:ab; try discriminate. inversion_clear H1'.
      unfold mem in *. unfold bmem in H0. simpl in H0.
      unfold ValueImpl.beq_var in H0; rewrite Eq in H0. auto.
      unfold mem at 2. unfold bmem. simpl. unfold ValueImpl.beq_var. rewrite Eq.
      reflexivity.
  Qed.


  Definition mem__fvar_defn v q e := mem v e -> fvar v q = true.

  Lemma mem__fvar : forall v p q e,
    p / q = Some e -> mem__fvar_defn v q e.
  Proof.
    intro v. apply tmatch_ind; unfold mem__fvar_defn; auto.
    Case "q = tvar v".
      intros p u M.
      unfold mem, bmem in M. simpl in M.
      destruct (ValueImpl.beq_var v u) eqn:vu; try discriminate.
      simpl. unfold ValueImpl.beq_var in vu. assumption.
    Case "q = node n q::qs".
      intros n p q ps qs p_q ps_qs e P_Q PS_QS IHq IHqs E M.
      simpl. apply union_mem with (a:=p_q) (b:=ps_qs) in M; auto.
      rewrite orb_true_iff.
      inversion M; auto.
  Qed.

  Lemma union_mem_left : forall v a b c,
    a & b = Some c ->
    mem v a ->
    lookup v c = lookup v a.
  Proof.
    intros. unfold union in H.
    destruct (disjoint a b) eqn:ab; try discriminate.
    inversion H. generalize dependent c; generalize dependent b. induction a. inversion H0.
    intros. simpl. destruct (ValueImpl.beq_var v v0) eqn:vv0; auto.
    eapply IHa; auto. apply mem_bind_diff with (v' := v0) (t := v1); auto.
    intro. rewrite H1 in vv0. discriminate.
    inversion ab. rewrite andb_true_iff in *. inversion H3. subst. rewrite H4. rewrite H1. auto.
  Qed.

  Lemma union_mem_right : forall v a b c,
    a & b = Some c ->
    mem v b ->
    lookup v c = lookup v b.
  Proof.
    intros. unfold union in H.
    destruct (disjoint a b) eqn:ab; try discriminate.
    inversion H. generalize dependent c; generalize dependent a. induction b. inversion H0.
    intros. apply lookup_concat_not_mem. intro. assert (C := disjoint_overlap _ _ _ H1 H0). 
    rewrite ab in C. inversion C.
  Qed.

  Definition subs_match_defn (p q : term) (p_q : env) : Prop :=
    forall v a ap_q t,
      (a * p) / q = Some ap_q ->
      lookup v p_q = Some t ->
      lookup v ap_q = Some (a * t).

  Theorem subs_match_proof : forall p q p_q,
    p / q = Some p_q -> subs_match_defn p q p_q.
  Proof.
    apply tmatch_ind; unfold subs_match_defn.
    Case "q = tvar v".
      intros p u v a ap_q t AP_Q T.
      simpl in *. inversion AP_Q. subst.
      unfold try_lookup, lookup in *.
      destruct (ValueImpl.beq_var v u); inversion T; auto.
    Case "q = node n nil".
      intros n u a ap_q t AP_Q T.
      inversion T.
    Case "q = node n qs".
      intros n p q ps qs p_q ps_qs e P_Q PS_QS IHq IHqs E u a ap_q t AP_Q T.
      assert (AP_Q' := AP_Q).
      rewrite subs_cons in AP_Q'. apply tmatch_cons in AP_Q'.
      inversion_clear AP_Q' as (b & c & B & C & BC).
      assert (M := T). apply lookup__mem in M.
      apply union_mem with (a:=p_q) (b:=ps_qs) in M; auto.
      inversion_clear M as [Mq | Mqs].
      SCase "u in q".
        assert (L: lookup u b = Some (a * t)).
        SSCase "Prove L".
          apply IHq; auto.
          apply union_mem_left with (b:=ps_qs) (c:=e) in Mq; auto.
          rewrite <- Mq; assumption.
        SSCase "Use L".
          rewrite <- L. eapply union_mem_left.
          symmetry; exact BC.
          eapply lookup__mem. exact L.
      SCase "u in qs".
        assert (L: lookup u c = Some (a * t)).
        SSCase "Prove L".
          apply IHqs; auto.
          apply union_mem_right with (a := p_q) (b:=ps_qs) (c:=e) in Mqs; auto.
          rewrite <- Mqs; assumption.
        SSCase "Use L".
          rewrite <- L. eapply union_mem_right.
          symmetry; exact BC.
          eapply lookup__mem. exact L.
  Qed.

  Definition fvar_false_lookup_defn v q e :=
    fvar v q = false -> lookup v e = None.
  Lemma fvar_false_lookup_proof : forall v p q e,
    p / q = Some e -> fvar_false_lookup_defn v q e.
  Proof.
    intros v p q e.
    intros. apply tmatch_ind with (p:=p) (q:=q) (e:=e).
    apply tmatch_ind.
    intros v p q; revert v p.
    apply 
    induction q; intros; auto. simpl in H0. simpl in H. inversion H0. simpl. unfold ValueImpl.beq_var.
    rewrite H. auto.
    simpl in H0. destruct p. inversion H0. destruct (negb (beq_id n i)). inversion H0.
    destruct l. inversion H0. auto. inversion H0.
    simpl in H. apply orb_false_iff in H. inversion_clear H. 
    assert (H' : forall p e, p / q = Some e -> lookup v e = None). intros. eapply IHq. auto. exact H.

  Lemma fvar_false_lookup : forall v p q e,
    fvar v q = false -> p / q = Some e -> lookup v e = None.
  Proof.
    intros v p q; revert v p.
    induction q; intros; auto. simpl in H0. simpl in H. inversion H0. simpl. unfold ValueImpl.beq_var.
    rewrite H. auto.
    simpl in H0. destruct p. inversion H0. destruct (negb (beq_id n i)). inversion H0.
    destruct l. inversion H0. auto. inversion H0.
    simpl in H. apply orb_false_iff in H. inversion_clear H. 
    assert (H' : forall p e, p / q = Some e -> lookup v e = None). intros. eapply IHq. auto. exact H.

  Corollary subs_match : forall p q a p_q ap_q,
    p / q = Some p_q ->
    (forall v, mem v a -> fvar v q = true) ->
    (a * p) / q = Some ap_q ->
    ap_q == compose a p_q.
  Proof.
    intros.
    assert (subs_match_defn p q p_q).
      apply subs_match_proof. assumption.
    unfold subs_match_defn in H2.
    intro. 
    assert (forall v t, lookup v p_q = Some t -> lookup v ap_q = Some (a * t)) by auto.
    destruct (fvar v q) eqn:FV.
      admit.
    
    auto.
  Qed.

  Definition env_sim a b :=
    forall v, try_lookup v a = try_lookup v b.
  Notation "a === b" := (env_sim a b) (at level 60).

  Corollary subs_match_eq : forall a b p,
    (a * p) / p = Some b -> a === b.
  Proof.
    intros.
    assert (G: b === compose a mtEnv).
      apply (subs_match p p).

(*
  Lemma prime : forall p q a p_q ap_q a_pq,
    (forall (x : var), mem x a -> fvar x q = true) ->
    (a * p) / q = Some ap_q ->
    p / q = Some p_q ->
    a & p_q = Some a_pq ->
    a_pq == ap_q.
  Proof.
    intros. intro v.
    

  Lemma subs_tmatch_comm : forall (p q : term) (a p_q ap_q a_pq : env),
    (forall (x : var), mem x a -> fvar x q = true) ->
    (a * p) / q = Some ap_q ->
    p / q = Some p_q ->
    a & p_q = Some a_pq ->
    a_pq == ap_q.
  Proof.
    (*
    intros p q a p_q ap_q a_pq M AP_Q PQ A_PQ.
    assert (H := tmatch_case p q p_q). simpl_impls.
    inversion H0.
    Case "q = tvar v". rename v into vq.
      simpl in *. intro.
      inversion AP_Q; clear AP_Q. inversion PQ; clear PQ. subst.
      admit.
    Case "q = node n nil".
      simpl; intro. subst.
      simpl in AP_Q. rewrite beq_id_refl in AP_Q. simpl in AP_Q.
      inversion AP_Q. subst.
      assert (H: a = mtEnv).
        destruct a. reflexivity.
        specialize M with v0. simpl in M.
        assert (false = true). apply M. apply mem_bind. inversion H.
      rewrite H in A_PQ. inversion A_PQ.
      subst; reflexivity.
    Case "q = node n (q :: qs)".
      intro; subst.
      rename q0 into q. rename p0 into p.
      induction q.
      apply tmatch_cons in PQ.
      simpl in *. rewrite beq_id_refl in *. simpl in *.
      *)

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
*)
