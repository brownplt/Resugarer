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

  Lemma lookup__mem : forall v e t,
    lookup v e = Some t -> mem v e.
  Proof. intros. unfold mem, bmem. rewrite H; auto. Qed.

  Lemma not_lookup__not_mem : forall v e,
    lookup v e = None -> ~ mem v e.
  Proof. intros. unfold mem, bmem. rewrite H; auto. Qed.

(*
  Lemma union_sym : forall a b ab,
    a & b = Some ab ->
    exists ba, b & a = Some ba /\ ab == ba.
  Proof.
    intros. unfold union in *.
    intros. generalize dependent b. generalize dependent ab.
    induction a as [ | v t a]; intros.
    Case "a = mtEnv".
      rewrite union_mtEnv_l in H. inversion H.
      exists ab. rewrite union_mtEnv_r. split; reflexivity.
    Case "a = bind v t a".
      unfold union in H.    

  Lemma union_not_mem_left : forall v a b c,
    a & b = Some c ->
    ~ (mem v a) ->
    bmem v b = bmem v c.
  Proof.
    intros. induction a.

  Lemma union_mem : forall v a b c,
    a & b = Some c ->
    (mem v c <-> mem v a \/ mem v b).
  Proof.
    intros. split. intro.
    inversion H0. SearchAbout union.
    SearchAbout mem.
*)

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

  Definition subs_tmatch_defn (p q : term) (p_q : env) : Prop :=
    forall v a ap_q t,
      (a * p) / q = Some ap_q ->
      lookup v p_q = Some t ->
      lookup v ap_q = Some (a * t).

  Theorem subs_tmatch_proof : forall p q p_q,
    p / q = Some p_q -> subs_tmatch_defn p q p_q.
  Proof.
    apply tmatch_ind; unfold subs_tmatch_defn.
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

  Lemma bmem_concat : forall v a b,
    bmem v (a ++ b) = bmem v a || bmem v b.
  Proof.
    intros. induction a; auto.
    simpl. unfold bmem, lookup, ValueImpl.beq_var.
    destruct (beq_var v v0); auto.
  Qed.

  Definition fvar_mem_defn v q e :=
    fvar v q = bmem v e.
  Lemma fvar_mem_proof : forall v p q e,
    p / q = Some e -> fvar_mem_defn v q e.
  Proof.
    intro v. apply tmatch_ind; unfold fvar_mem_defn; auto.
    Case "q = tvar u".
      intros p u. unfold bmem. simpl. unfold ValueImpl.beq_var.
      destruct (beq_var v u); auto.
    Case "q = node n (q::qs)".
      intros n p q ps qs p_q ps_qs e P_Q PS_QS IHq IHqs E.
      simpl. rewrite IHq. simpl in IHqs. rewrite IHqs.
      unfold union in E. destruct (disjoint p_q ps_qs) eqn:D; try inversion E.
      symmetry. apply bmem_concat.
  Qed.

  Lemma fvar_mem : forall v p q e,
    p / q = Some e -> fvar v q = bmem v e.
  Proof.
    intros. assert (fvar_mem_defn v q e) by
      (apply fvar_mem_proof with (p:=p); auto).
    auto.
  Qed.

  Corollary subs_tmatch : forall p q a p_q ap_q,
    p / q = Some p_q ->
    (forall v, mem v a -> fvar v q = true) ->
    (a * p) / q = Some ap_q ->
    ap_q == compose a p_q.
  Proof.
    intros p q a p_q ap_q P_Q FV AP_Q.
    rewrite subs_lookup_eqv; intros t.
    induction t; auto.
    SCase "t = tvar v".
      rewrite <- compose_subs_eq.
      assert (H: subs_tmatch_defn p q p_q). apply subs_tmatch_proof; auto.
      unfold subs_tmatch_defn in H.
      simpl. unfold try_lookup.
      destruct (lookup v p_q) as [t|] eqn:L.
      SSCase "(p/q)[v] = Some t".
        apply H with (v:=v) (t:=t) in AP_Q; auto.
        rewrite AP_Q. reflexivity.
      SSCase "(p/q)[v] = None".
        apply not_lookup__not_mem in L. unfold mem in L.
        apply not_true_is_false in L. rewrite <- fvar_mem with (p:=p) (q:=q) in L; auto.
        rewrite fvar_mem with (p:=a*p) (e:=ap_q) in L; auto.
        rewrite <- not_true_iff_false in L.
        assert (M: ~ mem v ap_q). unfold mem. assumption.
        rewrite lookup_not_mem in M. rewrite M.
        destruct (bmem v a) eqn:MA; elim_bmems.
        SSSCase "v in a".
          apply FV in MA.
          rewrite fvar_mem with (p:=a*p) (e:=ap_q) in MA; try contradiction.
          assumption.
        SSSCase "v not in a".
          simpl. rewrite try_lookup_not_mem; auto.
    SCase "t = node n (t::ts)".
      simpl in *. rewrite IHt. inversion IHt0. rewrite H0. reflexivity.
  Qed.

  Lemma lookup_union_not_mem : forall v a b c,
    a & b = Some c -> ~ (mem v a) -> lookup v c = lookup v b.
  Proof.
    intros.
    unfold union in H. destruct (disjoint a b); inversion H.
    rewrite lookup_concat_not_mem; auto.
  Qed.
  
  Lemma lookup_union_mem : forall v a b c,
    a & b = Some c -> mem v a -> lookup v c = lookup v a.
  Proof.
    intros.
    unfold union in H. destruct (disjoint a b); inversion H.
    rewrite lookup_concat_mem; auto.
  Qed.

  Lemma tmatch_eq :
    forall p e, p / p = Some e -> e == mtEnv.
  Proof.
    induction p; intros.
    Case "p = tvar v".
      inversion H. simpl.
      intros u. unfold try_lookup, lookup, ValueImpl.beq_var.
      destruct (beq_var u v) eqn:uv; auto. apply beq_var_true in uv. auto.
    Case "p = node n nil".
      inversion H. rewrite beq_id_refl in H1. inversion H1. reflexivity.
    Case "p = node n (p::ps)". rename IHp0 into IHps.
      apply tmatch_cons in H. inversion_clear H as (b & c & B & C & E).
      apply IHp in B. apply IHps in C.
      intro v.
      assert (D: disjoint b c = true) by
        (rewrite disjoint_iff; eauto).
      destruct (bmem v b) eqn:Mb; elim_bmems.
      SCase "v in b".
        destruct (bmem v c) eqn:Mc; elim_bmems.
        SSCase "v in c".
          contradict D. rewrite not_true_iff_false.
          apply disjoint_overlap with (v:=v); auto.
        SSCase "v not in c".
          assert (lookup v e = lookup v b) by
            (eapply lookup_union_mem; eauto).
          apply lookup_eqv in H; rewrite H; auto.
      SCase "v not in b".
        assert (lookup v e = lookup v c) by
          (eapply lookup_union_not_mem; eauto).
        apply lookup_eqv in H; rewrite H; auto.
  Qed.

  Lemma compose_mtEnv_r : forall e,
    compose e mtEnv = e.
  Proof. auto. Qed.

  Lemma compose_mtEnv_l : forall e,
    compose mtEnv e = e.
  Proof. intros. induction e; auto. simpl. rewrite IHe. rewrite subs_mtEnv. auto. Qed.

  Add Parametric Morphism : compose with signature (equiv ==> equiv ==> equiv) as compose_morph.
  Proof.
    intros a1 a2 A b1 b2 B.
    rewrite subs_lookup_eqv in *.
    induction t; auto;
      repeat (rewrite <- compose_subs_eq);
      rewrite A, B; reflexivity.
  Qed.
  
  Definition subs_exists_defn (q : term) (a : env) := exists e, q / q = Some e.
  Lemma subs_exists_proof : forall p q a, p / q = Some a -> subs_exists_defn q a.
  Proof.
    apply tmatch_ind; unfold subs_exists_defn; intros.
    Case "q = tvar v".
      simpl. eauto.
    Case "p, q = node n nil".
      simpl. rewrite beq_id_refl. simpl. eauto.
    Case "q = node n (q :: qs)".
      simpl. rewrite beq_id_refl. simpl.
      inversion H1 as [e1 G1]. rewrite G1.
      inversion H2 as [e2 G2].
      assert (G2' := G2). simpl in G2'. rewrite beq_id_refl in G2'. simpl in G2'. rewrite G2'. clear G2'.
      simpl.
      admit.
  Qed.
  Lemma subs_exists : forall p q a, p / q = Some a -> exists e, q / q = Some e.
  Proof.
    apply subs_exists_proof.
  Qed.

  Corollary subs_tmatch_eq : forall a b p,
    (forall v, mem v a -> fvar v p = true) ->
    (a * p) / p = Some b -> a == b.
  Proof.
    intros a b p FV H.
    destruct (p / p) eqn:I.
    Case "p / p exists".
      assert (E := I). apply tmatch_eq in E.
      assert (S: b == compose a e) by
        (eapply subs_tmatch; eauto).
      rewrite S. rewrite E. reflexivity.
    Case "p / p dne".
      apply subs_exists in H. inversion H.
      rewrite H0 in I; discriminate I.
  Qed.

  Lemma tmatch_subs_eq : forall p q a,
    p / q = Some a -> a * q = p.
  Proof.
    apply tmatch_ind; intros; auto.
    Case "q = tvar v".
      simpl. assert ((lookup v (bind v p mtEnv)) = Some p) by
        apply lookup_bind_eq.
      unfold try_lookup. rewrite H. reflexivity.
    Case "q = node n q::qs".
      rewrite subs_cons. simpl in H2. inversion H2.
      assert (Ep: e * q = p).
        rewrite <- H1. admit.
      assert (Eps: map (subs e) qs = ps).
        rewrite <- H5. admit.
      assert (Eps': map (subs ps_qs) qs = ps).
        admit.
      rewrite Ep. rewrite Eps. rewrite Eps'. reflexivity.
  Qed.