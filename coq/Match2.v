Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid Coq.Classes.SetoidClass.
Require Import Cases.
Require Import Util.
Require Import Env.
Require Import Term2.
Require Import Subs2.

Import StdEnv.

Fixpoint tmatch (q p : term) {struct q} : option env :=
  match (q, p) with
    | (tvar v, _)            => Some (bind v p mtEnv)
    | (const c1, const c2)   => if beq_id c1 c2 then Some mtEnv else None
    | (empty, empty)         => Some mtEnv
    | (cons q qs, cons p ps) => e1 <- tmatch q p;
                                e2 <- tmatch qs ps;
                                e1 & e2
    | (_, _)                 => None
  end.

Notation "p / q" := (tmatch q p).

Lemma fvar_cons : forall p ps v,
  fvar v (cons p ps) = fvar v p || fvar v ps.
Proof.
  intros. reflexivity.
Qed.

Lemma closed_uncons : forall p ps,
  closed (cons p ps) -> closed p /\ closed ps.
Proof.
  intros. unfold closed in *.
  split; intros; specialize H with v; rewrite fvar_cons in H;
    apply orb_false_iff in H; inversion H; assumption.
Qed.

Lemma closed_subs : forall p a,
  closed p -> a * p = p.
Proof.
  intros. induction p; auto.
  Case "tvar v".
    unfold closed in H. specialize (H v).
    simpl in H. rewrite beq_var_refl in H. inversion H.
  Case "p = cons p1 p2".
    simpl. apply closed_uncons in H. inversion H.
    apply IHp1 in H0. apply IHp2 in H1. rewrite H0. rewrite H1.
    reflexivity.
Qed.

Lemma subs_cons : forall a p q,
  a * (cons p q) = cons (a * p) (a * q).
Proof. reflexivity. Qed.

Lemma tmatch_cons : forall p ps q qs a,
  cons p ps / cons q qs = Some a ->
  exists b c,
    p / q = Some b /\
    ps / qs = Some c /\
    b & c = Some a.
Proof.
  intros.
  simpl in H.
  destruct (p / q) as [b|] eqn:B;
    destruct (ps / qs) as [c|] eqn:C;
      simpl in H; try inversion H.
  exists b, c. auto.
Qed.

Lemma tmatch_ind : forall (P : term -> term -> env -> Prop),
  (forall p v, P p (tvar v) (bind v p mtEnv)) ->
  (forall n, P (const n) (const n) mtEnv) ->
  (P empty empty mtEnv) ->
  (forall p ps q qs p_q ps_qs a,
    p / q = Some p_q ->
    ps / qs = Some ps_qs ->
    P p q p_q ->
    P ps qs ps_qs ->
    p_q & ps_qs = Some a ->
    P (cons p ps) (cons q qs) a) ->
  forall p q a, p / q = Some a -> P p q a.
Proof.
  intros P Hvar Hconst Hempty Hcons p q. generalize dependent p.
  induction q; intros.
  Case "q = tvar v".
    inversion H; apply Hvar.
  Case "q = const i".
    destruct p; try inversion H.
    destruct (beq_id i i0) eqn:I; inversion H1.
    apply beq_id_true in I. rewrite I. apply Hconst.
  Case "q = empty".
    inversion H. destruct p; try discriminate. inversion H1. apply Hempty.
  Case "q = cons q1 q2".
    destruct p; try discriminate.
    apply tmatch_cons in H. inversion H as (b & c & B & C & A).
    apply Hcons with (p_q:=b) (ps_qs:=c); auto.
Qed.

Definition subs_tmatch_defn (p q : term) (p_q : env) : Prop :=
  forall v a ap_q r,
    (a * p) / q = Some ap_q ->
    lookup v p_q = Some r ->
    lookup v ap_q = Some (a * r).

Theorem subs_tmatch_proof : forall p q p_q,
  p / q = Some p_q -> subs_tmatch_defn p q p_q.
Proof.
  apply tmatch_ind; unfold subs_tmatch_defn; try discriminate.
  Case "q = tvar v".
    intros p v u a ap_q r AP_Q R.
    inversion AP_Q.
    simpl in *. destruct (VarImpl.beq_var u v); inversion R.
    reflexivity.
  Case "cons".
    intros p ps q qs p_q ps_qs e P_Q PS_QS IHq IHqs E u a ap_q r AP_Q R.
    assert (AP_Q' := AP_Q). apply tmatch_cons in AP_Q'. fold subs in AP_Q'.
    inversion_clear AP_Q' as (b & c & B & C & BC).
    assert (M := R). apply lookup__mem in M.
    apply union_mem with (a:=p_q) (b:=ps_qs) in M; auto.
    inversion_clear M as [Mq | Mqs].
    SCase "u in q".
      assert (L: lookup u b = Some (a * r)).
      SSCase "Prove L".
        apply IHq; auto. eapply union_mem_left in Mq; eauto. rewrite <- Mq. auto.
      SSCase "Use L".
        rewrite <- L. eapply union_mem_left. exact BC. eapply lookup__mem. exact L.
    SCase "u in qs".
      assert (L: lookup u c = Some (a * r)).
      SSCase "Prove L".
        apply IHqs; auto. eapply union_mem_right in Mqs; eauto. rewrite <- Mqs. auto.
      SSCase "Use L".
        rewrite <- L. eapply union_mem_right. exact BC. eapply lookup__mem. exact L.
Qed.

Lemma mem_concat : forall v a b,
  mem v (a ++ b) = mem v a || mem v b.
Proof.
  intros. induction a; auto.
  simpl. unfold mem, lookup, VarImpl.beq_var.
  destruct (beq_var v v0); auto.
Qed.

Definition fvar_mem_defn v q e :=
  fvar v q = mem v e.
Lemma fvar_mem_proof : forall v p q a,
  p / q = Some a -> fvar_mem_defn v q a.
Proof.
  intro v. apply tmatch_ind; unfold fvar_mem_defn; auto.
  Case "q = tvar u".
    intros p u. unfold mem. simpl. unfold VarImpl.beq_var.
    destruct (beq_var v u); auto.
  Case "cons".
    intros p q ps qs p_q ps_qs a P_Q PS_QS IHq IHqs A.
    simpl. rewrite IHq. rewrite IHqs.
    unfold union in A. destruct (disjoint p_q ps_qs) eqn:D; try discriminate.
    inversion A. symmetry. apply mem_concat.
Qed.

Lemma fvar_mem : forall v p q e,
  p / q = Some e -> fvar v q = mem v e.
Proof.
  intros. assert (fvar_mem_defn v q e) by
    (apply fvar_mem_proof with (p:=p); auto).
  auto.
Qed.

Corollary subs_tmatch : forall p q a p_q ap_q,
  p / q = Some p_q ->
  (forall v, mem v a = true -> fvar v q = true) ->
  (a * p) / q = Some ap_q ->
  ap_q == compose a p_q.
Proof.
  intros p q a p_q ap_q P_Q FV AP_Q.
  rewrite subs_lookup_eqv; intros r.
  induction r; auto.
  SCase "r = tvar v".
    rewrite <- compose_subs_eq.
    assert (H: subs_tmatch_defn p q p_q). apply subs_tmatch_proof; auto.
    unfold subs_tmatch_defn in H.
    simpl. unfold try_lookup.
    destruct (lookup v p_q) as [r|] eqn:L.
    SSCase "(p/q)[v] = Some r".
      apply H with (v:=v) (r:=r) in AP_Q; auto.
      rewrite AP_Q. reflexivity.
    SSCase "(p/q)[v] = None".
      apply not_lookup__not_mem in L.
      rewrite <- fvar_mem with (p:=p) (q:=q) in L; auto.
      rewrite fvar_mem with (p:=a*p) (e:=ap_q) in L; auto.
      assert (M := L). rewrite lookup_not_mem in M. rewrite M.
      destruct (mem v a) eqn:MA.
      SSSCase "v in a".
        apply FV in MA.
        rewrite fvar_mem with (p:=a*p) (e:=ap_q) in MA.
          rewrite MA in L; inversion L.
        assumption.
      SSSCase "v not in a".
        simpl. rewrite try_lookup_not_mem; auto.
  SCase "r = cons r1 r2".
    simpl. rewrite IHr1. rewrite IHr2. reflexivity.
Qed.

Lemma lookup_union_not_mem : forall v a b c,
  a & b = Some c -> mem v a = false -> lookup v c = lookup v b.
Proof.
  intros.
  unfold union in H. destruct (disjoint a b); inversion H.
  rewrite lookup_concat_not_mem; auto.
Qed.
  
Lemma lookup_union_mem : forall v a b c,
  a & b = Some c -> mem v a = true -> lookup v c = lookup v a.
Proof.
  intros.
  unfold union in H. destruct (disjoint a b); inversion H.
  rewrite lookup_concat_mem; auto.
Qed.

Lemma tmatch_eq :
  forall p a, p / p = Some a -> a == mtEnv.
Proof.
  induction p; intros.
  Case "p = tvar v".
    inversion H. simpl.
    intros u. unfold try_lookup, lookup, VarImpl.beq_var.
    destruct (beq_var u v) eqn:uv; auto. apply beq_var_true in uv. auto.
  Case "p = const i".
    inversion H. rewrite beq_id_refl in H1. inversion H1. reflexivity.
  Case "p = empty".
    inversion H. reflexivity.
  Case "p = cons p1 p2".
    apply tmatch_cons in H. inversion_clear H as (b & c & B & C & A).
    apply IHp1 in B. apply IHp2 in C.
    intro v.
    assert (D: disjoint b c = true) by
      (rewrite disjoint_iff; eauto).
    destruct (mem v b) eqn:Mb.
    SCase "v in b".
      destruct (mem v c) eqn:Mc.
      SSCase "v in c".
        contradict D. rewrite not_true_iff_false.
        apply disjoint_overlap with (v:=v); auto.
      SSCase "v not in c".
        assert (lookup v a = lookup v b) by
          (eapply lookup_union_mem; eauto).
        apply lookup_eqv in H; rewrite H; auto.
    SCase "v not in b".
      assert (lookup v a = lookup v c) by
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
  induction p; auto;
    repeat (rewrite <- compose_subs_eq);
    rewrite A, B; reflexivity.
Qed.


Definition opt_env_eqv a b :=
  match (a, b) with
    | (None, None) => True
    | (Some a, Some b) => a == b
    | (_, _) => False
  end.

Lemma opt_env_eqv_refl : forall a, opt_env_eqv a a.
Proof. intros. unfold opt_env_eqv. destruct a; reflexivity. Qed.
Lemma opt_env_eqv_sym : forall a b, opt_env_eqv a b -> opt_env_eqv b a.
Proof. unfold opt_env_eqv. intros. destruct b; destruct a; auto. symmetry. apply H. Qed.
Lemma opt_env_eqv_trans : forall a b c, opt_env_eqv a b -> opt_env_eqv b c -> opt_env_eqv a c.
Proof. unfold opt_env_eqv. intros. destruct b; destruct a; destruct c; auto.
  transitivity e; auto. contradiction. Qed.

Add Relation (option env) opt_env_eqv
  reflexivity proved by opt_env_eqv_refl
  symmetry proved by opt_env_eqv_sym
  transitivity proved by opt_env_eqv_trans
  as Opt_env_eqv.

Instance opt_env_eqv_Setoid : Setoid (option env) :=
  {equiv := opt_env_eqv; setoid_equiv := Opt_env_eqv}.

(*
Add Parametric Morphism : union with signature (equiv ==> equiv ==> equiv) as Union_morph.
  intros. 
*)
  (* Unproven !!! *)

Definition wf p :=
  match p / p with
    | None => false
    | Some _ => true
  end.

Lemma wf_true : forall p, wf p = true -> exists a, p / p = Some a.
Proof. intros. unfold wf in H. destruct (p / p). exists e; auto. inversion H. Qed.

Lemma wf_var : forall v, wf (tvar v) = true.
Proof. reflexivity. Qed.
Hint Resolve wf_var.

Lemma wf_const : forall i, wf (const i) = true.
Proof. intros. unfold wf. simpl. rewrite beq_id_refl. reflexivity. Qed.
Hint Resolve wf_const.

Lemma wf_empty : wf empty = true.
Proof. reflexivity. Qed.
Hint Resolve wf_empty.

Lemma wf_cons : forall p q,
  wf (cons p q) = true -> wf p = true /\ wf q = true.
Proof.
  intros.
  unfold wf in *. simpl in H.
  destruct (p / p); destruct (q / q); try discriminate.
  auto.
Qed.
Hint Resolve wf_cons.

Lemma wf_overlap : forall p q v,
  fvar v p = true -> fvar v q = true -> wf (cons p q) = false.
Proof.
  intros. unfold wf. simpl.
  destruct (p / p) eqn:P; destruct (q / q) eqn:Q; auto. simpl.
  rewrite fvar_mem with (p:=p) (q:=p) (e:=e) in H; auto.
  rewrite fvar_mem with (p:=q) (q:=q) (e:=e0) in H0; auto.
  rewrite union_overlap with (v:=v); auto.
Qed.

Lemma disjoint_mem_iff : forall a b,
  disjoint a b = true <-> forall v, mem v a = true -> mem v b = true -> False.
Proof.
  split; intros.
  Case "Forward".
    contradict H. rewrite not_true_iff_false.
    apply disjoint_overlap with (v:=v); assumption.
  Case "Reverse".
    induction a as [ | v t a]; auto.
    simpl. rewrite andb_true_iff. split.
    SCase "Show v not in b".
      rewrite negb_true_iff. specialize H with v.
      rewrite mem_bind_same in H.
      destruct (mem v b); auto. elim H; auto. reflexivity.
    SCase "Show (disjoint a b)".
      apply IHa. intros u Ma Mb.
      specialize H with u. elim H; try assumption.
      apply mem_bind. assumption.
Qed.

Definition fvar_disjoint p q := forall v,
  fvar v p = true -> fvar v q = true -> False.

Lemma fvar_disjoint_union : forall p q ps qs p_q ps_qs,
  p / q = Some p_q ->
  ps / qs = Some ps_qs ->
  (fvar_disjoint q qs <-> disjoint p_q ps_qs = true).
Proof.
  intros.
  rewrite disjoint_mem_iff. unfold fvar_disjoint.
  split; intros.
  Case "forward".
    rewrite <- fvar_mem with (p:=p) (q:=q) in H2; try assumption.
    rewrite <- fvar_mem with (p:=ps) (q:=qs) in H3; try assumption.
    elim H1 with (v:=v); assumption.
  Case "reverse".
    rewrite fvar_mem with (p:=p) (e:=p_q) in H2; try assumption.
    rewrite fvar_mem with (p:=ps) (e:=ps_qs) in H3; try assumption.
    elim H1 with (v:=v); assumption.
Qed.

Lemma wf_cons_iff : forall p q,
  wf (cons p q) = true <-> wf p = true /\ wf q = true /\ fvar_disjoint p q.
Proof.
  split; intros.
  Case "Forward".
    unfold fvar_disjoint.
    assert (H' := H). apply wf_cons in H'. inversion H'.
    split. assumption. split. assumption. intros.
    contradict H. rewrite not_true_iff_false.
    apply wf_overlap with (v:=v); assumption.
  Case "Reverse".
    inversion_clear H as (WFp & WFq & FV).
    unfold wf in *. simpl.
    destruct (p / p) eqn:P; destruct (q / q) eqn:Q; auto.
      simpl. rename e into e1; rename e0 into e2.
    assert (D: disjoint e1 e2 = true).
      rewrite <- fvar_disjoint_union with
        (p_q:=e1) (ps_qs:=e2) (p:=p) (q:=p) (ps:=q)(qs:=q); auto.
    apply disjoint_iff in D. inversion D. rewrite H. reflexivity.
Qed.

Lemma tmatch__wf : forall p q a,
  p / q = Some a -> wf q = true.
Proof.
  intros.
  eapply tmatch_ind with (p:=p) (q:=q); auto.
  Case "cons".
    intros p1 p2 q1 q2 a1 a2 a12 A1 A2 WF1 WF2 A12.
    assert (G: exists a12, a1 & a2 = Some a12) by (exists a12; assumption).
    rewrite <- disjoint_iff in G.
    rewrite disjoint_mem_iff in G.
    assert (FV: fvar_disjoint q1 q2).
      rewrite fvar_disjoint_union with
        (p:=p1) (q:=q1) (ps:=p2) (qs:=q2) (p_q:=a1) (ps_qs:=a2); try assumption.
      apply disjoint_iff. exists a12. assumption.
    apply wf_cons_iff; auto.
    apply H.
Qed.

Lemma wf__tmatch : forall a p, wf p = true -> exists b, a * p / p = Some b.
Proof.
  intros. induction p; simpl; try eauto.
  Case "const i".
    rewrite beq_id_refl. eauto.
  Case "cons p1 p2".
    apply wf_cons_iff in H. inversion H as (WF1 & WF2 & D).
    apply IHp1 in WF1. apply IHp2 in WF2.
    inversion_clear WF1 as (b & B).
    inversion_clear WF2 as (c & C).
    rewrite B. rewrite C. simpl.
    rewrite fvar_disjoint_union with (p_q:=b) (ps_qs:=c) in D; try eauto.
    apply disjoint_true in D. rewrite D. eauto.
Qed.

Lemma wf_tmatch_iff : forall a p,
  wf p = true <-> exists b, a * p / p = Some b.
Proof.
  split; intros. apply wf__tmatch; assumption.
  inversion H as (b & B). apply tmatch__wf with (p:=a*p) (a:=b); assumption.
Qed.

Definition vareqv a b p :=
  forall v, fvar v p = true -> try_lookup v a = try_lookup v b.

Lemma subs_vareqv : forall a b p,
  vareqv a b p -> a * p = b * p.
Proof.
  intros. unfold vareqv in H. induction p; try reflexivity.
  Case "tvar v".
    simpl. apply H. simpl. apply beq_var_refl.
  Case "cons p1 p2".
    simpl. rewrite IHp1. rewrite IHp2. reflexivity.
      intros. apply H. rewrite fvar_cons. apply orb_true_iff. right; assumption.
      intros. apply H. rewrite fvar_cons. apply orb_true_iff. left; assumption.
Qed.

Corollary subs_tmatch_eq : forall a b p,
  (forall v, mem v a = true -> fvar v p = true) ->
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
    apply tmatch__wf in H. apply wf_true in H. rewrite I in H.
    inversion H; discriminate.
Qed.

(*
Corollary subs_match_eq' : forall a b p,
  (a * p) / p = Some b -> vareqv a b p.
*)

(* Correctness of tmatch *)
Theorem tmatch_subs_eq : forall p q a,
  p / q = Some a -> a * q = p.
Proof.
  apply tmatch_ind; intros; auto.
  Case "q = tvar v".
    simpl. assert ((lookup v (bind v p mtEnv)) = Some p) by
    apply lookup_bind_eq.
    unfold try_lookup. rewrite H. reflexivity.
  Case "q = node n q::qs".
    rewrite subs_cons. simpl in H2. inversion H2.
    assert (Gq: a * q = p_q * q).
      apply subs_vareqv. intros v FV.
      rewrite fvar_mem with (p:=p) (e:=p_q) in FV; try assumption.
      apply union_mem_left with (a:=p_q) (b:=ps_qs) (c:=a) in FV; try assumption.
      apply lookup_eqv. exact FV.
    assert (Gqs: a * qs = ps_qs * qs).
      apply subs_vareqv. intros v FV.
      rewrite fvar_mem with (p:=ps) (e:=ps_qs) in FV; try assumption.
      apply union_mem_right with (a:=p_q) (b:=ps_qs) (c:=a) in FV; try assumption.
      apply lookup_eqv. exact FV.
    rewrite Gq. rewrite H1. rewrite Gqs. reflexivity.
Qed.