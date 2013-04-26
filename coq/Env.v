Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Cases.
Require Import Patt.


Inductive env :=
| mtEnv : env
| bind : vid -> term -> env -> env.

Fixpoint try_lookup (v : vid) (e : env) : option term :=
  match e with
    | mtEnv => None
    | bind v' t e =>
      if beq_vid v v'
        then Some t
        else try_lookup v e
  end.

Definition lookup (v : vid) (e : env) : patt :=
  match try_lookup v e with
    | None => pvar v
    | Some t => term_to_patt t
  end.

Definition bmem (v : vid) (e : env) : bool :=
  match try_lookup v e with
    | None => false
    | Some _ => true
  end.

Definition mem (v : vid) (e : env) : Prop :=
  bmem v e = true.

Fixpoint insert_binding (v : vid) (t : term) (e : env) : option env :=
  match e with
    | mtEnv => Some (bind v t mtEnv)
    | bind v' t' e' =>
      if beq_vid v v'
        then None
        else match insert_binding v t e' with
               | None => None
               | Some e' => Some (bind v' t' e')
             end
  end.

(* Compose two environments. Fail if they overlap. *)
Fixpoint compose_env (e1 e2 : env) {struct e1} : option env :=
  match e1 with
    | mtEnv => Some e2
    | bind v t e1 =>
      if bmem v e2
        then None
        else match compose_env e1 e2 with
               | None => None
               | Some e => Some (bind v t e)
             end
  end.

Notation "x & y" := (compose_env x y) (at level 60).

Fixpoint subs (e : env) (p : patt) : patt :=
  match p with
    | pvar v => lookup v e
    | pnode n ps => pnode n (map (subs e) ps)
  end.

Notation "e * p" := (subs e p).

Definition env_eqv (e1 e2 : env) :=
  forall (v : vid), lookup v e1 = lookup v e2.

Notation "e1 ~= e2" := (env_eqv e1 e2) (at level 40).




(*******************)
(*** Easy Lemmas ***)
(*******************)



Lemma env_eqv_subs : forall (e1 e2 : env) (p : patt),
  e1 ~= e2 -> e1 * p = e2 * p.
Proof.
  intros. induction p.
  Case "var v". simpl. unfold env_eqv in H. apply H.
  Case "node n nil". reflexivity.
  Case "node n (p :: ps)". simpl. rewrite IHp.
    inversion IHp0. rewrite H1. reflexivity.
Qed.

Lemma mtEnv_subs_l : forall (p : patt), mtEnv * p = p.
Proof.
  intros. induction p; try reflexivity.
  Case "node n (p :: ps)". inversion IHp0.
    simpl. rewrite IHp. rewrite H0. rewrite H0. reflexivity.
Qed.

Lemma mem_mtEnv : forall (v : vid), ~ (mem v mtEnv).
Proof. intros. unfold mem. simpl. exact (Bool.diff_false_true). Qed.

Lemma beq_vid_sym : forall (v v' : vid),
  beq_vid v v' = beq_vid v' v.
Proof. intros. unfold beq_vid. apply NPeano.Nat.eqb_sym. Qed.

Lemma mem_bind : forall (v v' : vid) (t : term) (e : env),
  mem v e -> mem v (bind v' t e).
Proof.
  intros. unfold mem. unfold bmem. unfold try_lookup.
  unfold mem in H. unfold bmem in H. unfold try_lookup in H.
  destruct (beq_vid v v').
    reflexivity.
    exact H.
Qed.

Lemma mem_bind_same : forall (v v' : vid) (t : term) (e : env),
  beq_vid v v' = true -> mem v' (bind v t e).
Proof.
  intros. unfold beq_vid in H. apply beq_nat_true in H. rewrite H.
  unfold mem. unfold bmem. simpl. rewrite beq_vid_refl. reflexivity.
Qed.

Lemma mem_bind_diff : forall (v v' : vid) (t : term) (e : env),
  beq_vid v v' = false -> mem v (bind v' t e) -> mem v e.
Proof.
  intros. unfold mem in *. unfold bmem in *. unfold try_lookup in *.
  unfold beq_vid in *. rewrite H in H0. exact H0.
Qed.

Lemma mem_bind_same' : forall (v : vid) (t : term) (e : env),
  mem v (bind v t e).
Proof.
  intros. unfold mem. unfold bmem. simpl.
  rewrite beq_vid_refl. reflexivity.
Qed.

Lemma bmem_true : forall (v : vid) (e : env),
  bmem v e = true -> mem v e.
Proof. intros. unfold mem. exact H. Qed.

Lemma bmem_false : forall (v : vid) (e : env),
  bmem v e = false -> ~ (mem v e).
Proof.
  intros. unfold mem. destruct (bmem v e).
    inversion H.
    exact Bool.diff_false_true.
Qed.

Lemma lookup_bind : forall (v : vid) (t : term) (e : env),
  lookup v (bind v t e) = term_to_patt t.
Proof.
  intros. unfold lookup. unfold try_lookup.
  rewrite beq_vid_refl. reflexivity.
Qed.

Lemma lookup_bind_same : forall (v v' : vid) (t : term) (e : env),
  beq_vid v v' = true -> lookup v (bind v' t e) = term_to_patt t.
Proof.
  intros. unfold lookup. unfold try_lookup.
  rewrite H. reflexivity.
Qed.

Lemma lookup_bind_diff : forall (v v' : vid) (t : term) (e : env),
  beq_vid v v' = false -> lookup v (bind v' t e) = lookup v e.
Proof.
  intros. unfold lookup. unfold try_lookup.
  rewrite H. reflexivity.
Qed.

Lemma mem__subs_closed : forall (v : vid) (e : env),
  mem v e -> closed (e * (pvar v)).
Proof.
  intros. simpl.
  unfold mem in H. unfold bmem in H.
  unfold lookup. destruct (try_lookup v e).
  Case "v in e".
    apply term_to_patt_closed. inversion H.
Qed.

Lemma closed_subs : forall (p : patt) (e : env),
  closed p -> e * p = p.
Proof.
  intros. induction p.
  Case "var". inversion H.
  Case "node n nil". reflexivity.
  Case "node n (p :: ps)". simpl in *.
    inversion H; clear H.
    apply IHp in H0; clear IHp. rewrite H0.
    apply IHp0 in H1; clear IHp0. inversion H1.
      rewrite H2. rewrite H2. reflexivity.
Qed.



(**************************)
(*** Composition Lemmas ***)
(**************************)



Lemma compose_mtEnv_l : forall (e : env), mtEnv & e = Some e.
Proof. reflexivity. Qed.

Lemma compose_mtEnv_r : forall (e : env), e & mtEnv = Some e.
Proof.
  intros. induction e.
  Case "mtEnv". reflexivity.
  Case "bind v t e". simpl. rewrite IHe. reflexivity.
Qed.

Lemma bind_compose :
  forall (v : vid) (t : term) (e1 e2 e12: env),
  (bind v t e1) & e2 = Some e12 ->
  exists e12', e1 & e2 = Some e12' /\ e12 = bind v t e12'.
Proof.
  intros. unfold compose_env in H. fold compose_env in H.
  destruct (bmem v e2).
  Case "true". inversion H.
  Case "false". destruct (e1 & e2).
    SCase "Some e". exists e. split.
      reflexivity.
      inversion H. reflexivity.
    SCase "None". inversion H.
Qed.

Lemma compose_overlap : forall (e1 e2 : env) (v : vid),
  mem v e1 -> mem v e2 -> e1 & e2 = None.
Proof.
  intros.
  induction e1 as [ | v1 t e1].
  Case "mtEnv". simpl in *. inversion H.
  Case "bind v1 t1 e1". intros.
    unfold compose_env.
    destruct (bmem v1 e2) eqn:M; try reflexivity.
    fold compose_env.
    destruct (e1 & e2); try reflexivity.
    destruct (beq_vid v v1) eqn:V.
    SCase "v == v1".
      apply beq_vid_true in V; subst.
      apply bmem_false in M. elim M; apply H0.
    SCase "v != v1".
      apply (mem_bind_diff v v1 t e1) in V.
        apply IHe1 in V; inversion V.
        exact H.
Qed.

Lemma compose_not_member : forall (e1 e2 e12 : env) (v : vid),
  ~ (mem v e1) ->
  e1 & e2 = Some e12 ->
  lookup v e12 = lookup v e2.
Proof.
  intros.
  generalize dependent e12.
  induction e1 as [ | v1 t e1]; intros.
  Case "mtEnv".
    simpl in H0. inversion H0. reflexivity.
  Case "bind v1 t e1". intros.
    apply bind_compose in H0.
    elim H0; intros; rename x into e; clear H0.
    inversion H1; clear H1. subst.
    destruct (beq_vid v v1) eqn:V.
    SCase "v == v1".
      elim H. apply mem_bind_same. rewrite beq_vid_sym. exact V.
    SCase "v /= v1".
      rewrite lookup_bind_diff.
        apply IHe1; clear IHe1.
          intro. elim H. apply mem_bind. exact H1.
          exact H0.
        exact V.
Qed.

Lemma lookup_mtEnv : forall (v : vid), lookup v mtEnv = pvar v.
Proof. intros. compute. reflexivity. Qed.

Lemma lookup_not_member : forall (v : vid) (e : env),
  ~ (mem v e) -> lookup v e = pvar v.
Proof.
  intros.
  assert (e & mtEnv = Some e).
    rewrite compose_mtEnv_r. reflexivity.
  assert (lookup v e = lookup v mtEnv).
    apply compose_not_member with (e1 := e). exact H. exact H0.
  rewrite H1. rewrite lookup_mtEnv. reflexivity.
Qed.

Lemma compose_lookup_l : forall (e1 e2 e12 : env) (v : vid),
  mem v e1 ->
  e1 & e2 = Some e12 ->
  lookup v e12 = lookup v e1.
Proof.
  intros.
  generalize dependent e2. generalize dependent e12.
  induction e1 as [ | v1 t e1].
  Case "mtEnv".
    apply mem_mtEnv in H. inversion H.
  Case "bind v1 t1 e1". intros.
    apply bind_compose in H0.
    elim H0; intros; rename x into e; clear H0.
    inversion H1; clear H1. subst.
    destruct (beq_vid v v1) eqn:V.
    SCase "v == v1".
      rewrite (lookup_bind_same v v1 t e1 V).
      rewrite (lookup_bind_same v v1 t e V).
      reflexivity.
    SCase "v /= v1".
      rewrite (lookup_bind_diff v v1 t e1 V).
      rewrite (lookup_bind_diff v v1 t e V).
      apply IHe1 with (e2 := e2).
      apply mem_bind_diff with (v' := v1) (t := t).
        exact V. exact H. exact H0.
Qed.

Lemma compose_lookup_r : forall (e1 e2 e12 : env) (v : vid),
  mem v e2 ->
  compose_env e1 e2 = Some e12 ->
  lookup v e12 = lookup v e2.
Proof.
  intros.
  generalize dependent e2. generalize dependent e12.
  induction e1 as [ | v1 t e1].
  Case "mtEnv". intros.
    inversion H0. reflexivity.
  Case "bind v1 t e1". intros.
    destruct (beq_vid v v1) eqn:V.
    SCase "v == v1".
      assert (C : mem v (bind v1 t e1)).
        apply mem_bind_same. rewrite beq_vid_sym. exact V.
      apply compose_overlap
        with (e1:=bind v1 t e1) (e2:=e2) (v:=v) in C.
        rewrite C in H0; inversion H0.
        exact H.
    SCase "v /= v1".
      apply bind_compose in H0.
      elim H0; intros; rename x into e; clear H0.
      inversion H1; clear H1; subst.
      rewrite lookup_bind_diff.
        apply IHe1. exact H. exact H0.
        exact V.
Qed.

Lemma env_comm : forall (e1 e2 e12 e21 : env),
  e1 & e2 = Some e12 -> e2 & e1 = Some e21 -> e12 ~= e21.
Proof. 
  intros e1 e2 e12 e21 H12 H21 v.
  destruct (bmem v e1) eqn:V1; destruct (bmem v e2) eqn:V2;
    try apply bmem_true in V1; try apply bmem_true in V2.
  Case "v in e1, e2".
    assert (C : e1 & e2 = None).
      apply compose_overlap with (v := v). exact V1. exact V2.
    rewrite C in H12. inversion H12.
  Case "v in e1, not in e2".
    assert (L12 : lookup v e12 = lookup v e1).
      apply compose_lookup_l with (e2 := e2). exact V1. exact H12.
    assert (L21 : lookup v e21 = lookup v e1).
      apply compose_lookup_r with (e1 := e2). exact V1. exact H21.
    rewrite L12. rewrite L21. reflexivity.
  Case "v in e2, not in e1".
    assert (L12 : lookup v e12 = lookup v e2).
      apply compose_lookup_r with (e1 := e1). exact V2. exact H12.
    assert (L21 : lookup v e21 = lookup v e2).
      apply compose_lookup_l with (e2 := e1). exact V2. exact H21.
    rewrite L12. rewrite L21. reflexivity.
  Case "v not in e1, e2".
    apply bmem_false in V1.
    apply bmem_false in V2.
    assert (L12 : lookup v e12 = lookup v e2).
      apply compose_not_member with (e1 := e1). exact V1. exact H12.
    assert (L21 : lookup v e21 = lookup v e1).
      apply compose_not_member with (e1 := e2). exact V2. exact H21.
    assert (L1 : lookup v e1 = pvar v).
      apply lookup_not_member. exact V1.
    assert (L2 : lookup v e2 = pvar v).
      apply lookup_not_member. exact V2.
    rewrite L12. rewrite L21. rewrite L1. rewrite L2. reflexivity.
Qed.

Lemma env_subs_comm : forall (e1 e2 e12 : env) (p : patt),
  e1 & e2 = Some e12 ->
  e12 * p = e1 * (e2 * p).
Proof.
  intros. induction p.
  Case "var v".
    destruct (bmem v e1) eqn:V1; destruct (bmem v e2) eqn:V2;
      try apply bmem_true in V1; try apply bmem_true in V2.
    SCase "v in e1, e2".
      assert (C : e1 & e2 = None).
        apply compose_overlap with (v := v). exact V1. exact V2.
      rewrite C in H. inversion H.
    SCase "v in e1, not in e2".
      simpl. apply bmem_false in V2.
      assert (L2 : lookup v e2 = pvar v).
        apply lookup_not_member. exact V2.
      assert (L12 : lookup v e12 = lookup v e1).
        apply compose_lookup_l with (e2 := e2). exact V1. exact H.
      rewrite L2. rewrite L12. simpl. reflexivity.
    SCase "v in e2, not in e1".
      simpl. apply bmem_false in V1.
      assert (L12 : lookup v e12 = lookup v e2).
        apply compose_lookup_r with (e1 := e1). exact V2. exact H.
      assert (G : closed (lookup v e2)).
        apply mem__subs_closed. exact V2.
      apply closed_subs with (e := e1) in G.
      rewrite G. rewrite L12. reflexivity.
    SCase "v not in e1, e2".
      simpl. apply bmem_false in V1. apply bmem_false in V2.
      assert (L12 : lookup v e12 = lookup v e2).
        apply compose_not_member with (e1 := e1). exact V1. exact H.
      assert (L2 : lookup v e2 = pvar v).
        apply lookup_not_member. exact V2.
      assert (L1 : lookup v e1 = pvar v).
        apply lookup_not_member. exact V1.
      rewrite L12. rewrite L2. simpl. rewrite L1. reflexivity.
  Case "node n nil".
    reflexivity.
  Case "node n (t :: ts)".
    simpl. rewrite IHp.
    inversion IHp0. rewrite H1.
    reflexivity.
Qed.
