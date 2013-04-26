Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Util.
Require Import Cases.
Require Import Patt.
Require Import Env.


Inductive macro :=
| transf : patt -> patt -> macro.

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

(* Should return term? *)
Definition expand (m : macro) (t : term) : option patt :=
  match m with
    | transf p q =>
      e <- t / p;
      Some (e * q)
  end.

Definition unexpand (m : macro) (s t : term) : option patt :=
  match m with
    | transf p q =>
      e1 <- t/q;
      e2 <- s/p;
      Some (e1*(e2*p))
  end.


Lemma pmatch_subs : forall (t : term) (p : patt) (e : env),
  t / p = Some e -> e * p = term_to_patt t.
Proof.
  intros. generalize dependent e. generalize dependent t.
  induction p as [v | np | np p ps]; intros; simpl.
  Case "p = var".
    simpl in H. inversion H.
    rewrite lookup_bind. reflexivity.
  Case "p = node np nil".
    destruct t as [nt ts].
    simpl in H. destruct (negb (beq_nid np nt)) eqn:N. inversion H.
    destruct ts.
    SCase "ts = nil".
      inversion H. simpl. apply Bool.negb_false_iff in N.
      apply beq_nid_true in N. rewrite N. reflexivity.
    SCase "ts = t :: ts".
      inversion H.
  Case "p = node n (p :: ps)".
    destruct t as [nt ts].
    destruct (negb (beq_nid np nt)) eqn:N.
      inversion H. rewrite N in H1. inversion H1.
    destruct ts.
    SCase "ts = nil".
      inversion H. rewrite N in H1. inversion H1.
    SCase "ts = t :: ts".
      apply Bool.negb_false_iff in N.
      apply beq_nid_true in N; subst.
      simpl.
        
      
    
    

    destruct ts.
    SCase "t = node n' nil".
      inversion H. destruct (negb (beq_nid np nt)); inversion H1.
    SCase "t = node n' (t :: ts)".
      
      
    unfold pmatch in H. fold pmatch in H.
    apply IHp0 in H.
  
  


(*
Theorem lens1 : forall (m : macro) (t t' : term),
  t' <- expand m t; unexpand m t t' = Some t. *)









Lemma subs_node : forall (e : env) (n : nid) (ps : list term),
  e * (node n ps) = node n (map (fun t => e * t) ps).
Proof. intros. reflexivity. Qed.

Lemma subs_cons :
  forall (e : env) (n : nid) (p : term) (ps : list term),
    e * (node n (p :: ps))
    = node n (e * p :: map (fun t => e * t) ps).
Proof. intros. reflexivity. Qed.

Lemma divide_cons :
  forall (e1 e2 : env) (n : nid) (t p : term) (ts ps : list term),
    t / p = Some e1 ->
    (node n ts) / (node n ps) = Some e2 ->
    (node n (t :: ts)) / (node n (p :: ps)) = compose_env e1 e2.
Proof.
  intros. simpl. inversion H0. rewrite beq_nid_refl in *.
  rewrite H. simpl. simpl in H2. rewrite H2. reflexivity.
Qed.

Lemma lookup_compose_comm : forall (v : vid) (e1 e2 e12 e21 : env),
  compose_env e1 e2 = Some e12 ->
  compose_env e2 e1 = Some e21 ->
  lookup v e12 = lookup v e21.
Proof. intros. induction e1.

Lemma compose_subs_comm : forall (e1 e2 e12 : env) (t : term),
    compose_env e1 e2 = Some e12 -> e12 * t = e1 * (e2 * t).
Proof.
  intros. generalize dependent e12. induction e1 as [ | v1 t1 e1].
  Case "mtEnv". intros. simpl in H. inversion H.
    rewrite mtEnv_mult_l. reflexivity. intros.
    
  Case "bind v1 t1 e1". induction t. intros.
    SCase "var v". simpl. simpl in IHe1


Lemma match_subs_node : forall (ts : list term),
  Forall (fun (t : term) =>
    (forall (p : term) (e : env), t / p = Some e -> e * p = t))
    (ts : list term)
  ->
    (forall (n : nid) (ps : list term) (e : env),
      (node n ts) / (node n ps) = Some e -> e * (node n ps) = (node n ts)).
Proof.
  induction ts as [ | t ts]; intros; simpl in H0;
    rewrite beq_nid_refl in H0; simpl in H0; destruct ps as [ | p ps].
  Case "nil".
    SCase "nil". inversion H0. simpl. reflexivity.
    SCase "p :: ps". inversion H0.
  Case "t :: ts".
    SCase "nil". inversion H0.
    SCase "p :: ps". inversion H. clear H. subst.
      rename H3 into Ht. rename H4 into Hts.
      remember (IHts Hts) as H; clear HeqH IHts Hts; rename H into Hts.
      destruct (t / p).
      SSCase "Some e0". simpl in H0.
        unfold subs.
      SSCase "None". simpl in H0. inversion H0.
      

Lemma match_subs : forall (t p : term) (e : env),
  t / p = Some e -> e * p = Some t.
Proof.
  induction t; intros.
  Case "var". destruct p as [v' | n ps].
    SCase "var". simpl in H. inversion H. simpl.
      rewrite beq_vid_refl; reflexivity.
    SCase "node". simpl in H. inversion H.
  Case "node". rename H into IHt. rename H0 into H.
    destruct p as [v' | n' ps].
    SCase "var". simpl in H. inversion H. simpl.
      rewrite beq_vid_refl; reflexivity.
    SCase "node". simpl in H. destruct (negb (beq_nid n' n)) eqn:N.
      SSCase "true". inversion H.
      SSCase "false". destruct ts as [ | t ts].
        SSSCase "nil". destruct ps as [ | p ps].
          SSSSCase "nil". inversion H. simpl. f_equal. f_equal.
            unfold beq_nid in N. rewrite Bool.negb_false_iff in N.
            symmetry in N. apply beq_nat_eq in N. exact N.
          SSSSCase "p :: ps". inversion H.
        SSSCase "t :: ts". destruct ps as [ | p ps].
          SSSSCase "nil". inversion H.
          SSSSCase "p :: ps". (* Now what? *)
            unfold beq_nid in N. rewrite Bool.negb_false_iff in N.
            symmetry in N. apply beq_nat_eq in N. rewrite N.
            

destruct (divide t p) as [e' | ].
            SSSSSCase "Some e'".

inversion IHt.
              remember (H2 p) as V. clear HeqV.
              
            
        SSSCase "t :: ts". destruct ps as [ | p ps]. 
    SCase "node". destruct ts as [ | t ts].
      SSCase "nil". destruct ps as [ | p ps].
        SSSCase "nil". simpl in H. destruct (beq_nid n' n) eqn:N.
          SSSSCase "true". simpl in H. inversion H.
            unfold beq_nid in N.
            symmetry in N. apply beq_nat_eq in N.
            rewrite N. reflexivity.
          SSSSCase "false". simpl in H. inversion H.
        SSSCase "p :: ps". simpl in H.
          destruct (negb (beq_nid n' n)); inversion H.
      SSCase "t :: ts". induction ps as [ | p ps].
        SSSCase "nil". simpl in H.
          destruct (negb (beq_nid n' n)); inversion H.
        SSSCase "p :: ps". simpl in H.
          destruct (negb (beq_nid n' n)).
            SSSSCase "true". inversion H.
            SSSSCase "false". destruct (divide t p) as [e1 | ].
              SSSSSCase "Some e1".
            
          
      destruct (beq_vid v0 v) eqn:E.
      SSCase "eq". simpl. repeat f_equal. unfold beq_vid in E.
        symmetry in E; apply beq_nat_eq in E. assumption.
      SSCase "neq". 
    
  intros. induction p using patt_ind'.
  Case "var". simpl in *. inversion H. simpl.
    rewrite <- beq_nat_refl. reflexivity.
  Case "node". simpl in *. destruct t as [l' ts].
    destruct (beq_nid l l').

(*
Fixpoint subs (e : env) (t : term) : option term :=
  match t with
    | var v => lookup v e
    | node n ts =>
      match mapOpt (subs e) ts with
        | None => None
        | Some ts => Some (node n ts)
      end
  end.
  "Error: Cannot guess decreasing argument of fix."

(*
Fixpoint subs (t : term) (e : env) : option term :=
  let subss := fix subss (ts : list term) : option (list term) :=
    match ts with
      | nil => Some nil
      | t :: ts =>
        match subs t e with
          | None => None
          | Some t =>
            match subss ts with
              | None => None
              | Some ts => Some (t :: ts)
            end
        end
    end in
  match t with
    | var v => lookup v e
    | node n ts =>
      match subss ts with
        | None => None
        | Some ts => Some (node n ts)
      end
  end. *)

Inductive ForallType {A : Type} {P : A -> Type}: list A -> Type :=
    | ForallType_nil : ForallType nil
    | ForallType_cons : forall {x : A} {l : list A},
                     P x -> ForallType l -> ForallType (x :: l).

Definition term_rect := fun
  (P : term -> Type)
  (h : forall (v : vid), P (var v))
  (f : forall (n : nid) (ts : list term), ForallType ts -> P (node n ts))
  (p : term)
  =>
  fix term_rec (p : term) : P p :=
    match p return P p with
      | var v => h v
      | node n ps =>
      f n ps ((fix terms_rec (ps : list term) : ForallType ps :=
        match ps with
          | nil => ForallType_nil
          | p :: ps => ForallType_cons (term_rec p) (terms_rec ps)
        end) ps)
    end.

(*
Fixpoint divide (t : term) (p : term) : option env :=
  match p with
    | var v => Some (bind v t mtEnv)
    | node l ps =>
      match t with
        | var v => None
        | node l' ts =>
          if beq_nid l l'
            then dividees ts ps
            else None
      end
  end
with dividees (ts : list term) (ps : list term) : option env :=
  match (ts, ps) with
    | (nil, nil) => Some mtEnv
    | (nil, _) => None
    | (_, nil) => None
    | (t :: ts, p :: ps) =>
      match divide t p with
        | None => None
        | Some e =>
          match dividees ts ps with
            | None => None
            | Some e' => Some (compose_env e e')
          end
      end
  end.
  Error: Cannot guess decreasing argument of fix.
*)
