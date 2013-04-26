
Definition mid := nat.
Definition var := nat.

Definition Pmatch (patt env : Type) :=
  patt -> patt -> option env.

Definition Subs (patt env : Type) :=
  env -> patt -> patt.

Definition Lensy (patt env : Type)
  (pmatch : Pmatch patt env)
  (subs : Subs patt env) : Prop :=
    forall (p q : patt) (e : env),
      pmatch p q = Some e -> subs e q = p.


Inductive temp {patt : Type} :=
| tpatt : patt -> temp
| tlet : var -> mid -> temp -> temp.

Inductive macro {patt : Type} :=
| mnil : macro
| mcons : patt -> patt -> macro -> macro.

Inductive dict {patt : Type} :=
| mtdict : dict
| bind : mid -> @macro patt -> dict -> dict.

Inductive expand {patt env : Type}
  {pmatch : Pmatch patt env}
  {subs : Subs patt env}
  {lensy : Lensy patt env pmatch subs}
  (m : @macro patt) (t : patt) (t' : option patt) (n : nat) :=
| expand_nil : m = mnil -> t' = None -> n = 0 ->
  expand m t t' n
| expand_car (p q : patt) (e : env) (m' : macro) :
  m = mcons p q m' -> pmatch t p = Some e -> t' = Some (subs e q) -> n = 0 ->
  expand m t t' n
| expand_cdr (p q : patt) (e : env) (m' : macro) (n' : nat) :
  m = mcons p q m' -> pmatch t p = None -> expand m' t t' n' -> n = S n' ->
  expand m t t' n.

Inductive unexpand {patt env : Type}
  {pmatch : Pmatch patt env}
  {subs : Subs patt env}
  {lensy : Lensy patt env pmatch subs}
  (m : @macro patt) (n : nat) (t : patt) (t' : option patt) :=
| unexpand_nil : m = mnil -> t' = None ->
  unexpand m t t'
| unexpand_car (p q : patt) (e : env) (m' : macro) :
  m = mcons p q m' -> pmatch t q = Some e -> t' = Some (subs e p) ->
  unexpand m t t'
| unexpand_cdr (p q : patt) (e : env) (m' : macro) :
  m = mcons p q m' -> pmatch t q = None -> unexpand m' t t' ->
  unexpand m t t'.

Theorem MacroLens : forall (m : macro) (t t' : patt),
  expand m t (Some t') -> 

Check expand_base.

| expand_rec : m = mcons p q _ -> (

Check foo.
