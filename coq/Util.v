Require Import Coq.Lists.List.

Definition applyOpt {a b : Type} (f : a -> option b) (x : option a) : option b :=
  match x with
    | None => None
    | Some x => f x
  end.

Notation "x <- y ; z" := (applyOpt (fun x => z) y)
  (at level 65, right associativity).

Definition composeOpt {a b c : Type}
  (f : a -> option b) (g : b -> option c) : a -> option c :=
  fun x : a =>
    match f x with
      | None => None
      | Some y => g y
    end.

Fixpoint sequenceOpts {a : Type}
  (l : list (option a)) : option (list a) :=
  match l with
    | nil => Some nil
    | None :: _ => None
    | Some x :: l =>
      match sequenceOpts l with
        | None => None
        | Some xs => Some (x :: xs)
      end
  end.

Fixpoint mapOpt {a b : Type}
  (f : a -> option b) (l : list a) : option (list b) :=
  match l with
    | nil => Some nil
    | x :: xs =>
      match f x with
        | None => None
        | Some y =>
          match mapOpt f xs with
            | None => None
            | Some ys => Some (y :: ys)
          end
      end
  end.

Fixpoint mapOpt2 {a b c : Type}
  (f : a -> b -> option c) (l1 : list a) (l2 : list b) : option (list c) :=
  match (l1, l2) with
    | (nil, nil) => Some nil
    | (nil, _) => None
    | (_, nil) => None
    | (x :: xs, y :: ys) =>
      match f x y with
        | None => None
        | Some z =>
          match mapOpt2 f xs ys with
            | None => None
            | Some zs => Some (z :: zs)
          end
      end
  end.
