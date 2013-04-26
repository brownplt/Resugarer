

(* A "Module Type" is a _signature_; It has the form
     {var : type, var : type, ...}
   You can define one like this. *)
Module Type SIG.
  Parameter t : Type.
  Parameter f : t -> t.
End SIG.

(* A "Module" is a _record_. It has the form
     {var : type := value, var : type := value, ...}
   You can make an _instance_ of a Module Type.
   The instance is a Module, and the types of its variables must
     be subtypes of the Module Type's variable types. *)
Module Mod <: SIG.
  Definition t := nat.
  Definition f := fun (x : nat) => 1 + x.
  (* Putting x := fun (x : nat * nat) => x would fail here. *)
End Mod.

(* Q: Why can a Module contain a parameter? *)

(* A Module can _import_ a Module Type to use the things it defines.
   A Module that imports things is called a _Functor_.
   It's really a function, e.g. forall (Impl : SIG) -> SIG_TWICE. *)
Module SIG_TWICE (Import Impl : SIG).
  Definition xx := fun (x : t) => f (f x).
End SIG_TWICE.

(* To "call" this Functor, use f(x, y) notation.
   Both the forms `Module M := ~.` and `Module M. ~ End M.`
     are used to define a module named M,
     but they allow different things in the body ~. *)
Module ModTwice := SIG_TWICE(Mod).

(* A module defined this way can be imported,
   putting the things it defines into the local namespace. *)
Import ModTwice.
Lemma L : forall (n : nat), xx n = 2 + n.
Proof. intros. reflexivity. Qed.
