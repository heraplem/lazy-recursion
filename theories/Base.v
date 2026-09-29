Global Set Implicit Arguments.
Global Set Contextual Implicit.
Global Unset Automatic Proposition Inductives.

From ExtLib Require Export
  Structures.Monoid
  Structures.Functor
  Structures.Monad
.
From ITree Require Export
  ITree
  Eq
  CategoryOps
.
From ITree Require Import
  Events.Writer
  Events.State
.
Export
  ITree.Basics.Basics.Monads
.

(* The monoid (ℕ, +, 0). *)
Polymorphic Definition nat_sum_monoid : Monoid nat :=
  {| monoid_plus := Nat.add
  ;  monoid_unit := O
  |}
.
#[global] Polymorphic Instance nat_sum_monoid_laws : MonoidLaws nat_sum_monoid.
Proof.
  constructor; red; cbn; intros; auto using PeanoNat.Nat.add_assoc, PeanoNat.Nat.add_0_r.
Qed.

(* Reinterpret an effect at the front of the effect row. *)
Definition reinterp {E1 E1' E2 : Type -> Type} (h : E1 ~> itree (E1' +' E2))
  : itree (E1 +' E2) ~> itree (E1' +' E2) :=
  interp (case_sum1 (fun _ => h _) inr_)
.

(* The missing Functor and Monad instances for writerT. *)
#[global] Instance Functor_writerT {M : Type -> Type} {FM : Functor M} {W : Type}
  : Functor (writerT W M) :=
  {|
    fmap _ _ f := fmap (fun '(w, a) => (w, f a))
  |}
.
#[global] Instance Monad_writerT {M : Type -> Type} {MM : Monad M} {W : Type} {MW : Monoid W}
  : Monad (writerT W M) :=
  {|
    ret _ x := ret (monoid_unit MW, x)
  ; bind _ _ m k := @bind M _ _ _ m
                      (fun '(w, x) => @bind M _ _ _ (k x)
                                     (fun '(w', x') => ret (monoid_plus MW w w', x')))
  |}
.

(* Drop-in universe-polymorphic replacements for some ITrees functions. *)
Polymorphic Definition handle_writer {W : Type} {E : Type -> Type} (Monoid_W : Monoid W)
  : writerE W ~> stateT W (itree E)
  := fun _ e s =>
       match e with
       | Tell w => Ret (monoid_plus Monoid_W s w, tt)
       end
.
Polymorphic Definition run_writer {W E} (Monoid_W : Monoid W)
  : itree (writerE W +' E) ~> writerT W (itree E)
  := fun _ t =>
       interp_state (M := itree E)
         (case_ (handle_writer Monoid_W) pure_state) t
         (monoid_unit Monoid_W).

(* Interpretation with writerT handlers.  ITrees has no MonadIter instance or
   interpretation theory for writerT, so, like ITrees' own run_writer, we thread
   the accumulated output as state; this lets us reuse StateFacts. *)
Polymorphic Definition writer_to_state {W : Type} {E F : Type -> Type} (Monoid_W : Monoid W)
  (h : E ~> writerT W (itree F))
  : E ~> stateT W (itree F)
  := fun _ e s => ITree.map (fun '(w, x) => (monoid_plus Monoid_W s w, x)) (h _ e)
.
Polymorphic Definition interp_writer {W : Type} {E F : Type -> Type} (Monoid_W : Monoid W)
  (h : E ~> writerT W (itree F))
  : itree E ~> writerT W (itree F)
  := fun _ t => interp_state (writer_to_state Monoid_W h) t (monoid_unit Monoid_W)
.
(* The writerT analogue of pure_state: re-emit the event, writing nothing. *)
Polymorphic Definition pure_writer {W : Type} {E : Type -> Type} (Monoid_W : Monoid W)
  : E ~> writerT W (itree E)
  := fun _ e => ITree.map (fun x => (monoid_unit Monoid_W, x)) (trigger e)
.
