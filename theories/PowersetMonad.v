From ExtLib.Structures Require Import Monad.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Section PowersetType.

  Variable m : Type -> Type.
  Context `{M : Monad m}.

  Record powersetT (a : Type) : Type := mkPowersetT
    { runPowersetT : m a -> Prop }.

  Program Instance Monad_powersetT : Monad powersetT :=
    { ret := fun _ x => mkPowersetT (fun u => ret x = u)
    ; bind := fun _ _ t k => _
    }.
  Obligation 1.
  intros.
  apply mkPowersetT.
  intro v.
  refine (exists u : m T, _ /\ _).
  eapply runPowersetT.
  exact t.
  exact u.
