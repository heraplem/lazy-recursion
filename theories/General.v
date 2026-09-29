From gitrees Require Import gitree.

Inductive T (A : Type) : Type :=
| Undefined : T A
| Thunk : A -> T A
.

Module LazyForce.
  Parameter A : Type.
  Notation AO := (leibnizO A).

  Program Definition forceE (A : Type) : opInterp :=
    {|
      Ins := AO;
      Outs := AO;
    |}.
End LazyForce.
