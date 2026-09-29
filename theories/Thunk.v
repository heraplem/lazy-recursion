From Lazy Require Import
  Base
.

Inductive T (A : Type) : Type :=
| Undefined : T A
| Thunk : A -> T A
.
Arguments Undefined {A}.
Arguments Thunk {A}.
