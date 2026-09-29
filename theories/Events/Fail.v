From ITree Require Import
  Events.FailFacts
.
From Lazy Require Import
  Base
.

Variant failE (A : Type) : Type :=
| Fail : failE A
.
Arguments Fail {A}.

Definition fail {E : Type -> Type} `{failE -< E} {A : Type} : itree E A :=
  trigger Fail
.

Definition handle_fail {M : Type -> Type} `{Monad M} : failE ~> failT M :=
  fun _ e => match e with
          | Fail => ret None
          end
.

Definition run_fail {E M : Type -> Type} `{Monad M} `{MonadIter M} (h : E ~> M) :
  itree (failE +' E) ~> failT M :=
  interp_fail (case_sum1 handle_fail (fun _ e => fmap Some (h _ e)))
.

Definition run_fail_to_itree {E : Type -> Type} : itree (failE +' E) ~> failT (itree E) :=
  run_fail (M := itree E) (fun _ e => trigger e)
.
