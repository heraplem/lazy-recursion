From ExtLib Require Import
  Structures.Monoid
  Structures.Monad
.
From ITree Require Import
  Events.Writer
.
From Lazy Require Import
  Base
.

Variant tickE : Type -> Type :=
| Tick : tickE unit
.

Definition tick (E : Type -> Type) `{tickE -< E} : itree E unit :=
  trigger Tick
.

Definition handle_tick_to_writerT {E : Type -> Type} {W : Type} (w : W) :
  tickE ~> writerT W (itree E) :=
  fun _ e => match e with
          | Tick => Ret (w, tt)
          end
.

Polymorphic Definition run_tick_to_writerT {E : Type -> Type} {W : Type} (MW : Monoid W) (w : W) :
  itree (tickE +' E) ~> writerT W (itree E) :=
  interp_writer MW (case_sum1 (handle_tick_to_writerT w) (pure_writer MW))
.

Definition run_tick_to_writerT_nat_sum {E : Type -> Type} :
  itree (tickE +' E) ~> writerT nat (itree E) :=
  run_tick_to_writerT nat_sum_monoid 1
.

From Coq Require Import Program.Tactics Morphisms.
From ITree Require Import StateFacts.

Lemma eutt_run_tick_to_writerT (E : Type -> Type) (W : Type) (MW : Monoid W) (w : W) (T : Type) :
  Proper (eutt (R1 := T) (R2 := T) eq ==> eutt eq) (run_tick_to_writerT (E := E) MW w (T := T)).
Proof.
  repeat intro. unfold run_tick_to_writerT, interp_writer. rewrite H. reflexivity.
Qed.
