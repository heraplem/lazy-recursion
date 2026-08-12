From ExtLib.Data.Monads Require Import WriterMonad.
From ExtLib.Structures Require Import Monoid Functor Monad MonadWriter.

From ITree Require Import ITree Eq.
From ITree.Events Require Import Exception Nondeterminism Writer.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Open Scope type_scope.

(* The following definitions are taken from "Modular, Compositional, and
   Executable Formal Semantics for LLVM IR". *)

Inductive returns {E A} : itree E A -> A -> Prop :=
| returns_ret : forall {t a}, eutt eq t (ret a) -> returns t a
| returns_tau : forall {t a u}, eutt eq t (Tau u) -> returns u a -> returns t a
| returns_vis : forall {B t} {e : E B} {k a}, eutt eq t (Vis e k) -> (exists b, returns (k b) a) -> returns t a
.

Definition propT (E : Type -> Type) (A : Type) : Type :=
  itree E A -> Prop
.

(* In the bind constructor, the original paper gives k2 the type C -> itree E B,
   but it should certainly be C -> itree F B. *)
CoInductive interp_prop {A B E F} (R : A -> B -> Prop) (h : E ~> propT F) :
  itree E A -> itree F B -> Prop :=
| interp_prop_ret : forall {t2 r1 r2}, R r1 r2 -> eutt eq t2 (ret r2) -> interp_prop R h (Ret r1) t2
| interp_prop_tau : forall {t1 t2}, interp_prop R h t1 t2 -> interp_prop R h t1 (Tau t2)
| interp_prop_bind : forall {C e a t2 tc k1} {k2 : C -> itree F B},
    h _ e tc ->
    eutt eq t2 (bind tc k2) ->
    (forall c, returns tc c -> interp_prop R h (k1 a) (k2 c))
    -> interp_prop R h (Vis e k1) t2
.

Definition sum_mon : Monoid nat :=
  {| monoid_plus := plus
  ;  monoid_unit := O
  |}.

Inductive T (A : Type) : Type :=
| Undefined : T A
| Thunk : A -> T A
.

Inductive tickE : Type -> Type :=
| Tick : tickE unit
.

(* Inductive lazyE (A : Type) : Type := *)
(* | LazyE : forall {A}, itree E A -> lazyE (T A) *)
(* | ForceE : forall {A}, T A -> lazyE A *)
(* . *)

(* Definition tick (E : Type -> Type) `{writerE nat -< E} : itree E unit := *)
(*   tell 1 *)
(* . *)

Definition tick (E : Type -> Type) `{tickE -< E} : itree E unit :=
  trigger Tick
.

Definition h_tick (E : Type -> Type) : tickE ~> writerT sum_mon (itree E) :=
  fun _ e => match e with
          | Tick => MonadWriter.tell 1
          end
.

(* XXX Nondeterminism is a problem ... there should be an interpreter somewhere
   in the ITree library. *)
Definition thunk (E : Type -> Type) (A : Type) `{nondetE -< E} (u : itree E A) : itree E (T A) :=
  or (ret Undefined) (fmap Thunk u)
.

(* XXX When interpreting, it matters where the exception effect is in the effect
   row! *)
Definition forcing (E : Type -> Type) (A B : Type) `{nondetE -< E} `{exceptE no_choice -< E} (t : T A) (f : A -> itree E B) : itree E B :=
  match t with
  | Thunk v => f v
  | Undefined => throw NoChoice
  end
.

Definition force (E : Type -> Type) (A : Type) `{nondetE -< E} `{exceptE no_choice -< E} (t : T A) : itree E A :=
  forcing t ret
.

(* Definition handle_effects {E : Type -> Type} {A : Type} : *)
(*   itree (tickE + nondetE + exceptE no_choice) A -> *)
(*   (itree void (A * nat) -> Prop). *)

(* Fixpoint take (A : Type) (n : nat) (l : list A) :  *)

(* Use the paco library to model coinductive data *)
(* or look at what choice trees are using *)
CoInductive colist (A : Type) :=
| conil : colist A
| cocons : A -> colist A -> colist A
.

(* cofindE is an effect representing a call to the cofind function.  We
   introduce it locally, handle it using h_cofind, and then eliminate it using
   cofind (via mrec).  See "Interaction Trees" for an explanation of this
   approach to representing recursive functions; they demonstrate it using the
   Ackermann function.  The technique is ultimately due to McBride. *)

Inductive cofindE (A : Type) : Type -> Type :=
| Cofind : nat -> colist A -> cofindE A bool
.

Import MonadNotation.
Open Scope monad_scope.
Definition h_cofind (E : Type -> Type) `{tickE -< E} `{nondetE -< E} `{exceptE no_choice -< E} :
  cofindE nat ~> itree (cofindE nat +' E) :=
  fun _ e => match e with
          | Cofind n c =>
              tick ;;
              match c with
              | conil => ret false
              | cocons n' c' =>
                  bT <- thunk (trigger (Cofind n c')) ;;
                  if (Nat.eqb n n') then ret true else force bT
              end
          end
.

Definition cofind {E} `{tickE -< E} `{nondetE -< E} `{exceptE no_choice -< E}
  (n : nat) (c : colist nat) : itree E bool :=
  mrec (fun _ e => h_cofind e) (Cofind n c)
.
