From Coq Require Import Ensembles.
From ITree Require Import Props.Leaf.
From Lazy Require Import Base Events.Fail.

Definition returns_some {E : Type -> Type} : itree (failE +' E) ~> Ensemble :=
  fun _ t x => Leaf (Some x) (run_fail_to_itree t)
.

(* From Coq Require Import Ensembles. *)
(* From ITree.Events Require Import FailFacts Nondeterminism. *)
(* From Lazy Require Import Base Events.Fail. *)

(* (* maybe show conditional equivalence with: *)

(* interp (h : forall x, e x -> x -> Prop) (t : itree e a) : a -> Prop *)
(* interp h (Vis e k) r = exists x, h e x /\ k x r *)

(* *) *)

(* Inductive returns (E : Type -> Type) (A : Type) : itree E A -> Ensemble A := *)
(* | returns_Ret : forall {a}, returns (Ret a) a *)
(* | returns_Tau : forall {t a}, returns t a -> returns (Tau t) a *)
(* | returns_Vis : forall {X} {e : E X} {k : X -> itree E A} {a : A}, *)
(*     (exists x, returns (k x) a) -> returns (Vis e k) a *)
(* . *)

(* From Paco Require Import paco. *)
(* (* From ITree Require Import ITree  *) *)

(* Section ReturnsEutt. *)
(*   Context {E : Type -> Type} {A : Type}. *)

(*   (* Core inversion lemma: chase Tau's on the right when the left side *)
(*      is already headed by Ret or Vis. Proved by unfolding eutt and *)
(*      inducting on the eqitF derivation. *) *)
(*   Lemma returns_eutt_head (t t' : itree E A) (x : A) : *)
(*     t ≈ t' -> *)
(*     (forall a, t = Ret a -> a = x -> returns t' x) /\ *)
(*     (forall X (e : E X) k, *)
(*         t = Vis e k -> *)
(*         (exists y, returns (k y) x) -> *)
(*         returns t' x). *)
(*   Proof. *)
(*     intros H. punfold H. red in H. *)
(*     hinduction H before A; intros; subst; try discriminate; *)
(*       split; intros; subst; try discriminate. *)
(*     - (* EqRet *) *)
(*       injection H0 as ->; subst. *)
(*       constructor. *)
(*     - (* EqRet, Vis branch is vacuous here *) *)
(*       discriminate. *)
(*     - (* EqVis, Ret branch vacuous *) *)
(*       discriminate. *)
(*     - (* EqVis *) *)
(*       injection H0 as -> -> ->. *)
(*       pclearbot. *)
(*       destruct H1 as [y Hy]. *)
(*       econstructor; eexists. *)
(*       eapply IHk; eauto.  (* uses that Hy : returns (k y) x together *)
(*                               with REL y : k y ≈ k' y, by the outer IH *) *)
(*     - (* EqTauL: t = Tau t1, contradicts t = Ret a / Vis e k *) *)
(*       discriminate. *)
(*     - (* EqTauR: peel a Tau off t', recurse, then re-wrap with returns_Tau *) *)
(*       pclearbot. *)
(*       constructor. *)
(*       eapply IHeqitF; eauto. *)
(*   Qed. *)

(*   Lemma returns_eutt_mp (t t' : itree E A) (x : A) : *)
(*     t ≈ t' -> returns t x -> returns t' x. *)
(*   Proof. *)
(*     intros Heutt Hret. revert t' Heutt. *)
(*     induction Hret; intros t' Heutt. *)
(*     - eapply returns_eutt_head; eauto. *)
(*     - apply IHHret. now rewrite tau_eutt in Heutt. *)
(*     - eapply returns_eutt_head; eauto. *)
(*   Qed. *)

(*   Lemma returns_eutt (t t' : itree E A) (x : A) : *)
(*     t ≈ t' -> returns t x <-> returns t' x. *)
(*   Proof. *)
(*     split; [apply returns_eutt_mp | apply returns_eutt_mp; symmetry]; auto. *)
(*   Qed. *)

(* End ReturnsEutt. *)
(* returns (run_fail_to_itree t) (Some x) *)
(* . *)
