(* Equational theory for interp_writer, in writer style: every computation runs
   from monoid_unit, and bind combines outputs with monoid_plus. *)

From Coq Require Import Morphisms.
From ExtLib Require Import Structures.BinOps.
From ITree Require Import Events.State Events.StateFacts.
From Paco Require Import paco.
From Lazy Require Import Base.

(* interp_writer is universe polymorphic, so lemmas about it must be too, or
   they only apply at the universe levels fixed here. *)
Set Universe Polymorphism.

Section WriterFacts.
  Context {W : Type} (MW : Monoid W) {MWL : MonoidLaws MW}.
  Context {E F : Type -> Type} (h : E ~> writerT W (itree F)).

  Local Notation "a + b" := (monoid_plus MW a b).
  Local Notation "0" := (monoid_unit MW).

  (* Prefix every output of a writer computation with w. *)
  Local Notation shift w := (ITree.map (fun '(w', x) => (w + w', x))).

  (* The shifting lemma: running from state s1 + s2 is running from s2 and
     prefixing s1 to the output.  Needs associativity. *)
  Lemma interp_state_writer_shift {R} (t : itree E R) s1 s2 :
    interp_state (writer_to_state MW h) t (s1 + s2)
    ≅ shift s1 (interp_state (writer_to_state MW h) t s2).
  Proof.
    revert t s2. ginit. gcofix CIH. intros t s2.
    rewrite !unfold_interp_state. unfold ITree.map.
    destruct (observe t) as [x | t' | X e k]; cbn.
    - rewrite bind_ret_l. apply reflexivity.
    - rewrite bind_tau. gstep. constructor. gbase. apply CIH.
    - unfold writer_to_state, ITree.map. rewrite !bind_bind.
      guclo eqit_clo_bind. econstructor; [reflexivity |].
      intros [w x] ? <-. rewrite !bind_ret_l, bind_tau. cbn.
      gstep. constructor. rewrite monoid_assoc. gbase. apply CIH.
  Qed.

  Lemma interp_state_writer {R} (t : itree E R) s :
    interp_state (writer_to_state MW h) t s ≅ shift s (interp_writer MW h t).
  Proof.
    unfold interp_writer. rewrite <- interp_state_writer_shift, monoid_runit. reflexivity.
  Qed.

  (* interp_writer is a monad morphism into writerT. *)

  Lemma interp_writer_ret {R} (x : R) : interp_writer MW h (Ret x) ≅ Ret (0, x).
  Proof. unfold interp_writer. now rewrite interp_state_ret. Qed.

  Lemma interp_writer_bind {R S} (t : itree E R) (k : R -> itree E S) :
    interp_writer MW h (ITree.bind t k)
    ≅ ITree.bind (interp_writer MW h t) (fun '(w, x) => shift w (interp_writer MW h (k x))).
  Proof.
    unfold interp_writer at 1. rewrite interp_state_bind.
    apply eqit_bind; [reflexivity |]. intros [w x]. apply interp_state_writer.
  Qed.

  Lemma interp_writer_trigger {R} (e : E R) : interp_writer MW h (ITree.trigger e) ≈ h e.
  Proof.
    unfold interp_writer. rewrite interp_state_trigger. unfold writer_to_state, ITree.map.
    rewrite <- (bind_ret_r (h e)) at 2. apply eutt_eq_bind. intros [w x].
    now rewrite monoid_lunit.
  Qed.

  #[global] Instance interp_writer_eutt {R} :
    Proper (eutt eq ==> eutt eq) (@interp_writer W E F MW h R).
  Proof. intros t t' Ht. unfold interp_writer. now rewrite Ht. Qed.
End WriterFacts.
