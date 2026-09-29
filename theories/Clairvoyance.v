From Coq Require Import Ensembles.
From ITree.Events Require Import Nondeterminism.
From Lazy Require Import Base Thunk Events.Fail Events.Tick PropM.
From ExtLib Require Import
  Structures.Monoid.

Definition clairvoyanceE : Type -> Type := tickE +' failE +' nondetE.

Definition run_clairvoyance : itree clairvoyanceE ~> writerT nat Ensemble :=
  fun _ t => returns_some (run_tick_to_writerT_nat_sum t)
.

Definition thunk (E : Type -> Type) (A : Type) `{nondetE -< E} (u : itree E A) : itree E (T A) :=
  or (ret Undefined) (fmap Thunk u)
.

Definition force (E : Type -> Type) (A : Type) `{failE -< E} (t : T A) : itree E A :=
  match t with
  | Thunk v => ret v
  | Undefined => fail
  end
.

(* Use the paco library to model coinductive data *)
(* or look at what choice trees are using *)
CoInductive colist (A : Type) :=
| conil : colist A
| cocons : A -> colist A -> colist A
.
Arguments conil {A}.
Arguments cocons {A}.

(* cofindE is an effect representing a call to the cofind function.  We
   introduce it locally and then eliminate it using cofind (via mrec with
   handler h_cofind).  See "Interaction Trees" for an explanation of this
   approach to modeling general recursion; they demonstrate it using the
   Ackermann function.  The technique was first published in
   "Turing-Completeness Totally Free." *)

Variant cofindE (A : Type) : Type -> Type :=
| Cofind : nat -> colist A -> cofindE A bool
.
Arguments Cofind {A}.

Import MonadNotation.
Open Scope monad_scope.
Definition h_cofind (E : Type -> Type) `{tickE -< E} `{failE -< E} `{nondetE -< E} :
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

(* if I insert an element at a certain index, then the cost should be no greater than that index ... *)
(* also consider take ∘ append or take ∘ repeat *)
(* because it's clairvoyance semantics, we'll have to think about optimistic/pessimistic specs *)

Definition cofind {E} `{tickE -< E} `{failE -< E} `{nondetE -< E}
  (n : nat) (c : colist nat) : itree E bool :=
  mrec (fun _ e => h_cofind e) (Cofind n c)
.

(* Pure insert. *)
Fixpoint insert (A : Type) (n : nat) (x : A) (xs : colist A) : colist A :=
  match n, xs with
  | O, _ => cocons x xs
  | _, conil => cocons x xs
  | S n', cocons x' xs' => cocons x' (insert n' x xs')
  end
.

From Coq Require Import Morphisms.
From ITree Require Import Props.Leaf Events.FailFacts
  Interp.InterpFacts Interp.RecursionFacts.
From Lazy Require Import WriterFacts.
Import LeafNotations.

(* [t] can return [a] at cost [c] along some nondeterministic path that
   doesn't fail. *)
Definition runs_to {A} (t : itree clairvoyanceE A) (c : nat) (a : A) : Prop :=
  In _ (run_clairvoyance t) (c, a).

Ltac unfold_runs_to :=
  unfold runs_to, run_clairvoyance, returns_some, run_tick_to_writerT_nat_sum,
    run_tick_to_writerT, run_fail_to_itree, run_fail, In;
  cbv beta.

#[global] Instance runs_to_eutt {A} : Proper (eutt eq ==> eq ==> eq ==> iff) (@runs_to A).
Proof.
  intros t t' H c ? <- a ? <-. unfold_runs_to. now rewrite H.
Qed.

Lemma runs_to_cost {A} (t : itree clairvoyanceE A) c c' a :
  runs_to t c a -> c = c' -> runs_to t c' a.
Proof. now intros ? <-. Qed.

(* Composition principles for [runs_to]. *)

Lemma runs_to_ret {A} (a : A) : runs_to (Ret a) 0 a.
Proof.
  unfold_runs_to. rewrite interp_writer_ret, interp_fail_Ret. now apply Leaf_Ret.
Qed.

Lemma runs_to_bind {A B} (t : itree clairvoyanceE A) (k : A -> itree clairvoyanceE B) c1 c2 a b :
  runs_to t c1 a -> runs_to (k a) c2 b -> runs_to (ITree.bind t k) (c1 + c2) b.
Proof.
  unfold_runs_to. intros H1 H2.
  rewrite (interp_writer_bind (MW := nat_sum_monoid)), interp_fail_bind.
  eapply Leaf_bind; [exact H1 |]. cbn.
  unfold ITree.map. rewrite interp_fail_bind.
  eapply Leaf_bind; [exact H2 |]. cbn.
  rewrite interp_fail_Ret. now apply Leaf_Ret.
Qed.

Lemma runs_to_tick : runs_to (trigger (inl1 Tick)) 1 tt.
Proof.
  unfold_runs_to. rewrite (interp_writer_trigger (MW := nat_sum_monoid)). cbn.
  rewrite interp_fail_Ret. now apply Leaf_Ret.
Qed.

Lemma runs_to_or b : runs_to (trigger (inr1 (inr1 Or))) 0 b.
Proof.
  unfold_runs_to. rewrite (interp_writer_trigger (MW := nat_sum_monoid)). unfold pure_writer. cbn.
  unfold ITree.map. rewrite interp_fail_bind, interp_fail_trigger. cbn.
  rewrite bind_bind, bind_trigger. apply Leaf_Vis with b.
  rewrite bind_ret_l, interp_fail_Ret. now apply Leaf_Ret.
Qed.

Section Cofind.
  Local Notation h := (fun (T : Type) (e : cofindE nat T) => h_cofind (E := clairvoyanceE) e).

  Lemma runs_to_interp_or {A} (k : bool -> itree (cofindE nat +' clairvoyanceE) A) b c a :
    runs_to (interp (mrecursive h) (k b)) c a ->
    runs_to (interp (mrecursive h) (vis Or k)) c a.
  Proof.
    intros H. rewrite interp_vis. cbn.
    change c with (0 + c). eapply runs_to_bind; [apply runs_to_or |].
    rewrite tau_eutt. exact H.
  Qed.

  Lemma cofind_unfold n xs :
    cofind n xs ≈ interp (mrecursive h) (h_cofind (Cofind n xs)).
  Proof. apply mrec_as_interp. Qed.

  (* Both cocons cases start by paying for the tick. *)
  Lemma runs_to_cofind_cocons n y xs c b :
    runs_to (interp (mrecursive h)
               (bT <- thunk (trigger (Cofind n xs)) ;;
                if Nat.eqb n y then ret true else force bT)) c b ->
    runs_to (cofind n (cocons y xs)) (S c) b.
  Proof.
    intros H. rewrite cofind_unfold. cbn.
    rewrite interp_bind. change (S c) with (1 + c). eapply runs_to_bind.
    { unfold tick. rewrite interp_trigger. cbn. apply runs_to_tick. }
    exact H.
  Qed.

  Lemma cofind_hit n xs : runs_to (cofind n (cocons n xs)) 1 true.
  Proof.
    apply runs_to_cofind_cocons. cbn.
    rewrite interp_bind. change 0 with (0 + 0). eapply runs_to_bind.
    - unfold thunk, or. cbn. apply runs_to_interp_or with (b := true).
      rewrite interp_ret. apply runs_to_ret.
    - rewrite PeanoNat.Nat.eqb_refl, interp_ret. apply runs_to_ret.
  Qed.

  Lemma cofind_skip n y xs c :
    runs_to (cofind n xs) c true -> runs_to (cofind n (cocons y xs)) (S c) true.
  Proof.
    intros IH. apply runs_to_cofind_cocons. cbn.
    rewrite interp_bind. eapply runs_to_cost; [eapply runs_to_bind |].
    - unfold thunk, or. cbn. apply runs_to_interp_or with (b := false).
      unfold ITree.map. rewrite interp_bind. eapply runs_to_bind.
      + rewrite interp_trigger. cbn. exact IH.
      + rewrite interp_ret. apply runs_to_ret.
    - destruct (Nat.eqb n y); cbn; rewrite interp_ret; apply runs_to_ret.
    - cbn. now rewrite !PeanoNat.Nat.add_0_r.
  Qed.
End Cofind.

Lemma cofind_insert_terminates : forall xs n x, exists c, In _ (run_clairvoyance (cofind x (insert n x xs))) (c, true).
Proof.
  intros xs n x. revert xs.
  induction n as [| n IH]; intros [| y xs]; cbn;
    try (exists 1; apply cofind_hit).
  destruct (IH xs) as [c Hc]. exists (S c). now apply cofind_skip.
Qed.
