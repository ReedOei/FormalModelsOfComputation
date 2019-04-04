Require Import List PeanoNat Omega Bool MSets MSetDecide Ensembles.

Import ListNotations.

Require Import AutomataTactics.

Module S := Make Nat_as_OT.

Definition member (s : S.t) := {x : S.elt | S.mem x s = true}.
Definition subset (s : S.t) := {a : S.t | forall (x : S.elt), S.mem x a = true -> S.mem x s = true}.

Definition subset_mem {s : S.t} (x : S.elt) (s' : subset s) : bool :=
  match s' with
  | exist _ set _ => S.mem x set
  end.

Lemma empty_set_is_subset : forall {s : S.t} (x : S.elt), S.mem x S.empty = true -> S.mem x s = true.
Proof.
intuition.
Qed.

Lemma full_set_is_subset : forall {s : S.t} (x : S.elt), S.mem x s = true -> S.mem x s = true.
Proof.
intuition.
Qed.

Definition empty_set {s : S.t} : subset s := exist _ S.empty empty_set_is_subset.
Definition full_set {s : S.t} : subset s := exist _ s full_set_is_subset.

Hint Resolve empty_set_is_subset full_set_is_subset : sets.

Lemma mem_singleton_eq : forall (x y : S.elt), S.In x (S.singleton y) -> x = y.
Proof.
simplify.
inversion H.
simplify.
inversion H1.
inversion H1.
Qed.

Hint Rewrite mem_singleton_eq : sets.
Hint Rewrite S.mem_spec S.diff_spec : sets.

Lemma singleton_is_subset : 
  forall {s : S.t} {x : S.elt}, S.mem x s = true -> 
    forall (y : S.elt), S.mem y (S.singleton x) = true -> S.mem y s = true.
Proof.
simplify.
rewrite S.mem_spec in H0.
rewrite (mem_singleton_eq y x H0).
rewrite S.mem_spec in H.
assumption.
Qed.

Definition singleton_subset {s : S.t} (x : S.elt) (prf : S.mem x s = true) : subset s := 
  exist _ (S.singleton x) (singleton_is_subset prf).

Lemma diff_is_subset :
  forall {s s' : S.t} (x : S.elt), S.mem x (S.diff s s') = true -> S.mem x s = true.
Proof.
simplify.
rewrite S.mem_spec in H.
rewrite S.diff_spec in H.
destruct H.
assumption.
Qed.

Definition diff_subset (s s' : S.t) : subset s := exist _ (S.diff s s') diff_is_subset.
