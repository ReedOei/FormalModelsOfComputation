Require Import List PeanoNat Omega Bool MSets MSetDecide Ensembles.

Import ListNotations.

Module S := Make Nat_as_OT.

Definition member (s : S.t) := {x : S.elt | S.mem x s = true}.
Definition subset (s : S.t) := {a : S.t | forall (x : S.elt), S.mem x a = true -> S.mem x s = true}.

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
