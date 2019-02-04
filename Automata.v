Require Import List PeanoNat Omega Bool.

Import ListNotations.

Require Import Sets Strings.

Structure dfa := {
  Q : list nat;
  Sigma : list nat;

  t : element Q -> element Sigma -> element Q;
  s : element Q;

  A : subset Q;
}.

Arguments Q {d}.
Arguments Sigma {d}.
Arguments t {d} _ _.
Arguments A {d}.

Fixpoint tStar (M : dfa)
               (q : element (@Q M))
               (str : string Sigma)
               : element Q := 
  match str with
  | []      => q
  | x :: xs => tStar M (t q x) xs
  end.

Arguments tStar {M}.

Definition accepted (M : dfa) (x : string Sigma) : bool := A (tStar (@s M) x).

Fixpoint n_nats (i n : nat) : list nat :=
  match n with
  | 0   => [i]
  | S n => i :: n_nats (i + 1) (n - 1)
  end.

Definition range (high : nat) : list nat := n_nats 0 high.

Definition substr_dfa (x : string Sigma) : dfa :=
  Build_dfa (range (length x + 2)).

