Require Import List PeanoNat Omega.

Import ListNotations.

Variable A B : Type.

Variable eq : A -> A -> bool.

Notation "a == b" := (eq a b) (at level 10).

Fixpoint length (s : list A) : nat :=
  match s with
    | []      => 0
    | _ :: xs => 1 + length xs
  end.

Fixpoint concat (a b : list A) : list A :=
  match a with
    | []      => b
    | x :: xs => x :: concat xs b
  end.

Fixpoint reverse (s : list A) : list A :=
  match s with
  | []      => []
  | x :: xs => reverse xs ++ [x]
  end.

Fixpoint count (a : A) (s : list A) : nat :=
  match s with
  | []      => 0
  | x :: xs => if eq a x then 1 + count a xs else count a xs
  end.

Notation "a ++ b" := (concat a b).

Lemma concat_empty_string_id : forall (s : list A), s ++ [] = s.
Proof.
intuition.
induction s.
intuition.
simpl. rewrite IHs. reflexivity.
Qed.

Lemma length_concat : forall (a b : list A), length (a ++ b) = length a + length b.
Proof.
intros a b.
intuition.
induction a.
simpl. reflexivity.
simpl. rewrite IHa. reflexivity.
Qed.

Lemma concat_assoc : forall (a b c : list A), a ++ (b ++ c) = (a ++ b) ++ c.
Proof.
intuition.
induction a.
simpl. reflexivity.
simpl. rewrite IHa. reflexivity.
Qed.

Lemma length_reverse : forall (s : list A), length s = length (reverse s).
Proof.
intuition.
induction s.
simpl. reflexivity.
simpl. rewrite length_concat. 
simpl. rewrite IHs. 
rewrite Nat.add_comm.
simpl. reflexivity.
Qed.

Lemma reverse_concat : forall (a b : list A), reverse (a ++ b) = reverse b ++ reverse a.
Proof.
intuition.
induction a.
simpl. rewrite concat_empty_string_id. reflexivity.
simpl. rewrite IHa. rewrite <- concat_assoc. reflexivity.
Qed.

Lemma reverse_reverse_id : forall (s : list A), reverse (reverse s) = s.
Proof.
intuition.
induction s.
simpl. reflexivity.
simpl. rewrite reverse_concat. simpl. rewrite IHs. reflexivity.
Qed.

Lemma count_concat : forall (a b : list A) (x : A), count x (a ++ b) = count x a + count x b.
Proof.
intuition.
induction a.
intuition.
simpl.
induction (x == a).
simpl. rewrite IHa. reflexivity.
rewrite IHa. reflexivity.
Qed.

Lemma count_reverse : forall (s : list A) (x : A), count x s = count x (reverse s).
Proof.
intuition.
induction s.
intuition.
simpl.
rewrite IHs.
rewrite count_concat.
simpl.
induction (x == a).
omega.
omega.
Qed.

