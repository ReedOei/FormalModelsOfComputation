Require Import List PeanoNat Omega Bool.

Import ListNotations.

Require Import Sets.

Definition string (Sigma : list nat) := list (element Sigma).
Definition language (Sigma : list nat) := set (string Sigma).

Definition prefix {Sigma : list nat} (pre : string Sigma) (x : string Sigma) :=
  exists (suf : string Sigma), pre ++ suf = x.

Definition suffix {Sigma : list nat} (suf : string Sigma) (x : string Sigma) :=
  exists (pre : string Sigma), pre ++ suf = x.

Definition substring {Sigma : list nat} (sub : string Sigma) (x : string Sigma) :=
  exists (pre suf : string Sigma), pre ++ sub ++ suf = x.

Fixpoint length {Sigma : list nat} (s : string Sigma) : nat :=
  match s with
    | []      => 0
    | _ :: xs => 1 + length xs
  end.

Fixpoint concat {Sigma : list nat} (a b : string Sigma) : string Sigma :=
  match a with
    | []      => b
    | x :: xs => x :: concat xs b
  end.

Fixpoint reverse {Sigma : list nat} (s : string Sigma) : string Sigma :=
  match s with
  | []      => []
  | x :: xs => reverse xs ++ [x]
  end.

Definition eq_symb {Sigma : list nat} (a b : element Sigma) : bool :=
  match a, b with
  | exist _ n _, exist _ m _ => beq_nat n m
  end.

Fixpoint count {Sigma : list nat} (a : element Sigma) (s : string Sigma) : nat :=
  match s with
  | []      => 0
  | x :: xs => if eq_symb x a then 1 + count a xs else count a xs
  end.

Lemma length_concat : forall {Sigma : list nat} (a b : string Sigma), length (a ++ b) = length a + length b.
Proof.
intuition.
induction a.
simpl. reflexivity.
simpl. rewrite IHa. reflexivity.
Qed.

Lemma length_reverse : forall {Sigma : list nat} (s : string Sigma), length s = length (reverse s).
Proof.
intuition.
induction s.
simpl. reflexivity.
simpl. rewrite length_concat. 
simpl. rewrite IHs. 
rewrite Nat.add_comm.
simpl. reflexivity.
Qed.

Lemma reverse_concat : 
  forall {Sigma : list nat} (a b : string Sigma), 
    reverse (a ++ b) = reverse b ++ reverse a.
Proof.
intuition.
induction a.
simpl. rewrite app_nil_r. reflexivity.
simpl. rewrite IHa. rewrite <- app_assoc. reflexivity.
Qed.

Lemma reverse_reverse_id : forall {Sigma : list nat} (s : string Sigma), reverse (reverse s) = s.
Proof.
intuition.
induction s.
simpl. reflexivity.
simpl. rewrite reverse_concat. simpl. rewrite IHs. reflexivity.
Qed.

Lemma count_concat : 
  forall {Sigma : list nat} (a b : string Sigma) (x : element Sigma), 
    count x (a ++ b) = count x a + count x b.
Proof.
intuition.
induction a.
intuition.
simpl.
inversion x.
inversion a.
induction (beq_nat x0 x1).
  induction (eq_symb a x).
  omega. omega.

  induction (eq_symb a x).
  omega. omega.
Qed.

Lemma count_reverse : 
  forall {Sigma : list nat} (s : string Sigma) (x : element Sigma), 
    count x s = count x (reverse s).
Proof.
intuition.
induction s.
intuition.
simpl.
rewrite IHs.
rewrite count_concat.
simpl.
inversion x.
inversion a.
induction (beq_nat x0 x1).
  induction (eq_symb a x).
  omega. omega.

  induction (eq_symb a x).
  omega. omega.
Qed.

Lemma empty_always_prefix : forall {Sigma : list nat} (str : string Sigma), prefix [] str.
Proof.
intuition.
unfold prefix.
exists str.
intuition.
Qed.

Lemma whole_string_is_prefix : forall {Sigma : list nat} (str : string Sigma), prefix str str.
Proof.
intuition.
unfold prefix.
exists [].
intuition.
Qed.

Lemma empty_always_suffix : forall {Sigma : list nat} (str : string Sigma), suffix [] str.
Proof.
intuition.
unfold suffix.
exists str.
intuition.
Qed.

Lemma whole_string_is_suffix : forall {Sigma : list nat} (str : string Sigma), suffix str str.
Proof.
intuition.
unfold suffix.
exists [].
intuition.
Qed.

Lemma empty_always_substring : forall {Sigma : list nat} (str : string Sigma), substring [] str.
Proof.
intuition.
unfold substring.
exists []. exists str.
intuition.
Qed.

Lemma whole_string_is_substring : forall {Sigma : list nat} (str : string Sigma), substring str str.
Proof.
intuition.
unfold substring.
exists []. exists [].
rewrite app_assoc.
intuition.
Qed.
