Require Import List PeanoNat Omega Bool MSets MSetDecide Ensembles.

Import ListNotations.

Require Import Sets AutomataTactics.

Section Strings.
Variable Sigma : S.t.

Definition string := list (member Sigma).
Definition language := Ensemble string.

Definition empty_language : language := fun _ => False.
Definition full_language : language := fun _ => True.

Definition prefix (pre : string) (x : string) :=
  exists (suf : string), pre ++ suf = x.

Definition suffix (suf : string) (x : string) :=
  exists (pre : string), pre ++ suf = x.

Definition substring (sub : string) (x : string) :=
  exists (pre suf : string), pre ++ sub ++ suf = x.
End Strings.

Hint Unfold prefix suffix substring.

(* So we don't need to pass Sigma always *)
Arguments string : default implicits.
Arguments language : default implicits.
Arguments prefix : default implicits.
Arguments suffix : default implicits.
Arguments substring : default implicits.

Section Strings_funcs.
Variable Sigma : S.t.

Fixpoint length (s : string Sigma) : nat :=
  match s with
    | []      => 0
    | _ :: xs => 1 + length xs
  end.

Fixpoint concat (a b : string Sigma) : string Sigma :=
  match a with
    | []      => b
    | x :: xs => x :: concat xs b
  end.

Fixpoint reverse (s : string Sigma) : string Sigma :=
  match s with
  | []      => []
  | x :: xs => reverse xs ++ [x]
  end.

Definition eq_symb (a b : member Sigma) : bool :=
  match a, b with
  | exist _ n _, exist _ m _ => beq_nat n m
  end.

Fixpoint count (a : member Sigma) (s : string Sigma) : nat :=
  match s with
  | []      => 0
  | x :: xs => if eq_symb x a then 1 + count a xs else count a xs
  end.
End Strings_funcs.

Arguments length : default implicits.
Arguments concat : default implicits.
Arguments reverse : default implicits.
Arguments eq_symb : default implicits.
Arguments count : default implicits.

Hint Unfold length concat reverse eq_symb count.

Section Strings_facts.
Variable Sigma : S.t.

Lemma length_concat : forall (a b : string Sigma), length (a ++ b) = length a + length b.
Proof.
autoinduction a.
Qed.

Hint Rewrite length_concat : strings.

Lemma length_reverse : forall (s : string Sigma), length s = length (reverse s).
Proof.
autoinduction s.
Qed.

Lemma reverse_concat : 
  forall (a b : string Sigma), 
    reverse (a ++ b) = reverse b ++ reverse a.
Proof.
autoinduction a.
rewrite <- app_assoc. reflexivity.
Qed.

Hint Rewrite reverse_concat length_reverse : strings.

Lemma reverse_reverse_id : forall (s : string Sigma), reverse (reverse s) = s.
Proof.
autoinduction s.
Qed.

Lemma count_concat : 
  forall (a b : string Sigma) (x : member Sigma), 
    count x (a ++ b) = count x a + count x b.
Proof.
autoinduction a.
inversion x.
inversion a.
induction (beq_nat x0 x1).
  induction (eq_symb a x).
  omega. omega.

  induction (eq_symb a x).
  omega. omega.
Qed.

Hint Rewrite count_concat : strings.

Lemma count_reverse : 
  forall (s : string Sigma) (x : member Sigma), 
    count x s = count x (reverse s).
Proof.
autoinduction s.
inversion x.
inversion a.
induction (beq_nat x0 x1).
  induction (eq_symb a x).
  omega. omega.

  induction (eq_symb a x).
  omega. omega.
Qed.

Lemma empty_always_prefix : forall (str : string Sigma), prefix [] str.
Proof.
intuition.
unfold prefix.
exists str.
intuition.
Qed.

Lemma whole_string_is_prefix : forall (str : string Sigma), prefix str str.
Proof.
intuition.
unfold prefix.
exists [].
intuition.
Qed.

Lemma empty_always_suffix : forall (str : string Sigma), suffix [] str.
Proof.
intuition.
unfold suffix.
exists str.
intuition.
Qed.

Lemma whole_string_is_suffix : forall (str : string Sigma), suffix str str.
Proof.
intuition.
unfold suffix.
exists [].
intuition.
Qed.

Lemma empty_always_substring : forall (str : string Sigma), substring [] str.
Proof.
intuition.
unfold substring.
exists []. exists str.
intuition.
Qed.

Lemma whole_string_is_substring : forall (str : string Sigma), substring str str.
Proof.
intuition.
unfold substring.
exists []. exists [].
rewrite app_assoc.
intuition.
Qed.

End Strings_facts.
