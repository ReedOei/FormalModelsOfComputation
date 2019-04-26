Require Import List PeanoNat Omega Bool FinSets AutomataTactics.

Import ListNotations.

Section Strings.

Context {A : Type} `{EqA : DecEq A}.

Definition prefix (pre : list A) (x : list A) :=
  { suf : list A | pre ++ suf = x }.

Definition suffix (suf : list A) (x : list A) :=
  { pre : list A | pre ++ suf = x }.

Definition substring (sub : list A) (x : list A) :=
  { pair : list A * list A | let (pre,suf) := pair in pre ++ sub ++ suf = x }.

Fixpoint count (a : A) (s : list A) : nat :=
  match s with
  | []      => 0
  | x :: xs => if x =? a then 1 + count a xs else count a xs
  end.

Lemma count_concat : 
  forall (a b : list A) (x : A), 
    count x (a ++ b) = count x a + count x b.
Proof.
autoinduction a with (induction (deq a x)).
Qed.

Hint Rewrite count_concat : standard.

Lemma count_reverse : 
  forall (s : list A) (x : A), count x s = count x (rev s).
Proof.
autoinduction s with (rewrite IHs; simpl; induction (deq a x)).
Qed.

Hint Rewrite count_reverse : standard.

Lemma empty_always_prefix : forall (str : list A), prefix [] str.
Proof.
intros.
quick (exists str).
Qed.

Lemma whole_string_is_prefix : forall (str : list A), prefix str str.
Proof.
quick (exists []).
Qed.

Lemma empty_always_suffix : forall (str : list A), suffix [] str.
Proof.
intros.
quick (exists str).
Qed.

Lemma whole_string_is_suffix : forall (str : list A), suffix str str.
Proof.
quick (exists []).
Qed.

Lemma empty_always_substring : forall (str : list A), substring [] str.
Proof.
intros.
quick (exists ([], str)).
Qed.

Lemma whole_string_is_substring : forall (str : list A), substring str str.
Proof.
quick (exists ([],[])).
Qed.

End Strings.
