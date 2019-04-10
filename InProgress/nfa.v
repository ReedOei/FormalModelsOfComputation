Require Import List Bool.

Import ListNotations.

Require Import FinSets.

Structure dfa (A B : Type) := {
  t : A -> B -> A;
  s : A;

  F : A -> bool;

  A_fin : FinType A;
  B_fin : FinType B;
}.

Arguments t {A} {B}.
Arguments s {A} {B}.
Arguments F {A} {B}.
Arguments A_fin {A} {B}.
Arguments B_fin {A} {B}.

Fixpoint tStar {A B : Type} (M : dfa A B) (q : A) (str : list B) : A :=
  match str with
  | []      => q
  | x :: xs => tStar M (t M q x) xs
  end.

Definition accepted {A B : Type} (M : dfa A B) (str : list B) : bool :=
  F M (tStar M (s M) str).

Lemma tStar_step :
  forall {A B : Type} (M : dfa A B) (str : list B) (q : A) (x : B), 
    tStar M q (str ++ [x]) = t M (tStar M q str) x.
Proof.
intros A B M str.

induction str.
intuition.

intuition.
simpl.
exact (IHstr (t M q a) x).
Qed.

Definition not_dfa_f {A B : Type} (M : dfa A B) (q : A) : bool := negb (F M q).

Definition not_dfa {A B : Type} (M : dfa A B) : dfa A B :=
  Build_dfa A B (t M) (s M) (not_dfa_f M) (A_fin M) (B_fin M).

Lemma not_dfa_mirror {A B : Type} (M : dfa A B) : 
  forall (str : list B), tStar M (s M) str = tStar (not_dfa M) (s M) str.
Proof.
apply rev_ind.

intuition.

intuition.
rewrite tStar_step, tStar_step.
simpl.
rewrite H.
reflexivity.
Qed.

Theorem not_dfa_correct :
  forall {A B : Type} (M : dfa A B) (str : list B),
   accepted M str = true <-> accepted (not_dfa M) str = false.
Proof.
intros.
unfold accepted.
simpl.
rewrite not_dfa_mirror.
unfold not_dfa_f.
intuition.
rewrite H.
intuition.
induction (F M (tStar (not_dfa M) (s M) str)).
intuition.
intuition.
Qed.

Definition and_dfa_trans
  {A B C : Type} (M : dfa A B) (N : dfa C B) (q : A * C) (s : B) : A * C :=
  match q with
  | (qm, qn) => (t M qm s, t N qn s)
  end.

Definition and_dfa_f {A B C : Type} (M : dfa A B) (N : dfa C B) (q : A * C) : bool :=
  match q with
  | (a,c) => F M a && F N c
  end.

Definition and_dfa {A B C : Type} (M : dfa A B) (N : dfa C B) : dfa (A * C) B :=
  Build_dfa (A * C) B
            (and_dfa_trans M N) (s M, s N) (and_dfa_f M N)
            (prod_of_fin_is_fin (A_fin M) (A_fin N)) (B_fin M).

Lemma and_dfa_mirror_m
  {A B C : Type} (M : dfa A B) (N : dfa C B) :
    forall (str : list B), tStar M (s M) str = fst (tStar (and_dfa M N) (s (and_dfa M N)) str).
Proof.
apply rev_ind.

intuition.

intros.

rewrite tStar_step, tStar_step.
destruct (tStar (and_dfa M N) (s (and_dfa M N)) l).
unfold and_dfa.
simpl.
rewrite H.
intuition.
Qed.

Lemma and_dfa_mirror_n
  {A B C : Type} (M : dfa A B) (N : dfa C B) :
    forall (str : list B), tStar N (s N) str = snd (tStar (and_dfa M N) (s (and_dfa M N)) str).
Proof.
apply rev_ind.

intuition.

intros.

rewrite tStar_step.
rewrite tStar_step.
destruct (tStar (and_dfa M N) (s (and_dfa M N)) l).
unfold and_dfa.
simpl.
rewrite H.
intuition.
Qed.

Theorem and_dfa_correct :
  forall {A B C : Type} (M : dfa A B) (N : dfa C B) (str : list B),
    accepted (and_dfa M N) str = true <-> accepted M str && accepted N str = true.
Proof.
intros.
unfold accepted.
rewrite (and_dfa_mirror_m M N str).
rewrite (and_dfa_mirror_n M N str).
destruct (tStar (and_dfa M N) (s (and_dfa M N)) str).
simpl.

intuition.
Qed.

Structure nfa (A B : Type) := {
  nt : A -> B -> A -> bool;
  ns : A;

  nF : A -> bool;
}.

Arguments nt {A} {B}.
Arguments ns {A} {B}.
Arguments nF {A} {B}.

Definition powerset_nfa_trans
  {A B : Type} (M : nfa A B) (possible : list A) (x : B) : list A :=
  map 

Definition powerset_nfa
  {A B : Type} (M : nfa A B) : dfa (list A) B :=
    Build_dfa (list A) B power_nfa_trans.
