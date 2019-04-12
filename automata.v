Require Import List Bool.

Import ListNotations.

Require Import FinSets.

Section DFA.

Structure dfa (A B : Type) := {
  t : A -> B -> A;
  s : A;

  F : A -> bool;
}.

Arguments t {A} {B}.
Arguments s {A} {B}.
Arguments F {A} {B}.

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
  Build_dfa A B (t M) (s M) (not_dfa_f M).

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
            (and_dfa_trans M N) (s M, s N) (and_dfa_f M N).
(*             (prod_of_fin_is_fin (A_fin M) 
 *)
(*  (A_fin N)) (B_fin M). *)

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

End DFA.

Section NFA.

Structure nfa (A B : Type) := {
  nt : A -> B -> list A;
  ns : A;

  nF : A -> bool;
}.

Arguments nt {A} {B}.
Arguments ns {A} {B}.
Arguments nF {A} {B}.

Fixpoint ntStar {A B : Type} (M : nfa A B) (q : A) (str : list B) : list A :=
  match str with
  | []      => [q]
  | x :: xs => flat_map (fun st => ntStar M st xs) (nt M q x)
  end.

Definition naccepted {A B : Type} (M : nfa A B) (str : list B) : bool :=
  existsb (nF M) (ntStar M (ns M) str).

Definition powerset_nfa_trans
  {A B : Type} (M : nfa A B) (possible : list A) (x : B) : list A :=
    flat_map (fun source => nt M source x) possible.

Definition powerset_nfa_f
  {A B : Type} (M : nfa A B) (possible : list A) : bool :=
    existsb (nF M) possible.

Definition powerset_nfa
  {A B : Type} (M : nfa A B) : dfa (list A) B :=
    Build_dfa (list A) B 
      (powerset_nfa_trans M) 
      [ns M]
      (powerset_nfa_f M).

Lemma flat_map_works :
  forall {A B : Type} {f : A -> list B} (xs : list A) (a : A) (b : B), 
    Elem a xs -> Elem b (f a) -> Elem b (flat_map f xs).
Proof.
intuition.
induction xs.

inversion H.
simpl.
inversion H.
rewrite <- H3.
exact (elem_append_l b H0).
exact (elem_append_r b (IHxs prf)).
Qed.

Lemma flat_map_id :
  forall {A : Type} (xs : list A), flat_map (fun x => [x]) xs = xs.
Proof.
intuition.
induction xs.
intuition.
simpl.
rewrite IHxs.
reflexivity.
Qed.

Lemma flat_map_app :
  forall {A B : Type} {f : A -> list B} (xs ys : list A),
    flat_map f (xs ++ ys) = flat_map f xs ++ flat_map f ys.
Proof.
intuition.
induction xs.
intuition.
simpl.
rewrite IHxs.
rewrite app_assoc.
reflexivity.
Qed.

Lemma flat_map_comp :
  forall {A B C : Type} {f1 : A -> list B} {f2 : B -> list C} (xs : list A),
    flat_map f2 (flat_map f1 xs) = flat_map (fun x => flat_map f2 (f1 x)) xs.
Proof.
intuition.
induction xs.
intuition.
simpl.
rewrite <- IHxs.
apply flat_map_app.
Qed.

Axiom functional_extensionality :
  forall {A B : Type} {f g : A -> B}
    (prf : forall (x : A), f x = g x), f = g.

Lemma flat_map_equality :
  forall {A B : Type} (f g : A -> list B) (xs : list A),
    f = g -> flat_map f xs = flat_map g xs.
Proof.
intuition.
rewrite H.
reflexivity.
Qed.

Lemma ntStar_step {A B : Type} (M : nfa A B) :
  forall (str : list B) (x : B) (q : A),
    ntStar M q (str ++ [x]) = flat_map (fun st => nt M st x) (ntStar M q str).
Proof.
induction str.
intuition.
simpl.
rewrite app_nil_r.
apply flat_map_id.

intuition.
simpl.
rewrite flat_map_comp.
apply flat_map_equality.
apply functional_extensionality.
intuition.
Qed.

Lemma powerset_nfa_mirror
  {A B : Type} (M : nfa A B) :
    forall (str : list B),
      tStar (powerset_nfa M) (s (list A) B (powerset_nfa M)) str = ntStar M (ns M) str.
Proof.
apply rev_ind.
intuition.
intuition.
rewrite tStar_step.
rewrite ntStar_step.
simpl.
unfold powerset_nfa_trans.
rewrite <- H.
intuition.
Qed.

Theorem powerset_nfa_correct
  {A B : Type} (M : nfa A B) :
    forall (str : list B), accepted (powerset_nfa M) str = true <-> naccepted M str = true.
Proof.
apply rev_ind.

intuition.

intuition.
unfold accepted, powerset_nfa in H.
rewrite (powerset_nfa_mirror M) in H.
intuition.

unfold naccepted in H.
rewrite <- (powerset_nfa_mirror M) in H.
rewrite tStar_step in H.
simpl.
rewrite tStar_step.
intuition.
Qed.

End NFA.
