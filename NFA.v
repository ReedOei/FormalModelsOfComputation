Require Import List Bool DFA.

Import ListNotations.

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
      tStar (powerset_nfa M) (s (powerset_nfa M)) str = ntStar M (ns M) str.
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
