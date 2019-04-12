Require Import List Bool DFA AutomataTactics.

Import ListNotations.

Axiom functional_extensionality :
  forall {A B : Type} {f g : A -> B}
    (prf : forall (x : A), f x = g x), f = g.

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

Lemma flat_map_id :
  forall (A : Type) (xs : list A), flat_map (fun x => [x]) xs = xs.
Proof.
intuition.
induction xs.
intuition.
simpl.
now (rewrite IHxs).
Qed.

Lemma flat_map_app :
  forall (A B : Type) {f : A -> list B} (xs ys : list A),
    flat_map f (xs ++ ys) = flat_map f xs ++ flat_map f ys.
Proof.
intuition.
induction xs.
intuition.
simpl.
now (rewrite IHxs, app_assoc).
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

Lemma flat_map_equality :
  forall {A B : Type} (f g : A -> list B) (xs : list A),
    f = g -> flat_map f xs = flat_map g xs.
Proof.
congruence.
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
now (apply functional_extensionality).
Qed.

Definition dfa_to_nfa {A B : Type} (M : dfa A B) : nfa A B :=
  Build_nfa A B (fun st x => [t M st x]) (s M) (F M).

Lemma dfa_to_nfa_mirror {A B : Type} (M : dfa A B) :
  forall (str : list B), [tStar M (s M) str] = ntStar (dfa_to_nfa M) (ns (dfa_to_nfa M)) str.
Proof.
apply rev_ind.
intuition.

intuition.
now (rewrite tStar_step, ntStar_step, <- H).
Qed.

Theorem dfa_to_nfa_correct :
  forall {A B : Type} (M : dfa A B) (str : list B), 
    accepted M str = true <-> naccepted (dfa_to_nfa M) str = true.
Proof.
intuition.

unfold accepted in H.
unfold naccepted.
rewrite <- dfa_to_nfa_mirror.
simpl.
now (rewrite H).

unfold accepted.
unfold naccepted in H.
rewrite <- dfa_to_nfa_mirror in H.
simpl in H.
now (rewrite orb_false_r in H).
Qed.

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

Lemma powerset_nfa_mirror
  {A B : Type} (M : nfa A B) :
    forall (str : list B),
      tStar (powerset_nfa M) (s (powerset_nfa M)) str = ntStar M (ns M) str.
Proof.
apply rev_ind.
intuition.
intuition.
rewrite tStar_step, ntStar_step.
simpl.
unfold powerset_nfa_trans.
now (rewrite <- H).
Qed.

Theorem powerset_nfa_correct :
  forall {A B : Type} (M : nfa A B) (str : list B),
    accepted (powerset_nfa M) str = true <-> naccepted M str = true.
Proof.
intuition.

unfold accepted in H.
simpl in H.
unfold naccepted.
now (rewrite (powerset_nfa_mirror M) in H).

unfold accepted.
unfold naccepted in H.
simpl.
now (rewrite <- (powerset_nfa_mirror M) in H).
Qed.
