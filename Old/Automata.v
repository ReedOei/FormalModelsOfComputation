Require Import List PeanoNat Omega Bool MSets MSetDecide Ensembles.

Import ListNotations.

Require Import Strings Sets AutomataTactics.

Structure dfa := {
  Q : S.t;
  Sigma : S.t;

  t : member Q -> member Sigma -> member Q;
  s : member Q;

  A : subset Q;
}.

Arguments Q {d}.
Arguments Sigma {d}.
Arguments t {d} _ _.
Arguments s {d}.
Arguments A {d}.

Fixpoint tStar {M : dfa}
               (q : member (@Q M))
               (str : string Sigma)
               : member Q := 
  match str with
  | []      => q
  | x :: xs => tStar (t q x) xs
  end.

Definition accepted {M : dfa} (x : string Sigma) : bool := 
  match @A M, @tStar M s x with
  | exist _ accepted _, exist _ final _ => S.mem final accepted
  end.

Definition accepted_lang (M : dfa) : language Sigma := fun str => @accepted M str = true.

Definition false_dfa {Sigma : S.t} : dfa := 
  Build_dfa (S.singleton 0) Sigma (fun q => fun x => q) (exist _ 0 eq_refl)
    empty_set.

Definition true_dfa {Sigma : S.t} : dfa :=
  Build_dfa (S.singleton 0) Sigma (fun q => fun x => q) (exist _ 0 eq_refl) 
    full_set.

Lemma false_trans_does_nothing : 
  forall (Sigma : S.t) (str : string Sigma), @tStar (@false_dfa Sigma) s str = s.
Proof.
autoinduction str.
Qed.

Lemma true_trans_does_nothing : 
  forall (Sigma : S.t) (str : string Sigma), @tStar (@true_dfa Sigma) s str = s.
Proof.
autoinduction str.
Qed.

Lemma false_accepts_empty : 
  forall {Sigma : S.t}, 
    accepted_lang false_dfa = empty_language Sigma.
Proof.
simplify.
apply Extensionality_Ensembles.
simplify.
inversion H.
unfold accepted in H1.
rewrite false_trans_does_nothing in H1.
inversion H1.
Qed.

Lemma true_accepts_full : 
  forall {Sigma : S.t}, 
    accepted_lang true_dfa = full_language Sigma.
Proof.
simplify.
apply Extensionality_Ensembles.
simplify.
unfold accepted_lang.
unfold accepted.
rewrite true_trans_does_nothing.
simplify.
Qed.

Definition and_states (M N : dfa) : S.t 

Definition and_dfa (M N : dfa) : dfa :=
  Build_dfa (and_states M N).

Definition even_len_states := S.union (S.singleton 0) (S.singleton 1).

Lemma even_len_states_has_two : forall (n : nat), S.mem (S (S n)) even_len_states = true -> False.
Proof.
simplify.
Qed.

Lemma absurd : forall {A}, False -> A.
Proof.
intuition.
Qed.

Definition even_len_dfa_trans {Sigma : S.t} 
  (q : member even_len_states) (x : member Sigma) : member even_len_states :=
  match q with
  | exist _ 0 _ => exist _ 1 eq_refl
  | exist _ 1 _ => exist _ 0 eq_refl
  | exist _ (S (S n)) prf => absurd (even_len_states_has_two n prf)
  end.

Definition even_len_dfa {Sigma : S.t} : dfa :=
  Build_dfa even_len_states Sigma
    even_len_dfa_trans (exist _ 0 eq_refl) (@singleton_subset even_len_states 0 eq_refl).

Lemma even_dfa_accepted_is_0 : 
  forall {Sigma : S.t}, @A (@even_len_dfa Sigma) = @singleton_subset even_len_states 0 eq_refl.
Proof.
simplify.
Qed.

Fixpoint even_len {A} (str : list A) : bool :=
  match str with
  | [] => true
  | [_] => false
  | _ :: xs => negb (even_len xs)
  end.

Lemma neg_twice_true : forall (b : bool), negb (negb b) = true <-> b = true.
Proof.
simplify.
induction b.
reflexivity.
inversion H.
rewrite H.
simplify.
Qed.

Lemma even_len_add_is_odd : 
  forall {A} (str : list A) (x : A),
    even_len (x :: str) = true <-> even_len str = false.
Proof.
simplify.
inversion H.
destruct str.
inversion H1.
apply negb_true_iff.
assumption.

unfold negb.
rewrite H.
destruct str.
inversion H.
reflexivity.
Qed.

Lemma even_len_dfa_alternates : 
  forall {Sigma : S.t} (str : string Sigma) (a : member Sigma),
    tStar (@s even_len_dfa) str = exist _ 0 eq_refl <-> 
    tStar (@s even_len_dfa) (a :: str) = exist _ 1 eq_refl.
Proof.
simplify.
induction str.
simplify.
destruct str.
simplify.
inversion H.
unfold tStar in IHstr.
simpl in IHstr.


Lemma even_len_dfa_works : 
  forall {Sigma : S.t} (str : string Sigma), 
    @accepted even_len_dfa str = true -> even_len str = true.
Proof.
simplify.
induction str.
simplify.
unfold accepted in H.
pose proof @even_dfa_accepted_is_0 Sigma0.
rewrite H0 in H.
unfold singleton_subset in H.
destruct tStar.
rewrite S.mem_spec in H.
pose proof mem_singleton_eq x 0 H.
