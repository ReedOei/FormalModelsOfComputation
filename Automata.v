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
