Require Import List Bool DFA NFA.

Import ListNotations.

Definition swap_alpha_trans {A B C : Type} (M : dfa A (B * C)) (q : A) (x : C * B) : A :=
  match x with
  | (c,b) => t M q (b,c)
  end.

Definition swap_alpha_dfa {A B C : Type} (M : dfa A (B * C)) : dfa A (C * B) :=
  Build_dfa A (C * B) (swap_alpha_trans M) (s M) (F M).

Definition swap {B C : Type} (xs : list (B * C)) : list (C * B) :=
  map (fun letter => 
    match letter with
    | (b,c) => (c,b)
    end) xs.

Lemma swap_app :
  forall {B C : Type} (b : B) (c : C) (xs : list (B * C)),
    swap (xs ++ [(b,c)]) = swap xs ++ [(c,b)].
Proof.
intuition.
induction xs.
intuition.
simpl.
rewrite IHxs.
reflexivity.
Qed.

Lemma swap_alpha_mirror
  {A B C : Type} (M : dfa A (B * C)) :
    forall (str : list (B * C)),
      tStar (swap_alpha_dfa M) (s (swap_alpha_dfa M)) (swap str) = tStar M (s M) str.
Proof.
apply rev_ind.
intuition.
intuition.
rewrite tStar_step.
rewrite swap_app.
rewrite tStar_step.
simpl.
rewrite <- H.
intuition.
Qed.

Theorem swap_alpha_correct
  {A B C : Type} (M : dfa A (B * C)) :
    forall (str : list (B * C)),
      accepted (swap_alpha_dfa M) (swap str) = true <-> accepted M str = true.
Proof.
apply rev_ind.
intuition.

intuition.

unfold accepted.
rewrite tStar_step.
unfold accepted in H.
rewrite <- swap_alpha_mirror.
rewrite swap_app in H.
rewrite tStar_step in H.
intuition.

unfold accepted in H.
rewrite tStar_step in H.
unfold accepted.
rewrite swap_app.
rewrite tStar_step.
rewrite <- swap_alpha_mirror in H.
intuition.
Qed.

Definition exist_dfa_trans {A B : Type} (M : dfa A (B * C))

Definition exist_quant_dfa
  {A B C : Type} (M : dfa A (B * C)) : dfa A B :=
    Build_dfa A B.
