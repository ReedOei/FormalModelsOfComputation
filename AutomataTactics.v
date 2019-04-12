Require Import List Omega.

Import ListNotations.

Ltac rewrite_each :=
  match goal with
  | H : _ |- _ => rewrite H || rewrite <- H
  end.

Ltac simpl_hyp :=
  match goal with
  | H : ?a = ?b |- _ => progress (simpl in H)
  | H : _ |- _       => progress (rewrite app_nil_r in H)
  | _ : _ |- _       => progress (rewrite app_nil_r)
  | H : ex _ |- _    => destruct H
  end.

Hint Rewrite app_assoc : standard.

Lemma app_not_empty :
  forall (A : Type) (x : A) (xs ys : list A), xs ++ (x :: ys) <> [].
Proof.
intuition.
induction xs.
simpl in H.
inversion H.
simpl in H.
inversion H.
Qed.

Ltac impossible :=
  match goal with
  | H : _ :: _ = [] |- _ => inversion H
  | H : [] = _ :: _ |- _ => inversion H
  | H : _ ++ (_ :: _) = [] |- _ => apply app_not_empty in H; contradiction
  | H : [] = _ ++ (_ :: _) |- _ => symmetry in H; apply app_not_empty in H; contradiction
  end.

Tactic Notation "prove" "with" tactic(tac) :=
  repeat (
    intuition;
    try simpl_hyp;
    try impossible;
    try (autorewrite with standard); 
    try congruence;
    try rewrite_each;
    try tac).

Ltac prove := prove with idtac.

Tactic Notation "autoinduction" ident(x) "with" tactic(tac) :=
    induction x;

    intuition;
    simpl;
    prove with tac;

    intuition;
    simpl;
    prove with tac.

Tactic Notation "auto_rev_ind" ident(x) "with" tactic(tac) :=
    try (generalize x);
    apply rev_ind;

    intuition;
    simpl;
    prove with tac;

    intuition;
    simpl;
    prove with tac.

Tactic Notation "autoinduction" "on" ident(x) := autoinduction x with idtac.
Tactic Notation "auto_rev_ind" "on" ident(x) := auto_rev_ind x with idtac.
