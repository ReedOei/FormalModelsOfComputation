Require Import List Bool.

Import ListNotations.

Structure dfa (A B : Type) := {
  t : A -> B -> A;
  s : A;

  F : A -> Prop;
  F_dec : forall (x : A), {F x} + {~F x}
}.

Arguments t {A} {B}.
Arguments s {A} {B}.
Arguments F {A} {B}.
Arguments F_dec {A} {B}.

Fixpoint tStar {A B : Type}
               (M : dfa A B) (q : A) (str : list B) : A :=
  match str with
  | []      => q
  | x :: xs => tStar M (t M q x) xs
  end.

Definition accepted {A B : Type}
                    (M : dfa A B) (str : list B) : bool :=
  if F_dec M (tStar M (s M) str) then true else false.

Definition and_dfa_trans {A B C : Type}
                    (M : dfa A B) (N : dfa C B)
                    (q : A * C) 
                    (s : B) : A * C := 
  match q with
  | (qm, qn) => (t M qm s, t N qn s)
  end.

Definition and_dfa_f_dec_bool
  {A B C : Type}
  (M : dfa A B) (N : dfa C B)
  (q : A * C) : bool :=
  match q with
  | (a,c) => 
     match F_dec M a, F_dec N c with
     | left _, left _ => true
     | _, right _ => false
     | right _, _ => false
     end
  end.

Definition and_dfa_f_dec
  {A B C : Type}
  (M : dfa A B) (N : dfa C B)
  (q : A * C) : Prop := and_dfa_f_dec_bool M N q = true.

Lemma and_dfa_final_dec
  {A B C : Type}
                   (M : dfa A B) (N : dfa C B) : 
  forall (x : A * C), {and_dfa_f_dec M N x} + {~and_dfa_f_dec M N x}.
Proof.
intuition.
unfold and_dfa_f_dec.
unfold and_dfa_f_dec_bool.
induction (F_dec M a).
induction (F_dec N b). intuition. intuition.
induction (F_dec N b). intuition. intuition.
Qed.

Definition and_dfa {A B C : Type}
                   (M : dfa A B) (N : dfa C B) : dfa (A * C) B :=
  Build_dfa (A * C) B
            (and_dfa_trans M N)
            (s M, s N)
            (and_dfa_f_dec M N)
            (and_dfa_final_dec M N).

Definition tStar_step_prop 
   {A B : Type}
   (M : dfa A B)
   (str : list B) : Prop :=
    forall (q : A) (x : B),  tStar M q (str ++ [x]) = t M (tStar M q str) x.

Lemma tStar_step :
  forall {A B : Type}
   (M : dfa A B)
   (str : list B), tStar_step_prop M str.
Proof.
intros.

induction str.
unfold tStar_step_prop.
intuition.

unfold tStar_step_prop.
unfold tStar_step_prop in IHstr.
intuition.
simpl.
exact (IHstr (t M q a) x).
Qed.

Theorem and_dfa_mirror_m :
  forall {A B C : Type}
   (M : dfa A B) (N : dfa C B)
   (str : list B),
    tStar M (s M) str = fst (tStar (and_dfa M N) (s (and_dfa M N)) str).
Proof.
intros.

revert str.
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

Theorem and_dfa_mirror_n :
  forall {A B C : Type}
   (M : dfa A B) (N : dfa C B)
   (str : list B),
    tStar N (s N) str = snd (tStar (and_dfa M N) (s (and_dfa M N)) str).
Proof.
intros.

revert str.
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
  forall {A B C : Type}
         (M : dfa A B) (N : dfa C B) 
         (str : list B),
          accepted (and_dfa M N) str = true <-> accepted M str && accepted N str = true.
Proof.
intros.
unfold accepted.
rewrite (and_dfa_mirror_m M N str).
rewrite (and_dfa_mirror_n M N str).
destruct (tStar (and_dfa M N) (s (and_dfa M N)) str).
simpl.

intuition.

induction (and_dfa_final_dec M N (a,c)).
unfold and_dfa_f_dec, and_dfa_f_dec_bool in a0.

induction (F_dec M a).
induction (F_dec N c). intuition. intuition.
induction (F_dec N c). intuition. intuition.

induction (F_dec M a).
induction (F_dec N c). intuition. intuition.
induction (F_dec N c). intuition. intuition.

induction (and_dfa_final_dec M N (a,c)).
intuition.
unfold and_dfa_f_dec, and_dfa_f_dec_bool in b.

induction (F_dec M a).
induction (F_dec N c). intuition. intuition.
induction (F_dec N c). intuition. intuition.
Qed.

Definition not_dfa_f_bool
  {A B : Type}
   (M : dfa A B) (q : A) : bool := if F_dec M q then false else true.

Definition not_dfa_f
  {A B : Type}
   (M : dfa A B) (q : A) : Prop := not_dfa_f_bool M q = true.

Lemma not_dfa_f_dec
  {A B : Type}
   (M : dfa A B) (q : A) : {not_dfa_f M q} + {~not_dfa_f M q}.
Proof.
intuition.
unfold not_dfa_f, not_dfa_f_bool.
induction (F_dec M q).
intuition.
intuition.
Qed.

Definition not_dfa
   {A B : Type}
   (M : dfa A B) : dfa A B :=
  Build_dfa A B (t M) (s M) (not_dfa_f M) (not_dfa_f_dec M).

Theorem not_dfa_mirror
   {A B : Type}
   (M : dfa A B) : forall (str : list B), tStar M (s M) str = tStar (not_dfa M) (s M) str.
Proof.
apply rev_ind.

intuition.

intuition.
rewrite tStar_step.
rewrite tStar_step.
simpl.
rewrite H.
intuition.
Qed.

Theorem not_dfa_correct
   {A B : Type}
   (M : dfa A B) : 
   forall (str : list B), accepted M str = true <-> accepted (not_dfa M) str = false.
Proof.
intros.
unfold accepted.
simpl.
rewrite not_dfa_mirror.

intuition.
induction (not_dfa_f_dec M (tStar (not_dfa M) (s M) str)).
unfold not_dfa_f, not_dfa_f_bool in a.
induction (F_dec M (tStar (not_dfa M) (s M) str)).
intuition.
intuition.
intuition.

induction (not_dfa_f_dec M (tStar (not_dfa M) (s M) str)).
unfold not_dfa_f, not_dfa_f_bool in a.
induction (F_dec M (tStar (not_dfa M) (s M) str)).
intuition.
intuition.
unfold not_dfa_f, not_dfa_f_bool in b.
induction (F_dec M (tStar (not_dfa M) (s M) str)).
intuition.
intuition.
Qed.
