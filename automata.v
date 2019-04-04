Require Import List Bool.

Import ListNotations.

Class DecEq {a : Type} := {
  deq (x y : a) : {x = y} + {x <> y}
}.

Notation "a =? b" := (if deq a b then true else false) (at level 70, no associativity).
Notation "a == b" := (deq a b) (at level 70, no associativity).

(* Extensionality *)
Fixpoint finset_eq {a : Type} `{DecEq a} (l1 : list a) (l2 : list a) : bool :=
  match l1, l2 with
  | [], []           => true
  | [], _            => false
  | _, []            => false
  | x :: xs, y :: ys => (x =? y) && finset_eq xs ys
  end.

Inductive Elem {a : Type}: a -> list a -> Prop :=
  | Here (x : a) (xs : list a) : Elem x (x :: xs)
  | There (x y : a) (xs : list a) (prf : Elem x xs) : Elem x (y :: xs).

Definition Member {a : Type} (xs : list a) := 
  { x : a | Elem x xs }.

Definition Subset {a : Type} (xs : list a) := 
  { ys : list a | forall (x : a), Elem x ys -> Elem x xs }.

Lemma elem_lemma {a : Type} `{DecEq a} : 
  forall (x y : a) (xs : list a), Elem x (y :: xs) -> x <> y -> Elem x xs.
Proof.
intuition.
induction xs.
inversion H0.
contradiction.
intuition.
inversion H0.
contradiction.
assumption.
Qed.

Lemma elem {a : Type} `{DecEq a} (x : a) (xs : list a) : {Elem x xs} + ({~ Elem x xs}).
Proof.
induction xs.
right.
intuition.
inversion H0.
intuition.
constructor.
constructor.
assumption.
induction (x == a0).

left.
rewrite a1.
constructor.
right.
contradict b.
intuition.
exact (elem_lemma x a0 xs b b0).
Qed.

Structure dfa {a b : Type} `{DecEq a} `{DecEq b} := {
  Q : list a;
  Sigma : list b;

  t : Member Q -> Member Sigma -> Member Q;
  s : Member Q;

  A : Subset Q
}.

Fixpoint tStar {a b : Type} `{DecEq a} `{DecEq b} 
               (M : dfa) (q : Member (Q M)) (str : list (Member (Sigma M))) : Member (Q M) :=
  match str with
  | []      => q
  | x :: xs => tStar M (t M q x) xs
  end.

Definition accepted {a : Type} `{DecEq a} 
                    (M : dfa) (str : list (Member (Sigma M))) : bool :=
  match tStar M (s M) str, A M with
  | exist _ final _, exist _ state_list _ => 
      if elem final state_list then true else false
  end.

Lemma prod_eq : forall {A B : Type} {a1 a2 : A} {b1 b2 : B}, a1 = a2 -> b1 = b2 -> (a1,b1) = (a2,b2).
Proof.
intuition.
rewrite H, H0.
reflexivity.
Qed.

Lemma prod_neq : forall {A B : Type} {a1 a2 : A} {b1 b2 : B}, a1 <> a2 \/ b1 <> b2 -> (a1,b1) <> (a2,b2).
Proof.
intuition.
inversion H0.
contradiction.
inversion H0.
contradiction.
Qed.

Instance dec_eq_prod (A B : Type) `(EqA : DecEq A, EqB : DecEq B) : @DecEq (prod A B) :=
  {
    deq x y := match x, y with
               | (a1,b1), (a2,b2) => 
                  match a1 == a2, b1 == b2 with
                  | left aprf, left bprf => left (prod_eq aprf bprf)
                  | _, right bprf => right (prod_neq (or_intror bprf))
                  | right aprf, _ => right (prod_neq (or_introl aprf))
                  end
               end
  }.

Fixpoint pair_with {A B : Type} (a : A) (l2 : list B) : list (A * B) :=
  match l2 with
  | []      => []
  | y :: ys => (a,y) :: pair_with a ys
  end.

Fixpoint cart_prod {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1  with
  | []      => []
  | x :: xs => pair_with x l2 ++ cart_prod xs l2
  end.

Lemma pair_with_member:
  forall {A B : Type} {l2 : list B} (a : A) (b : Member l2),
    match b with
    | exist _ v _ => Elem (a,v) (pair_with a l2)
    end.
Proof.
intuition.
induction l2.
inversion b. inversion H.
destruct b.
inversion e.
simpl.
constructor.
pose proof IHl2 (exist _ x prf).
destruct prf.
simpl.
constructor.
constructor.
simpl.
constructor.
assumption.
Qed.

Lemma elem_append_l : forall {A : Type} (x : A) {l1 l2 : list A}, Elem x l1 -> Elem x (l1 ++ l2).
Proof.
intuition.
induction l1.
inversion H.
inversion H.
simpl.
constructor.
simpl.
constructor.
exact (IHl1 prf).
Qed.

Lemma elem_append_r : forall {A : Type} (x : A) {l1 l2 : list A}, Elem x l2 -> Elem x (l1 ++ l2).
Proof.
intuition.
induction l1.
inversion H.
simpl.
rewrite H1.
assumption.
simpl.
rewrite H1.
assumption.
simpl.
constructor.
assumption.
Qed.

Lemma elem_append_only_second : 
  forall {A : Type} {l1 l2 : list A} `{DecEq A} (a : A), 
    Elem a (l1 ++ l2) -> ~(Elem a l1) -> Elem a l2.
Proof.
intuition.
induction l1.
simpl in H0.
assumption.
simpl in H0.
inversion H0.
induction l2.
rewrite app_nil_r in H0.
contradiction.
rewrite H4 in H1.
pose proof Here a0 l1.
contradiction.
induction (elem a l1).
pose proof There a a0 l1 a1.
contradiction.
exact (IHl1 prf b).
Qed.

Lemma pair_member : 
  forall {A B : Type} {l1 : list A} {l2 : list B} (a : Member l1) (b : Member l2),
    match a, b with
    | exist _ v1 _, exist _ v2 _ => Elem (v1, v2) (cart_prod l1 l2)
    end.
Proof.
intuition.
destruct a. destruct b.
induction l1.
inversion e.
inversion e.
simpl.
pose proof pair_with_member a (exist _ x0 e0).
exact (elem_append_l (a,x0) H0).
exact (elem_append_r (x,x0) (IHl1 prf)).
Qed.

Lemma make_pair :
  forall {A B : Type} {l1 : list A} {l2 : list B} (a : Member l1) (b : Member l2),
    Member (cart_prod l1 l2).
Proof.
intuition.
pose proof pair_member a b.
destruct a. destruct b.
exists (x, x0).
assumption.
Qed.

Lemma pair_with_second :
  forall {A B : Type} {l2 : list B}
         (a : A) (b : B), Elem (a,b) (pair_with a l2) -> Elem b l2.
Proof.
intuition.
induction l2.
inversion H.
inversion H.
constructor.
constructor.
exact (IHl2 prf).
Qed.

Lemma cart_prod_empty_is_empty :
  forall {A B : Type} {l1 : list A}, @cart_prod A B l1 [] = [].
Proof.
intuition.
induction l1.
intuition.
simpl.
assumption.
Qed.

Lemma cart_prod_not_empty_if :
  forall {A B : Type} {l1 : list A} {l2 : list B}, 
    cart_prod l1 l2 <> [] -> l1 <> [] /\ l2 <> [].
Proof.
intuition.
rewrite H0 in H.
simpl in H.
contradiction.
rewrite H0 in H.
rewrite cart_prod_empty_is_empty in H.
contradiction.
Qed.

Lemma cart_prod_not_empty_fi :
  forall {A B : Type} {l1 : list A} {l2 : list B}, 
     l1 <> [] /\ l2 <> [] -> cart_prod l1 l2 <> [].
Proof.
intuition.
induction l1.
contradiction.
induction l2.
contradiction.
inversion H0.
Qed.

Lemma elem_means_nonempty :
  forall {A : Type} (x : A) (l1 : list A), Elem x l1 -> l1 <> [].
Proof.
intuition.
induction l1.
inversion H.
inversion H0.
Qed.

Lemma pair_with_first :
  forall {A B : Type} {l2 : list B}
         (a a0 : A) (b : B), Elem (a,b) (pair_with a0 l2) -> a = a0.
Proof.
intuition.
induction l2.
inversion H.
inversion H.
reflexivity.
exact (IHl2 prf).
Qed.

Lemma cart_prod_second :
  forall {A B : Type} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
         (b : B), (exists (a : A), Elem (a,b) (cart_prod l1 l2)) -> Elem b l2.
Proof.
intuition.
induction l1.
inversion H.
inversion H0.
destruct H.
simpl in H.
induction (elem (x,b) (pair_with a l2)).
pose proof @pair_with_first A0 B l2 x a b a0.
rewrite H0 in a0.
exact (pair_with_second a b a0).

pose proof elem_append_only_second (x,b) H b0.
exact (IHl1 (ex_intro _ x H0)).
Qed.

Lemma pair_with_first_contra :
  forall {A B : Type} {l2 : list B} `{DecEq A}
    (a a0 : A) (b : B), a <> a0 -> ~(Elem (a,b) (pair_with a0 l2)).
Proof.
intuition.
induction l2.
inversion H1.
simpl in H1.
inversion H1.
contradiction.
exact (IHl2 prf).
Qed.

Lemma member_cart_prod :
  forall {A B : Type} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
         (x : A * B), Elem x (cart_prod l1 l2) -> 
    match x with
    | (a,b) => Elem a l1 /\ Elem b l2
    end.
Proof.
intuition.
induction l1.
inversion H.
destruct x.
inversion H.
induction (a0 == a).
rewrite a1.
split.
constructor.
exact (cart_prod_second b (ex_intro _ a0 H)).

pose proof @pair_with_first_contra A0 B l2 EqA a0 a b b0.
pose proof dec_eq_prod A0 B EqA EqB.
pose proof elem_append_only_second (a0, b) H H1.
constructor.
pose proof IHl1 H3.
intuition.
constructor.
assumption.
exact (cart_prod_second b (ex_intro _ a0 H)).

split.
simpl in H.
induction (a0 == a).
rewrite a1.
constructor.
pose proof @pair_with_first_contra A0 B l2 EqA a0 a b b0.
pose proof dec_eq_prod A0 B EqA EqB.
pose proof elem_append_only_second (a0, b) H H1.
constructor.
pose proof IHl1 H3.
intuition.
exact (cart_prod_second b (ex_intro _ a0 H)).
Qed.

Definition and_dfa_trans {A B C : Type} `{EqA : DecEq A, EqB : DecEq B, EqC : DecEq C}
                         (M : @dfa A B EqA EqB) (N : dfa)
                         (q : Member (cart_prod (Q M) (Q N))) 
                         (s : Member (Sigma M)) : Member (cart_prod (Q M) (Q N)) :=
  match q with
  | exist _ (q1,q2) _ => make_pair (t M q1 s) (t N q2 s)
  end.

Definition and_dfa {A B C : Type} `{EqA : DecEq A, EqB : DecEq B, EqC : DecEq C}
                   (M : @dfa A B EqA EqB) (N : @dfa C B EqC EqB) : Sigma M = Sigma N -> dfa :=
  match s M, s N with
  | exist _ sm _, exist _ sn _ =>
      let newQ := cart_prod (Q M) (Q N) in
      let newSigma := Sigma M in
      Build_dfa (A * C) B (dec_eq_prod a c EqA EqC) EqB
                newQ newSigma and_dfa_trans
  end.
