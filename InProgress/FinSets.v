Require Import List Bool.

Import ListNotations.

Class DecEq {a : Type} := {
  deq (x y : a) : {x = y} + {x <> y}
}.

Notation "a =? b" := (if deq a b then true else false) (at level 70, no associativity).
Notation "a == b" := (deq a b) (at level 70, no associativity).

Inductive Elem {a : Type}: a -> list a -> Prop :=
  | Here (x : a) (xs : list a) : Elem x (x :: xs)
  | There (x y : a) (xs : list a) (prf : Elem x xs) : Elem x (y :: xs).

Definition Member {a : Type} (xs : list a) := 
  { x : a | Elem x xs }.

Definition IsSubset {A : Type} (ys : list A) (xs : list A) := 
  forall (x : A), Elem x ys -> Elem x xs.

Definition Subset {a : Type} (xs : list a) := 
  { ys : list a | IsSubset ys xs }.

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

Lemma subset_of_empty_is_empty :
  forall {A : Type} (ys : list A), IsSubset ys [] -> ys = [].
Proof.
intuition.
induction ys.
reflexivity.

pose proof H a (Here a ys).
inversion H0.
Qed.

Definition FinType (A : Type) := exists (all : list A), forall (x : A), Elem x all.

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
  forall {A B : Type} {l2 : list B} (a : A) {b : B} (prf : Elem b l2), 
    Elem (a,b) (pair_with a l2).
Proof.
intuition.
induction l2.
inversion prf.
inversion prf.
simpl.
constructor.
simpl.
constructor.
exact (IHl2 prf0).
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
  forall {A B : Type} {l1 : list A} {l2 : list B} {x : A} {y : B} (a : Elem x l1) (b : Elem y l2),
    Elem (x, y) (cart_prod l1 l2).
Proof.
intuition.
induction l1.
inversion a.

inversion a.
simpl.

exact (elem_append_l (a0,y) (pair_with_member a0 b)).
simpl.
exact (elem_append_r (x,y) (IHl1 prf)).
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
pose proof @pair_with_first A B l2 x a b a0.
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

pose proof @pair_with_first_contra A B l2 EqA a0 a b b0.
pose proof dec_eq_prod A B EqA EqB.
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
pose proof @pair_with_first_contra A B l2 EqA a0 a b b0.
pose proof dec_eq_prod A B EqA EqB.
pose proof elem_append_only_second (a0, b) H H1.
constructor.
pose proof IHl1 H3.
intuition.
exact (cart_prod_second b (ex_intro _ a0 H)).
Qed.

Lemma cart_prod_of_subset : 
  forall {A B : Type} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
         (s1 : Subset l1) (s2 : Subset l2), 
          match s1, s2 with
          | exist _ l1' _, exist _ l2' _ => 
              forall (a : A) (b : B), Elem (a,b) (cart_prod l1' l2') -> Elem (a,b) (cart_prod l1 l2)
          end.
Proof.
intuition.
destruct s1. destruct s2.
intuition.
destruct (member_cart_prod (a,b) H).
exact (pair_member (i a H0) (i0 b H1)).
Qed.

Definition cart_prod_subset 
  {A B : Type} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
  (s1 : Subset l1) (s2 : Subset l2) : list (A * B) :=
  match s1, s2 with
  | exist _ l1' _, exist _ l2' _ => cart_prod l1' l2'
  end.

Lemma make_subset_prod 
  {A B : Type} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
  (s1 : Subset l1) (s2 : Subset l2) : IsSubset (cart_prod_subset s1 s2) (cart_prod l1 l2).
Proof.
unfold IsSubset.
intuition.
pose proof cart_prod_of_subset s1 s2.
destruct x.
unfold cart_prod_subset in H.
destruct s1. destruct s2.
exact (H0 a b H).
Qed.

Lemma empty_has_no_app :
  forall {A : Type} (x : A) (xs : list A),
    xs ++ [x] <> [].
Proof.
intuition.
induction xs.
simpl in H.
discriminate.
inversion H.
Qed.

Lemma app_non_empty :
  forall {A : Type} (xs : list A), 
    (exists (x : A) (ys : list A), xs = ys ++ [x])
    <-> 
    (exists (a : A) (zs : list A), a :: zs = xs).
Proof.
intuition.
induction xs.

destruct H. destruct H.
symmetry in H.
pose proof empty_has_no_app x x0.
contradiction.

exists a. exists xs.
reflexivity.

induction xs.

destruct H. destruct H.
inversion H.

destruct xs.
inversion H.
exists a. exists [].
intuition.
cut (exists (a : A) (zs : list A), a :: zs = a0 :: xs).
intuition. destruct H1. destruct H1.
exists x. exists (a :: x0).
simpl.
rewrite H1.
reflexivity.

exists a0. exists xs.
reflexivity.
Qed.

Lemma prod_of_fin_is_fin :
  forall {A B : Type}, FinType A -> FinType B -> FinType (A * B).
Proof.
intuition.
unfold FinType.
destruct H.
destruct H0.
exists (cart_prod x x0).
intuition.
exact (pair_member (H a) (H0 b)).
Qed.
