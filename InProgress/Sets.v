Require Import List Bool.

Import ListNotations.

Class DecEq {A : Set} := {
  deq (x y : A) : {x = y} + {x <> y}
}.

Class Order {A : Set} := {
  equiv : A -> A -> Prop;
  lt : A -> A -> Prop;
  equiv_from_eq : forall (x y : A), x = y -> equiv x y;
  equiv_refl : forall (x : A), equiv x x;
  equiv_sym : forall (x y : A), equiv x y -> equiv y x;
  equiv_trans : forall (x y z : A), equiv x y -> equiv y z -> equiv x z
}.

Notation "a =? b" := (if deq a b then true else false) (at level 70, no associativity).
Notation "a == b" := (deq a b) (at level 70, no associativity).
Notation "a < b" := (lt a b) (at level 70, no associativity).
Notation "a === b" := (equiv a b) (at level 70, no associativity).
Notation "a <= b" := (lt a b \/ equiv a b) (at level 70, no associativity).

Class StrictPartialOrder {A : Set} `{Ord : Order A} := {
  lt_irrefl : forall (x y : A), x === y -> ~(x < y);
  lt_trans : forall (a b c : A), a < b -> b < c -> a < c;
}.

Lemma lt_antisym :
  forall {A : Set} `{Ord : StrictPartialOrder A} (a b : A), a < b -> ~(b < a).
Proof.
intuition.
exact (lt_irrefl a a (equiv_refl a) (lt_trans a b a H H0)).
Qed.

Class Total {A : Set} `{Ord : Order A} := {
  tot_antisym : forall (a b : A), a <= b -> b <= a -> a === b;
  tot_trans : forall (a b c : A), a <= b -> b <= c -> a <= c;
  tot_connex : forall (a b : A), a <= b \/ b <= a
}.

Inductive Elem {a : Set} : a -> list a -> Prop :=
  | Here (x : a) (xs : list a) : Elem x (x :: xs)
  | There (x y : a) (xs : list a) (prf : Elem x xs) : Elem x (y :: xs).

Definition Member {a : Set} (xs : list a) :=
  { x : a | Elem x xs }.

Inductive Distinct {A : Set} : list A -> Prop :=
  | NilDistinct : Distinct []
  | ConsDistinct (x : A) (xs : list A) : ~(Elem x xs) -> Distinct xs -> Distinct (x :: xs).

Inductive Sorted {A : Set} `{Ord : Order A} : list A -> Prop :=
  | Empty : Sorted []
  | Singleton (x : A) : Sorted [x]
  | Cons (x y : A) (xs : list A) (prf : Sorted (y :: xs)) : x < y -> Sorted (x :: y :: xs).

Definition IsSubset {A : Set} (ys : list A) (xs : list A) := 
  Distinct ys /\ forall (x : A), Elem x ys -> Elem x xs.

Definition Subset {a : Set} (xs : list a) :=
  { ys : list a | IsSubset ys xs }.

Definition set (A : Set) := A -> bool.
Definition subset {A : Set} (supset : set A) :=
  { subset : set A | forall (x : A), subset x = true -> supset x = true }.
Definition finset {A : Set} `{Ord : Order A} (s : set A) := 
  { xs : list A | Sorted xs /\ forall (x : A), s x = true -> Elem x xs }.

Definition FinType (A : Set) `{Ord : Order A} :=
  { xs : list A | Sorted xs /\ forall (x : A), Elem x xs }.

Lemma lt_implies_neq : 
  forall {A : Set} `{Ord : StrictPartialOrder A} (x y : A), x < y -> x <> y.
Proof.
intuition.
exact (lt_irrefl x y (equiv_from_eq x y H0) H).
Qed.

Lemma sorted_remove :
  forall {A : Set} `{Ord : StrictPartialOrder A} (x y : A) (xs : list A),
    Sorted (x :: y :: xs) -> Sorted (x :: xs).
Proof.
intuition.
inversion H.
inversion prf.
constructor.
constructor.
assumption.
exact (lt_trans x y y1 H1 H5).
Qed.

Lemma sorted_terminal_seg :
  forall {A : Set} `{Ord : StrictPartialOrder A} (x y z : A) (xs : list A),
    x < y -> Sorted (y :: xs) -> Elem z xs -> x < z.
Proof.
intuition.
induction xs.
inversion H1.
inversion H0.
inversion H1.
exact (lt_trans x y a H H3).
apply sorted_remove in H0.
intuition.
Qed.

Lemma lt_sorted_not_elem :
  forall {A : Set} `{Ord : StrictPartialOrder A} (x y : A) (xs : list A),
    x < y -> Sorted (y :: xs) -> ~Elem x xs.
Proof.
intuition.
induction xs.
inversion H1.

inversion H0.
inversion H1.
pose proof lt_trans x y a H H3.
exact (lt_irrefl x a (equiv_from_eq x a H8) H7).
apply sorted_remove in H0.
intuition.
Qed.

Lemma sorted_implies_distinct :
  forall {A : Set} `{Ord : StrictPartialOrder A} (xs : list A), Sorted xs -> Distinct xs.
Proof.
intuition.
induction xs.
constructor.
inversion H.
constructor.
intuition.
inversion H0.
constructor.
rewrite H2 in prf.
intuition.
constructor.
rewrite <- H2 in prf.
pose proof lt_sorted_not_elem a y xs0 H1 prf.
intuition.
inversion H5.
exact (lt_irrefl a y (equiv_from_eq a y H8) H1).
intuition.
rewrite H2.
assumption.
Qed.

Definition set_eq {A : Set} (s1 s2 : set A) := 
  forall (x : A), s1 x = true <-> s2 x = true.

Definition set_cart_prod {A B : Set} (s1 : set A) (s2 : set B) : set (A * B) :=
  fun x => let (v1,v2) := x in s1 v1 && s2 v2.

Instance ord_prod (A B : Set) `(OrdA : Order A, OrdA : Order B) : @Order (prod A B):=
  {
    equiv x y :=
      match x, y with
      | (x1,x2),(y1,y2) => equiv x1 y1 /\ equiv x2 y2
      end;
    lt x y :=
      match x, y with
      | (x1,x2),(y1,y2) => lt x1 y1 \/ (x1 = y1 /\ lt x2 y2)
      end
  }.
Proof.
intuition.
inversion H.
intuition.
apply equiv_from_eq.
reflexivity.
apply equiv_from_eq.
reflexivity.

intuition.
apply equiv_refl.
apply equiv_refl.

intuition.
destruct y.
intuition.
apply equiv_sym.
assumption.
apply equiv_sym.
assumption.

intuition.
destruct z.
intuition.
exact (equiv_trans a a0 a1 H1 H).
exact (equiv_trans b b0 b1 H2 H3).
Defined.

Lemma elem_lemma {A : Set} `{DecEq A} : 
  forall (x y : A) (xs : list A), Elem x (y :: xs) -> x <> y -> Elem x xs.
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

Lemma elem {A : Set} `{DecEq A} (x : A) (xs : list A) : {Elem x xs} + ({~ Elem x xs}).
Proof.
induction xs.
right.
intuition.
inversion H0.
intuition.
constructor.
constructor.
assumption.
induction (x == a).

left.
rewrite a0.
constructor.
right.
contradict b.
intuition.
exact (elem_lemma x a xs b b0).
Qed.

Lemma subset_of_empty_is_empty :
  forall {A : Set} (ys : list A), IsSubset ys [] -> ys = [].
Proof.
intuition.
induction ys.
reflexivity.

destruct H.

pose proof H0 a (Here a ys).
inversion H1.
Qed.

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

Instance dec_eq_prod (A B : Set) `(EqA : DecEq A, EqB : DecEq B) : @DecEq (prod A B) :=
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

Fixpoint pair_with {A B : Set} (a : A) (l2 : list B) : list (A * B) :=
  match l2 with
  | []      => []
  | y :: ys => (a,y) :: pair_with a ys
  end.

Fixpoint cart_prod {A B : Set} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1  with
  | []      => []
  | x :: xs => pair_with x l2 ++ cart_prod xs l2
  end.

Lemma pair_with_member:
  forall {A B : Set} {l2 : list B} (a : A) {b : B} (prf : Elem b l2), 
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

Lemma elem_append_l : forall {A : Set} (x : A) {l1 l2 : list A}, Elem x l1 -> Elem x (l1 ++ l2).
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

Lemma elem_append_r : forall {A : Set} (x : A) {l1 l2 : list A}, Elem x l2 -> Elem x (l1 ++ l2).
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
  forall {A : Set} {l1 l2 : list A} `{DecEq A} (a : A), 
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
  forall {A B : Set} {l1 : list A} {l2 : list B} {x : A} {y : B} (a : Elem x l1) (b : Elem y l2),
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
  forall {A B : Set} {l2 : list B}
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
  forall {A B : Set} {l1 : list A}, @cart_prod A B l1 [] = [].
Proof.
intuition.
induction l1.
intuition.
simpl.
assumption.
Qed.

Lemma cart_prod_not_empty_if :
  forall {A B : Set} {l1 : list A} {l2 : list B}, 
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
  forall {A B : Set} {l1 : list A} {l2 : list B}, 
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
  forall {A : Set} (x : A) (l1 : list A), Elem x l1 -> l1 <> [].
Proof.
intuition.
induction l1.
inversion H.
inversion H0.
Qed.

Lemma pair_with_first :
  forall {A B : Set} {l2 : list B}
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
  forall {A B : Set} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
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
  forall {A B : Set} {l2 : list B} `{DecEq A}
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
  forall {A B : Set} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
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
pose proof IHl1 H4.
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
pose proof IHl1 H4.
intuition.
exact (cart_prod_second b (ex_intro _ a0 H)).
Qed.

Lemma cart_prod_of_subset : 
  forall {A B : Set} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
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
destruct i. destruct i0.
exact (pair_member (H3 a H0) (H5 b H1)).
Qed.

Definition cart_prod_subset 
  {A B : Set} {l1 : list A} {l2 : list B} `{EqA : DecEq A, EqB : DecEq B}
  (s1 : Subset l1) (s2 : Subset l2) : list (A * B) :=
  match s1, s2 with
  | exist _ l1' _, exist _ l2' _ => cart_prod l1' l2'
  end.

(* Lemma make_subset_prod 
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
Qed. *)

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

Definition upper_bound
  {A : Set} `{OrdA : Order A} (x : A) (xs : list A) := forall (y : A), Elem y xs -> y < x.

Definition upper_bounds
  {A : Set} `{OrdA : Order A} (xs ys : list A) :=
    forall (y : A), Elem y ys -> upper_bound y xs.

Lemma upper_bound_elim :
  forall {A : Set} `{OrdA : Order A} (x y : A) (xs : list A),
    upper_bound y (x :: xs) -> upper_bound y xs.
Proof.
intuition.
intros z.
intuition.
exact (H z (There z x xs H0)).
Qed.

Lemma upper_bounds_elim_r :
  forall {A : Set} `{OrdA : Order A} (y : A) (xs ys : list A),
    upper_bounds xs (y :: ys) -> upper_bounds xs ys.
Proof.
intuition.
intro z.
intuition.
exact (H z (There z y ys H0)).
Qed.

Lemma upper_bounds_elim_l :
  forall {A : Set} `{OrdA : Order A} (x : A) (xs ys : list A),
    upper_bounds (x :: xs) ys -> upper_bounds xs ys.
Proof.
intuition.
intro z.
intuition.
pose proof H z H0.
intro x1.
intuition.
exact (H1 x1 (There x1 x xs H2)).
Qed.

Lemma upper_bounds_of_empty :
  forall {A : Set} `{OrdA : Order A} (xs : list A), upper_bounds [] xs.
Proof.
intuition.
intros x.
intuition.
intros y.
intuition.
inversion H0.
Qed.

Lemma sort_res :
  forall {A : Set} `{OrdA : StrictPartialOrder A} 
    (a0 y : A) (xs ys : list A),
      (Sorted (y :: ys) -> Sorted ((a0 :: xs) ++ ys)) -> Sorted (y :: ys) -> Sorted (xs ++ ys).
Proof.
intuition.
simpl in H1.
inversion H1.
constructor.
assumption.
Qed.

Lemma app_sorted_cons :
  forall {A : Set} `{OrdA : StrictPartialOrder A} (y : A) (xs ys : list A),
    Sorted xs -> Sorted (y :: ys) -> upper_bound y xs -> Sorted (xs ++ ys).
Proof.
intuition.
induction ys.
rewrite app_nil_r.
intuition.

induction xs.
simpl.
inversion H0.
assumption.

inversion H.
simpl.
constructor.
inversion H0.
assumption.
inversion H0.
exact (lt_trans a0 y a (H1 a0 (Here a0 xs)) H5).
simpl.
constructor.
rewrite H4 in prf.
apply upper_bound_elim in H1.
apply sorted_remove in H0.
pose proof sort_res a0 y xs ys IHys.
intuition.
rewrite <- H4 in H5.
intuition.
intuition.
Qed.

Lemma app_upper_bound :
  forall {A : Set} `{OrdA : StrictPartialOrder A} (y : A) (xs : list A),
    Sorted xs -> upper_bound y xs -> Sorted (xs ++ [y]).
Proof.
intuition.
induction xs.
simpl.
constructor.
simpl.
inversion H.
simpl.
constructor.
constructor.
exact (H0 a (Here a xs)).
rewrite H3 in prf.
apply upper_bound_elim in H0.
intuition.
rewrite <- H3 in H5.
simpl.
simpl in H5.
constructor.
assumption.
assumption.
Qed.

Definition app_sorted_prop {A : Set} `{OrdA : StrictPartialOrder A} (ys : list A) :=
  forall (xs : list A), Sorted xs -> Sorted ys -> upper_bounds xs ys -> Sorted (xs ++ ys).

Lemma app_elem :
  forall {A : Set} (x : A) (xs : list A), Elem x (xs ++ [x]).
Proof.
intuition.
induction xs.
simpl.
constructor.
simpl.
constructor.
assumption.
Qed.

Lemma sorted_app_r :
  forall {A : Set} `{OrdA : StrictPartialOrder A} (x : A) (xs : list A), 
    Sorted xs -> upper_bound x xs -> Sorted (xs ++ [x]).
Proof.
intuition.
induction xs.
simpl.
constructor.
inversion H.
simpl.
constructor.
constructor.
exact (H0 a (Here a xs)).
rewrite H3 in prf.
apply upper_bound_elim in H0.
intuition.
rewrite <- H3 in H5.
simpl.
constructor.
intuition.
assumption.
Qed.

Lemma sorted_elim_r :
  forall {A : Set} `{OrdA : StrictPartialOrder A} (x : A) (xs : list A),
    Sorted (xs ++ [x]) -> Sorted xs.
Proof.
intuition.
induction xs.
constructor.

simpl in H.
inversion H.
pose proof app_non_empty (xs ++ [x]).
intuition.
cut (exists (x0 : A) (ys : list A), xs ++ [x] = ys ++ [x0]).
intuition.
destruct H5. destruct H4.
rewrite <- H4 in H2.
inversion H2.
exists x. exists xs.
reflexivity.

rewrite H2 in prf.
intuition.
rewrite <- H2 in prf.
destruct xs.
constructor.
constructor.
assumption.
inversion H2.
rewrite H5 in H1.
assumption.
Qed.

Lemma upper_bounds_elim_r_sorted : 
  forall {A : Set} `{OrdA : StrictPartialOrder A} (y : A) (xs ys : list A),
    upper_bounds xs (ys ++ [y]) -> upper_bounds xs ys.
Proof.
intuition.
intros u.
intuition.
intros x.
intuition.
pose proof H u (elem_append_l u H0).
exact (H2 x H1).
Qed.

Lemma app_not_empty :
  forall {A : Set} (x : A) (xs : list A), xs ++ [x] <> [].
Proof.
intuition.
pose proof app_non_empty (xs ++ [x]).
intuition.
cut (exists (x0 : A) (ys : list A), xs ++ [x] = ys ++ [x0]).
intuition.
destruct H3. destruct H2.
rewrite <- H2 in H.
inversion H.
exists x. exists xs.
reflexivity.
Qed.

Lemma sorted_app_is_upper_bound :
  forall {A : Set} `{OrdA : StrictPartialOrder A} (x : A) (xs : list A),
    Sorted (xs ++ [x]) -> upper_bound x xs.
Proof.
intuition.
induction xs.
intros y.
intuition.
inversion H0.
intros y.
intuition.
simpl in H.
inversion H.
pose proof app_not_empty x xs.
symmetry in H3.
contradiction.
rewrite H3 in prf.
intuition.
inversion H0.
destruct xs.
inversion H3.
rewrite H9 in H2.
assumption.
inversion H3.
pose proof (H4 a0 (Here a0 xs)).
rewrite H9 in H2.
exact (lt_trans a a0 x H2 H6).
exact (H4 y prf0).
Qed.

Lemma upper_bound_trans : 
  forall {A : Set} `{OrdA : StrictPartialOrder A} (x y : A) (xs ys : list A),
    upper_bounds xs (y :: ys) -> upper_bound x (y :: ys) -> upper_bound x (xs ++ y :: ys).
Proof.
intuition.
induction xs.
intuition.
pose proof H.
apply upper_bounds_elim_l in H1.
intuition.
intro u.
intuition.
simpl in H3.
inversion H3.
pose proof H y (Here y ys) a (Here a xs).
pose proof H0 y (Here y ys).
exact (lt_trans a y x H5 H8).
exact (H2 u prf).
Qed.

Lemma app_sorted :
  forall {A : Set} `{OrdA : StrictPartialOrder A},
    forall (ys : list A), app_sorted_prop ys.
Proof.
intros A OrdA Ord.
apply rev_ind.
unfold app_sorted_prop.
intuition.
rewrite app_nil_r.
assumption.
intuition.
unfold app_sorted_prop.
intuition.
pose proof H2 x (app_elem x l).
unfold app_sorted_prop in H.
pose proof H xs H0.
rewrite app_assoc.
pose proof H1.
apply sorted_elim_r in H5.
intuition.
pose proof H2.
apply upper_bounds_elim_r_sorted in H2.
intuition.
apply sorted_app_r.
assumption.
pose proof sorted_app_is_upper_bound x l H1.
destruct l.
rewrite app_nil_r.
assumption.
exact (upper_bound_trans x a xs l H2 H6).
Qed.

Lemma pair_with_sorted :
  forall {A B : Set} `{OrdA : Order A, OrdB : Order B} (x : A) (ys : list B),
    Sorted ys -> Sorted (pair_with x ys).
Proof.
intuition.
induction ys.
simpl.
constructor.
simpl.
inversion H.
simpl.
constructor.
rewrite H2 in prf.
pose proof IHys prf.
simpl.
constructor.
rewrite <- H2 in H3.
intuition.
intuition.
right.
intuition.
Qed.

Lemma cart_prod_sorted :
  forall {A B : Set} `{OrdA : StrictPartialOrder A, OrdB : StrictPartialOrder B} (xs : list A) (ys : list B),
    Sorted xs -> Sorted ys -> Sorted (cart_prod xs ys).
Proof.
intuition.
induction xs.
simpl.
constructor.
simpl.
pose proof @app_sorted (A * B) (ord_prod A B Ord Ord0).
unfold app_sorted_prop in H1.
pose proof H1 (cart_prod xs ys) (pair_with a ys).

Lemma prod_of_fin_is_fin :
  forall {A B : Set} `{OrdA : Order A, OrdB : Order B}, 
    FinType A -> FinType B -> FinType (A * B).
Proof.
intuition.
unfold FinType.
destruct H.
destruct H0.
exists (cart_prod x x0).
intuition.
exact (pair_member (e a) (e0 b)).
Qed.

Lemma map_form : 
  forall {A B : Type} {f : A -> B} (xs : list A) (b : B), 
    Elem b (map f xs) -> exists (x : A), Elem x xs /\ f x = b.
Proof.
intuition.
induction xs.
inversion H.
simpl in H.
inversion H.
exists a.
intuition.
constructor.
destruct (IHxs prf).
exists x0.
intuition.
constructor.
intuition.
Qed.

Fixpoint powerset {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | []      => [[]]
  | x :: xs => powerset xs ++ map (fun subset => x :: subset) (powerset xs)
  end.

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

Lemma powerset_no_discard :
  forall {A : Type} (x : A) (xs : list A) (ys : list A),
    Elem ys (powerset xs) -> Elem ys (powerset (x :: xs)).
Proof.
intuition.
induction xs.

simpl in H.
inversion H.
simpl.
constructor.
inversion prf.

simpl.
simpl in H.
inversion H.
constructor.

rewrite H2.
apply elem_append_l.
assumption.
Qed.

Lemma powerset_has_empty : 
  forall {A : Type} (xs : list A), Elem [] (powerset xs).
Proof.
intuition.
induction xs.

simpl.
constructor.

apply powerset_no_discard.
assumption.
Qed.

Lemma empty_is_subset :
  forall {A : Type} (xs : list A), IsSubset [] xs.
Proof.
intuition.
unfold IsSubset.
intuition.
unfold Distinct.
intuition.
inversion H.
Qed.

Lemma tail_of_subset_is_subset :
  forall {A : Type} (x : A) (xs : list A) (ys : list A),
    IsSubset (x :: xs) ys -> IsSubset xs ys.
Proof.
intuition.
induction xs.
apply empty_is_subset.
unfold IsSubset.
intuition.
unfold IsSubset in H.
intuition.
unfold Distinct in H0.
unfold Distinct.
intuition.
unfold IsSubset in H.
intuition.
exact (H2 x0 (There x0 x (a :: xs) H0)).
Qed.

Lemma subset_nonempty_supset_nonempty :
  forall {A : Type} (x : A) (xs : list A) (ys : list A),
    IsSubset (x :: xs) ys -> exists (z : A) (zs : list A), ys = z :: zs.
Proof.
intuition.
induction ys.

pose proof subset_of_empty_is_empty (x :: xs) H.
inversion H0.

exists a.
exists ys.
reflexivity.
Qed.

Lemma map_works :
  forall {A B : Type} {f : A -> B} (x : A) (xs : list A),
    Elem x xs -> Elem (f x) (map f xs).
Proof.
intuition.
induction xs.
inversion H.
simpl.
inversion H.
constructor.
constructor.
exact (IHxs prf).
Qed.

Lemma app_elem : 
  forall {A : Type} (l1 l2 : list A) (x : A), Elem x (l1 ++ l2) -> Elem x l1 \/ Elem x l2.
Proof.
intuition.
induction l1.
right.
simpl in H.
assumption.
simpl in H.
inversion H.
left.
constructor.
intuition.
constructor.
constructor.
assumption.
Qed.

Theorem fin_cart_prod_is_fin :
  forall {A B : Set} `{OrdA : Order A, OrdB : Order B}
         (s1 : set A) (s2 : set B) (f1 : finset s1) (f2 : finset s2),
    finset (set_cart_prod s1 s2).
Proof.
intuition.
destruct f1. destruct f2.
intuition.
unfold finset.

