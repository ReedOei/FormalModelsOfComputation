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

Structure dfa (A B : Type) (Sigma : list B) `{EqA : DecEq A, EqB : DecEq B} := {
  Q : list A;

  t : Member Q -> Member Sigma -> Member Q;
  s : Member Q;

  F : Subset Q
}.

Arguments Q {A} {B} {Sigma} {EqA} {EqB}.
Arguments t {A} {B} {Sigma} {EqA} {EqB}.
Arguments s {A} {B} {Sigma} {EqA} {EqB}.
Arguments F {A} {B} {Sigma} {EqA} {EqB}.

Fixpoint tStar {A B : Type} `{EqA : DecEq A, EqB : DecEq B} 
               {SigmaM : list B}
               (M : dfa A B SigmaM) (q : Member (Q M)) (str : list (Member SigmaM)) : Member (Q M) :=
  match str with
  | []      => q
  | x :: xs => tStar M (t M q x) xs
  end.

Definition accepted {A B : Type} `{EqA : DecEq A, EqB : DecEq B}
                    {SigmaM : list B}
                    (M : dfa A B SigmaM) (str : list (Member SigmaM)) : bool :=
  match tStar M (s M) str, F M with
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

Definition make_pair 
  {A B : Type} {l1 : list A} {l2 : list B} (a : Member l1) (b : Member l2) : A * B :=
  match a, b with
  | exist _ a' _, exist _ b' _ => (a', b')
  end.

Lemma make_pair_is_member :
  forall {A B : Type} {l1 : list A} {l2 : list B} (a : Member l1) (b : Member l2),
    Elem (make_pair a b) (cart_prod l1 l2).
Proof.
intuition.
pose proof pair_member a b.
destruct a. destruct b.
unfold make_pair.
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

Definition and_dfa_trans {A B C : Type} `{EqA : DecEq A, EqB : DecEq B, EqC : DecEq C}
                    {Sigma : list B}
                    (M : dfa A B Sigma) (N : dfa C B Sigma)
                    (q : Member (cart_prod (Q M) (Q N))) 
                    (s : Member Sigma) : Member (cart_prod (Q M) (Q N)) :=
  match q with
  | exist _ (qm,qn) prf' => 
    let m := member_cart_prod (qm,qn) prf' in
    let newQM := t M (exist _ qm (proj1 m)) s in
    let newQN := t N (exist _ qn (proj2 m)) s in
      exist _ (make_pair newQM newQN) (make_pair_is_member newQM newQN)
  end.

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
exact (pair_member (exist _ a (i a H0)) (exist _ b (i0 b H1))).
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

Definition and_dfa {A B C : Type} `{EqA : DecEq A, EqB : DecEq B, EqC : DecEq C}
                   {Sigma : list B}
                   (M : dfa A B Sigma) (N : dfa C B Sigma) : dfa (A * C) B Sigma :=
  match s M, s N with
  | exist _ sm _, exist _ sn _ =>
      let newQ := cart_prod (Q M) (Q N) in
      Build_dfa (A * C) B Sigma (dec_eq_prod A C EqA EqC) EqB
                newQ (and_dfa_trans M N)
                (exist _ (make_pair (s M) (s N)) (make_pair_is_member (s M) (s N)))
                (exist _ (cart_prod_subset (F M) (F N)) (make_subset_prod (F M) (F N)))
  end.

Lemma and_dfa_start_same
  {A B C : Type} `{EqA : DecEq A, EqB : DecEq B, EqC : DecEq C}
  {Sigma : list B}
  (M : dfa A B Sigma) (N : dfa C B Sigma) :
    match s M, s (and_dfa M N) with
    | exist _ qm _, exist _ (qm',_) _ => qm = qm'
    end.
Proof.
intuition.
unfold and_dfa.
destruct (s M). destruct (s N).
simpl.
reflexivity.
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

Lemma app_induction_rev :
  forall {A : Type} {P : list A-> Prop},
    P [] ->
    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list A, P (rev l).
Proof.
intros.
induction l.
intuition.
exact (H0 a l IHl).
Qed.

Theorem app_induction :
  forall {A : Type} {P : list A -> Prop}, 
    P [] ->
    (forall (x : A) (xs : list A), P xs -> P (xs ++ [x])) ->
    forall (xs : list A), P xs.
Proof.
intuition.

pose proof rev_involutive xs.
rewrite <- H1.
apply app_induction_rev.

assumption.

intros.
simpl.
exact (H0 a (rev l) H2).
Qed.

Definition tStar_step_prop 
   {A B : Type} `{EqA : DecEq A, EqB : DecEq B}
   {Sigma : list B}
   (M : dfa A B Sigma)
   (str : list (Member Sigma)) : Prop :=
    forall (q : Member (Q M)) (x : Member Sigma), 
      tStar M q (str ++ [x]) = t M (tStar M q str) x.

Lemma tStar_step :
  forall {A B : Type} `{EqA : DecEq A, EqB : DecEq B}
   {Sigma : list B}
   (M : dfa A B Sigma)
   (str : list (Member Sigma)), tStar_step_prop M str.
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

Theorem and_dfa_mirror :
  forall {A B C : Type} `{EqA : DecEq A, EqB : DecEq B, EqC : DecEq C}
   {Sigma : list B}
   (M : dfa A B Sigma) (N : dfa C B Sigma)
   (str : list (Member Sigma)),
    proj1_sig (tStar M (s M) str) = fst (proj1_sig (tStar (and_dfa M N) (s (and_dfa M N)) str)).
Proof.
intros.

revert str.
apply app_induction.

simpl.
unfold proj1_sig, fst, and_dfa.
destruct (s M).
destruct (s N).
simpl.
reflexivity.

intros.

rewrite tStar_step.
rewrite tStar_step.
unfold proj1_sig, fst.
unfold proj1_sig, fst in H.
destruct (tStar M (s M) xs).
destruct (tStar (and_dfa M N) (s (and_dfa M N)) xs).
destruct x1.

unfold and_dfa.
destruct (s M). destruct (s N).
simpl.
unfold and_dfa_trans.
destruct (tStar M (exist (fun x : A => Elem x (Q M)) x0 e) xs).
destruct (tStar (and_dfa M N) (s (and_dfa M N)) xs).
destruct x3.
destruct (t M (exist (fun x3 : A => Elem x3 (Q M)) x2 e1) x).
simpl.

Theorem and_dfa_correct :
  forall {A B C : Type} `{EqA : DecEq A, EqB : DecEq B, EqC : DecEq C}
         (M : dfa A B) (N : dfa C B) 
         (prf : Sigma M = Sigma N) (str : list (Member (Sigma M))),
          accepted (and_dfa M N prf) (alphabet_same str (and_dfa_alphabet_same M N prf)) 
          = true -> accepted M str && accepted N (alphabet_same str prf) = true.
Proof.
intuition.
induction str.

rewrite alphabet_same_empty in H.
rewrite alphabet_same_empty.

unfold accepted.
simpl.
destruct (s M).
destruct (s N).
simpl.
rewrite alphabet_same_empty.
destruct (F M). destruct (F N).
simpl.
rewrite alphabet_same_empty in H.
unfold accepted in H.
simpl in H.
destruct (s (and_dfa M N prf)). destruct (F (and_dfa M N prf)).
apply andb_true_iff.
destruct x3.
induction (elem (a,c) x4).
