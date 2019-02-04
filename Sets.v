Require Import List PeanoNat Omega Bool.

Import ListNotations.

Parameter A : Set.

Definition set (A : Set) := A -> bool.

Fixpoint contains {A : Set} {eq : A -> A -> bool} (v : list A) (e : A) : bool :=
  match v with
  | [] => false
  | x :: xs => if eq e x then true else @contains A eq xs e
  end.

Arguments contains {A} {eq} _ _.

Definition element (l : list nat) := {x : nat | @contains nat beq_nat l x = true}.
Definition subset (l : list nat) := element l -> bool.

Definition set_eq (A : Set) (x y : set A) : Prop := forall (e : A), x e = y e.

Definition cart_prod (A B : Set) (a : set A) (b : set B) : set (A * B) := 
  fun p => 
    match p with
    | pair x y => (a x) && (b y)
    end.

Arguments cart_prod {A} {B} _ _.
