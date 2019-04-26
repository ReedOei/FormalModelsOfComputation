Require Import List Bool FinSets DFA NFA AutomataTactics Strings.

Import ListNotations.

Inductive Regex (A : Type) : Type :=
  | Empty  : Regex A
  | Eps    : Regex A
  | Char   : A -> Regex A
  | Or     : Regex A -> Regex A -> Regex A
  | Concat : Regex A -> Regex A -> Regex A
  | Star   : Regex A -> Regex A.

Arguments Empty {A}.
Arguments Eps {A}.
Arguments Char {A}.
Arguments Or {A}.
Arguments Concat {A}.
Arguments Star {A}.

Fixpoint derive_empty {A : Type} (r : Regex A) : bool :=
  match r with
  | Empty        => false
  | Eps          => true
  | Char _       => false
  | Or r1 r2     => derive_empty r1 || derive_empty r2
  | Concat r1 r2 => derive_empty r1 && derive_empty r2
  | Star _       => true
  end.

Fixpoint derive {A : Type} `{EqA : DecEq A} (r : Regex A) (letter : A) : Regex A :=
  match r with
  | Empty        => Empty
  | Eps          => Empty
  | Char x       => if letter =? x then Eps else Empty
  | Or r1 r2     => Or (derive r1 letter) (derive r2 letter)
  | Concat r1 r2 =>
    if derive_empty r1 then
      Or (Concat (derive r1 letter) r2) r2
    else
      Concat (derive r1 letter) r2
  | Star r       => Concat (derive r letter) (Star r)
  end.

Inductive RegexNFA (A : Type) : Type :=
  | NFA {B : Type} : nfa B A -> RegexNFA A
  | OrNFA     : RegexNFA A -> RegexNFA A -> RegexNFA A
  | ConcatNFA : RegexNFA A -> RegexNFA A -> RegexNFA A
  | StarNFA   : RegexNFA A -> RegexNFA A.

Arguments NFA {A}.
Arguments OrNFA {A}.
Arguments ConcatNFA {A}.
Arguments StarNFA {A}.

Inductive FalseSt := FalseStart.

Definition false_dfa {A : Type} : dfa FalseSt A :=
  Build_dfa FalseSt A (fun st x => FalseStart) FalseStart (fun _ => false).

Theorem false_dfa_correct :
  forall {A : Type} (str : list A), accepted false_dfa str = false.
Proof.
intuition.
Qed.

Inductive TrueSt := TrueStart.

Definition true_dfa {A : Type} : dfa TrueSt A :=
  Build_dfa TrueSt A (fun st x => TrueStart) TrueStart (fun _ => true).

Theorem true_dfa_correct :
  forall {A : Type} (str : list A), accepted true_dfa str = true.
Proof.
intuition.
Qed.

Inductive EmptySt := EmptyStart | NonEmpty.

Definition empty_dfa {A : Type} : dfa EmptySt A :=
  Build_dfa EmptySt A (fun st _ => NonEmpty) EmptyStart 
    (fun st => match st with
               | EmptyStart => true
               | _          => false
               end).

Lemma empty_dfa_nonempty :
  forall {A : Type} (x : A) (str : list A), 
    tStar empty_dfa EmptyStart (x :: str) = NonEmpty.
Proof.
intuition.
induction str.
intuition.
intuition.
Qed.

Theorem empty_dfa_correct :
  forall {A : Type} (str : list A), accepted empty_dfa str = true <-> str = [].
Proof.
intuition.
destruct str.
reflexivity.
intuition.
unfold accepted in H.
rewrite empty_dfa_nonempty in H.
simpl in H.
discriminate.
rewrite H.
intuition.
Qed.

Inductive StringSt {A : Type} (str : list A) : Type :=
  | StrReject : StringSt str
  | StrConcat (suf : list A) : suffix suf str -> StringSt str.

Arguments StrReject {A} {str}.
Arguments StrConcat {A} {str}.

Lemma suf_tail :
  forall {A : Type} {x : A} {suf xs : list A},
    suffix (x :: suf) xs -> suffix suf xs.
Proof.
intuition.
induction suf.
exists xs.
apply app_nil_r.
destruct X.
exists (x0 ++ [x]).
now (rewrite <- app_assoc).
Qed.

Definition string_dfa_trans {A : Type} `{EqA : DecEq A}
  (str : list A) (q : StringSt str) (x : A) :=
  match q with
  | StrReject => StrReject
  | StrConcat [] _ => StrReject
  | StrConcat (y :: ys) prf  => if x =? y then StrConcat ys (suf_tail prf) else StrReject
  end.

Definition string_dfa_f {A : Type} `{EqA : DecEq A} (str : list A)
  (q : StringSt str) : bool :=
  match q with
  | StrConcat [] _ => true
  | _              => false
  end.

Definition string_dfa {A : Type} `{EqA : DecEq A} (str : list A) : dfa (StringSt str) A :=
  Build_dfa (StringSt str) A (string_dfa_trans str)
    (StrConcat str (whole_string_is_suffix str))
    (string_dfa_f str).

Lemma refl_deq :
  forall {A : Type} `{EqA : DecEq A} (x : A), x =? x = true.
Proof.
intuition.
now (induction (deq x x)).
Qed.

Lemma lemma :
  forall {A : Type} `{EqA : DecEq A} (a : A) (str : list A),
    string_dfa_f (tStar (string_dfa str)
       (StrConcat str (whole_string_is_suffix str)) str).
Proof.
intuition.
induction str.
simpl.

Lemma accepts_self {A : Type} `{EqA : DecEq A} (x : A) :
  forall (str : list A),
    accepted (string_dfa str) str = true.
Proof.
induction str.
intuition.

simpl.
intuition.
rewrite (refl_deq a).

simpl in IHstr.

induction str.
simpl.
intuition.
intuition.
simpl in H.
simpl.
unfold string_dfa_f.
induction (x =? x).
intuition.

unfold accepted in H.
simpl in H.
unfold string_dfa_f in H.
induction H.
inversion H.
simpl.

Theorem string_dfa_correct {A : Type} `{EqA : DecEq A} (str : list A) :
  forall (str' : list A), accepted (string_dfa str) str' = true <-> str' = str.
Proof.
induction str'.
induction str.
intuition.
intuition.
inversion H1.
inversion H1.
intuition.
inversion H1.
unfold string_dfa_f in H3.
simpl in H3.

apply rev_ind.
intuition.
quick (destruct str).
quick (destruct str).
intuition.
unfold accepted in H.
rewrite tStar_step in H.
simpl in H.
simpl in H.
simpl in IHstr.
inversion str.
inversion H.

Fixpoint regex_nfa_build {A : Type} (r : Regex A) : RegexNFA A :=
  match r with
  | Empty => NFA FalseSt (dfa_to_nfa false_dfa)
  | Eps => NFA EmptySt (dfa_to_nfa empty_dfa)
  end.

(* states here are nfas
 *)
Definition regex_nfa_trans
  {A : Type} (r : Regex A) (q : RegexNFA A) (x : A) :=
  match r with
  | Empty     => DUD_STATE
  | Eps       => SELF
  | Char x    => MATCH X AND GO FORWARD
  | Or r1 r2  => 
      build the nfa to match r1 and to match r2, then add epsilon transitions to both
  | Concat r1 r2 => 
      build the nfa to match r1, then the nfa to match r2, 
        add epsilon transition into r1 and epsilon transitions from all the final states of r1 to the start state of r2
  

Definition regex_nfa 
  {A : Type} (r : Regex A) : nfa nat A
