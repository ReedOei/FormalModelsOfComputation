Require Import Omega.

Ltac simplify := 
  repeat (
    try intuition;
    try simpl;
    try reflexivity;
    try autorewrite with core;
    try autorewrite with list;
    try autorewrite with omega;
    try autorewrite with strings;
    try autorewrite with sets;
    try autounfold with sets;
    try assumption;
    try trivial;
    try contradiction;
    try congruence;
    try omega
  ).

Ltac autoinduction x := 
  intuition;
  induction x; 
  simplify;
  try (
    match goal with
    | H : _ = _ |- _ => rewrite H
    | H : _ = _ |- _ => rewrite <- H
    end);
  simplify.