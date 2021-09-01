Require Import Coq.Unicode.Utf8_core.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Line n := n.-tuple (list nat).
Definition Coloring n := n.-tuple nat.

Definition contains_unpermuted {N} (coloring: Coloring N) (line: Line N) :=
  all (λ x, x.1 \in x.2) (zip coloring line).

Definition contains {N} (coloring : Coloring N) (line : Line N) :=
  ∃ (p : Coloring N), perm_eq p coloring ∧ contains_unpermuted p line.

Notation "a ∈ L" := (contains a L) (at level 70, no associativity).

Lemma contains_permutation' : ∀ N (a a' : Coloring N) s, perm_eq a a' -> a ∈ s -> a' ∈ s.
  move=> n a a' s pe [x [pe2 unper]].
  exists x; split; rewrite //.
  by apply: perm_trans; eassumption.
Qed.

Lemma contains_permutation : ∀ N (a a' : Coloring N) s, perm_eq a a' -> a ∈ s <-> a' ∈ s.
  intros.
  split; apply: contains_permutation'; by [ | rewrite perm_sym].
Qed.

Lemma permutation_contains' : ∀ N (a : @Coloring N) s s', Permutation N s s' -> a ∈ s -> a ∈ s'.
  intros.
  induction H; eauto.

  destruct H0, H0.
  destruct x0.
  destruct H1.
  destruct (IHPermutation v). exists v. eauto with db.
  destruct H3.
  exists (n, x0). split.
  eauto with db.
  split; eauto.

  destruct H0, H, x0, v.
  exists (n0, (n, v)).
  split. eauto with db.
  destruct H0, H1.
  repeat (try assumption; split).
Qed.

Lemma permutation_contains : ∀ N (a : @Coloring N) s s', Permutation N s s' -> a ∈ s <-> a ∈ s'.
  split; eauto using permutation_contains', Permutation_sym.
Qed.

Definition nat_eq_dec: forall a b : nat, {a = b} + {a <> b}.
  decide equality.
Defined.

Definition combination {N} (a : @Line (S N)) (b : @Line (S N)) : @Line (S N) :=
  ( set_union nat_eq_dec (hd a) (hd b)
  , map2 (set_inter nat_eq_dec) (tl a) (tl b)
  ).

Definition IsCombinationOfTwo {N} (a b c : @Line (S N)) := ∃ a' b', Permutation (S N) a' a ∧ Permutation (S N) b' b ∧ combination a' b' = c.

Lemma combination_is_sound_helper1 {N} : ∀ (a b : @Line N) x, All (map2 (set_In (A:=nat)) x (map2 (set_inter nat_eq_dec) a b)) ->
  All (map2 (set_In (A:=nat)) x a).
  induction N; auto.
  intros.
  destruct x, a, b, H.
  split; eauto using set_inter_elim1.
Qed.

Lemma combination_is_sound_helper2 {N} : ∀ (a b : @Line N) x, All (map2 (set_In (A:=nat)) x (map2 (set_inter nat_eq_dec) a b)) ->
  All (map2 (set_In (A:=nat)) x b).
  induction N; auto.
  intros.
  destruct x, a, b, H.
  split; eauto using set_inter_elim2.
Qed.

Theorem combination_is_sound {N} (a : @Line (S N)) (b : @Line (S N)) :
∀ c col, IsCombinationOfTwo a b c -> col ∈ c -> col ∈ a ∨ col ∈ b.
  intros.
  destruct H, H, H, H1.
  rewrite (permutation_contains _ _ a x); auto with db.
  rewrite (permutation_contains _ _ b x0); auto with db.

  destruct col, x, x0.
  rewrite <- H2 in H0.
  destruct H0, H0, x.
  destruct H3.
  apply set_union_elim in H3; destruct H3; [left | right];

  exists (n0, v2);
  split; auto with db; split; auto;
  eauto using combination_is_sound_helper1, combination_is_sound_helper2.
Qed.

(** Show that every maximal line is reachable via combinations *)

Fixpoint weight {N} (line : @Line N) : nat :=
  match N as n return Vec (list nat) n -> nat with
  | 0 => λ _, 0
  | S n => λ xs, match xs with
    | (h, t) => length h + weight t
    end
  end line.

Lemma split_into_colorings {N} (line: @Line (S N)):
weight line > (S N) -> ∃ a b, combination a b = line ∧ weight a < weight line ∧ weight b < weight line.
  intros.
Abort.

Definition subset {N} (a b : @Line N) := ∀ x, x ∈ a -> x ∈ b.
Notation "a ⊆ b" := (subset a b) (at level 70, no associativity).
Notation "a ⊈ b" := (~ subset a b) (at level 70, no associativity).

Definition valid {N} (line : @Line N) (input: list (@Line N)) :=
  ∀ x, x ∈ line -> ∃ i, set_In i input ∧ x ∈ i.

Inductive IsCombinationOf {N} : @Line (S N) -> list (@Line (S N)) -> Prop :=
    present : ∀ a lines, set_In a lines -> IsCombinationOf a lines
  | combined : ∀ (a b c : @Line (S N)) lines, IsCombinationOf a lines -> IsCombinationOf b lines -> 
      IsCombinationOfTwo a b c -> IsCombinationOf c lines.

Theorem combination_is_complete {N} (input : list (@Line (S N))) : ∀ line, valid line input -> IsCombinationOf line input.
  intros.
  (* split into smallest lines, declare impossibility if some coloring is not in input *)
Abort.

Theorem combining_two_suffices {N} (lines : list (@Line (S N))) (missing : @Line (S N)):
(∀ line, set_In line lines -> missing ⊈ line) -> valid missing lines ->
  ∃ a b c, set_In a lines ∧ set_In b lines ∧ IsCombinationOfTwo a b c ∧ ∀ line, set_In line lines -> c ⊈ line.
