Require Import Coq.Lists.ListSet.
Require Import Coq.Unicode.Utf8_core.

Fixpoint Vec A n : Type :=
  match n with
  | 0 => unit
  | S n => A * Vec A n
  end.

Fixpoint map2 {N A B C} (f: A -> B -> C) (a: Vec A N) (b: Vec B N) :=
  match N as n return Vec A n -> Vec B n -> Vec C n with
    | 0 => λ _ _, tt
    | S N => λ a b, match a, b with
      | (ah, a), (bh, b) => (f ah bh, map2 f a b)
    end
  end a b.

Fixpoint All {N} (xs: Vec Prop N) :=
  match N as n return Vec Prop n -> Prop with
  | 0 => λ _, True
  | S _ => λ xs, match xs with
    | (h, t) => h ∧ All t
    end
  end xs.

Definition Forall2 {N A B} (a: Vec A N) (b: Vec B N) (f: A -> B -> Prop): Prop :=
  All (map2 f a b).

Definition hd {N A} (xs: Vec A (S N)) :=
  match xs with
  | (h, _) => h
  end.

Definition tl {N A} (xs: Vec A (S N)) :=
  match xs with
  | (_, t) => t
  end.

Definition Line {N} := Vec (list nat) N.

Definition Coloring {N} := Vec nat N.

Inductive Permutation {A} : ∀ N, Vec A N → Vec A N → Prop :=
    perm_nil : Permutation 0 tt tt
  | perm_skip : ∀ N x l l', Permutation N l l' → Permutation (S N) (x, l) (x, l')
  | perm_swap : ∀ N (x y : A) (l : Vec A N), Permutation (S (S N)) (y, (x, l)) (x, (y, l))
  | perm_trans : ∀ N l l' l'', Permutation N l l' → Permutation N l' l'' → Permutation N l l''.

Local Hint Constructors Permutation : db.

Lemma Permutation_refl {A} : ∀ n a, @Permutation A n a a.
  induction n; intro; destruct a; auto with db.
Qed.

Lemma Permutation_sym {A} : ∀ n a a', @Permutation A n a a' -> @Permutation A n a' a.
  intros.
  induction H; eauto with db.
Qed.

Local Hint Resolve Permutation_refl Permutation_sym : db.

Definition contains_unpermuted {N} (coloring: @Coloring N) (line: @Line N) : Prop :=
  Forall2 coloring line (@set_In nat).

Definition contains {N} (coloring : @Coloring N) (line : @Line N) :=
  ∃ p, Permutation N coloring p ∧ contains_unpermuted p line.

Notation "a ∈ L" := (contains a L) (at level 70, no associativity).

Lemma contains_permutation' : ∀ N (a a' : @Coloring N) s, Permutation N a a' -> a ∈ s -> a' ∈ s.
  intros.
  destruct H0. destruct H0.
  exists x.
  split; eauto with db.
Qed.

Lemma contains_permutation : ∀ N (a a' : @Coloring N) s, Permutation N a a' -> a ∈ s <-> a' ∈ s.
  split; eauto using contains_permutation', Permutation_sym.
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
