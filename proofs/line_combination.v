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
  Forall2 coloring line (λ c l, set_In c l).

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

Theorem combination_is_sound {N} (a : @Line (S N)) (b : @Line (S N)) :
∀ a' b' c, c ∈ combination a' b' -> Permutation (S N) a a' -> Permutation (S N) b b' -> c ∈ a ∨ c ∈ b.
  intros.
  rewrite (permutation_contains _ _ a a'); auto.
  rewrite (permutation_contains _ _ b b'); auto.

  destruct H, H.
  destruct x, a', b', H2.
  apply set_union_elim in H2; destruct H2; [left | right];

  exists (n, v);
  split; auto; split; auto;
  induction N; auto;
  destruct v1, v, v0, H3;
  split;
  eauto using set_inter_elim1, set_inter_elim2, Permutation_refl.
Qed.
