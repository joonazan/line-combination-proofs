Require Import Coq.Unicode.Utf8_core.
From mathcomp Require Import all_ssreflect all_fingroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma tnth_zip n S T (a : n.-tuple T) (b : n.-tuple S) i :
  tnth (zip_tuple a b) i = (tnth a i, tnth b i).
  rewrite /tnth -nth_zip; last by rewrite !size_tuple.
  apply: set_nth_default.
  by rewrite size_tuple.
Qed.

Lemma all2Et n T S r (t : n.-tuple T) (s : n.-tuple S) : all2 r t s = all [pred xy | r xy.1 xy.2] (zip t s).
  by rewrite all2E !size_tuple eq_refl.
Qed.

Lemma all2_tnthP n T S (p : T -> S -> bool) (t : n.-tuple T) (s : n.-tuple S) :
  reflect (∀ i, p (tnth t i) (tnth s i)) (all2 p t s).
  rewrite all2Et.
  apply: (iffP all_tnthP);

  move => /= H i; pose proof (H i); move: H0;
  by rewrite tnth_zip.
Qed.

Section Lines.

Variable alphabet_size: nat.
Definition color := 'I_alphabet_size.
Variable one_minus_delta: nat.
Definition Δ := one_minus_delta.+1.

Definition line := Δ.-tuple {set color}.
Definition coloring := Δ.-tuple color.

Definition contains_unpermuted (cl: coloring) (l: line) : bool :=
  all2 (λ c (s : {set color}), c \in s) cl l.

Definition contains (cl : coloring) (line : line) :=
  ∃ p : coloring, perm_eq p cl ∧ contains_unpermuted p line.

Notation "a ∈ L" := (contains a L) (at level 70, no associativity).

Lemma contains_permutation' : ∀ (a a' : coloring) s, perm_eq a a' -> a ∈ s -> a' ∈ s.
  move=> a a' s pe [x [pe2 unper]].
  exists x; split; rewrite //.
  by apply: perm_trans; eassumption.
Qed.

Lemma contains_permutation : ∀ (a a' : coloring) s, perm_eq a a' -> a ∈ s <-> a' ∈ s.
  intros.
  split; apply: contains_permutation'; by [ | rewrite perm_sym].
Qed.

Lemma permutation_contains' : ∀ (a : coloring) (s s' : line), perm_eq s s' -> a ∈ s -> a ∈ s'.
  move=> c s s' pe.
  rewrite /contains/contains_unpermuted. move=> [cs [pe_cs q]].
  move: pe; rewrite perm_sym; move=> /tuple_permP [mapping smap].
  exists [tuple tnth cs (mapping i) | i < Δ].
  split.
    apply: perm_trans; last by apply pe_cs.
    by apply/tuple_permP; exists mapping.
  move: q => /all2_tnthP q.
  rewrite smap; apply/all2_tnthP; move=> i.
  rewrite !tnth_map.
  by apply: q.
Qed.

Lemma permutation_contains a (s s' : line) :
  perm_eq s s' -> a ∈ s <-> a ∈ s'.
  by split; [| rewrite perm_sym in H]; apply: permutation_contains'.
Qed.

Definition combine (a : line) (b : line) : line :=
  [tuple of (thead a) :|: (thead b)
  :: map (λ ab, ab.1 :&: ab.2) (zip (behead a) (behead b))
  ].

Definition combination_of (a b c : line) :=
  ∃ (a' b' : line), perm_eq a' a ∧ perm_eq b' b ∧ combine a' b' = c.

Lemma combination_is_sound_helper : ∀ a b c col,
  combine a b = c -> contains_unpermuted col c -> col ∈ a ∨ col ∈ b.
  case/tupleP => ah a.
  case/tupleP => bh b.
  case/tupleP => ch c.
  case/tupleP => colh col.
  move=> []; rewrite !theadE => ahbhch abc.
  rewrite /contains_unpermuted /= -ahbhch => /andP [].
  case/setUP => colhah colc.

  left.
  exists [tuple of colh :: col]; split. by [].
  rewrite /contains_unpermuted /= colhah /=.
  rewrite -abc in colc.
  rewrite all2E !size_tuple. apply/andP; split. by [].
  apply/all_tnthP; move=> i.
  rewrite tnth_zip /=.
  move: colc => /all2_tnthP H.
  specialize H with i; move: H; rewrite tnth_map tnth_zip /=.
  by move=> /setIP [].

  right.
  exists [tuple of colh :: col]; split. by [].
  rewrite /contains_unpermuted /= colhah /=.
  rewrite -abc in colc.
  rewrite all2E !size_tuple. apply/andP; split. by [].
  apply/all_tnthP; move=> i.
  rewrite tnth_zip /=.
  move: colc => /all2_tnthP H.
  specialize H with i; move: H; rewrite tnth_map tnth_zip /=.
  by move=> /setIP [].
Qed.

Theorem combination_is_sound (a b c : line) col :
  combination_of a b c -> col ∈ c -> col ∈ a ∨ col ∈ b.
  move=> [a' [b'] [pa] [pb] comb] [col' [pcol] cu].
  rewrite -(permutation_contains _ pa) -(permutation_contains _ pb) -!(contains_permutation _ pcol).
  eauto using combination_is_sound_helper.
Qed.

Definition subset (a b : line) := ∀ x, x ∈ a -> x ∈ b.
Notation "a ⊆ b" := (subset a b) (at level 70, no associativity).
Notation "a ⊈ b" := (~~ subset a b) (at level 70, no associativity).

Definition singleton (l : line) := ∃ c : coloring, l = [tuple of map set1 c].

Variable input : seq line.

Definition valid (l : line) :=
  ∀ x, x ∈ l -> ∃ i, x ∈ i ∧ i \in input.

Lemma valid_singleton_in_input a : valid a -> singleton a -> ∃ b : line, b \in input ∧ a ⊆ b.
  move=> v [c prf].
  pose x := v c; move: x => [].
    exists c; split; auto.
    rewrite prf. apply/all2_tnthP. move=> i. rewrite tnth_map.
    by rewrite in_set1.
  move=> x [c_in_x x_in].
  exists x; split; auto.

  move=> c' [c'' [pe up]].
  move: up. rewrite prf /contains_unpermuted => /all2_tnthP ceq.
  suff ee : [forall i, tnth c'' i == tnth c i].
    move: ee; rewrite -eqEtuple => /eqP ee.
    by rewrite -(contains_permutation _ pe) ee.
  apply/forallP; move=> i.
  specialize ceq with i; rewrite tnth_map in ceq.
  by rewrite -in_set1.
Qed.

Lemma split_into_colorings (l : line) :
  valid l -> ∃ l', l ⊆ l' ∧ l' \in input ∨ ∃ a b, combination_of a b l ∧ a ⊂ l ∧ b ⊂ l.

Lemma bigger_is_better a b a' b' : a ⊆ a' -> b ⊆ b' -> ∃ c, combination_of a' b' c ∧ combine a b ⊆ c.
  move=> ab bb.

Inductive iterated_combination : line -> list line -> Prop :=
    present : ∀ a lines, a \in lines -> iterated_combination a lines
  | combined : ∀ (a b c : line) lines, iterated_combination a lines -> iterated_combination b lines -> 
      combination_of a b c -> iterated_combination c lines.

Theorem combination_is_complete (input : list line) :
  ∀ line, valid line input -> ∃ line', iterated_combination line' input ∧ line ⊆ line'.
  move=> line validl.

  (* split into smallest lines, declare impossibility if some coloring is not in input *)
Abort.

Theorem combining_two_suffices {N} (lines : list (@Line (S N))) (missing : @Line (S N)):
(∀ line, set_In line lines -> missing ⊈ line) -> valid missing lines ->
  ∃ a b c, set_In a lines ∧ set_In b lines ∧ IsCombinationOfTwo a b c ∧ ∀ line, set_In line lines -> c ⊈ line.
