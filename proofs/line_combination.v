Require Import Coq.Unicode.Utf8_core Lia.
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

Definition contains (cl : coloring) (line : line) : bool :=
  [exists (p : coloring | perm_eq p cl), contains_unpermuted p line].

Notation "a ∈ L" := (contains a L) (at level 50, no associativity).

Lemma contains_permutation' : ∀ (a a' : coloring) s, perm_eq a a' -> a ∈ s -> a' ∈ s.
  move=> a a' s pe /existsP[x] /andP[pe2 unper].
  apply/existsP; exists x; apply/andP; split; rewrite //.
  by apply: perm_trans; eassumption.
Qed.

Lemma contains_permutation : ∀ (a a' : coloring) s, perm_eq a a' -> a ∈ s <-> a' ∈ s.
  intros.
  split; apply: contains_permutation'; by [ | rewrite perm_sym].
Qed.

Lemma permutation_contains' : ∀ (a : coloring) (s s' : line), perm_eq s s' -> a ∈ s -> a ∈ s'.
  move=> c s s' pe.
  rewrite /contains/contains_unpermuted.
  move=> /existsP[cs /andP[pe_cs q]].
  move: pe; rewrite perm_sym; move=> /tuple_permP [mapping smap].
  apply/existsP; exists [tuple tnth cs (mapping i) | i < Δ].
  apply/andP; split.
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

Definition combine n (T := n.+1.-tuple {set color}) (a : T) (b : T) : T :=
  [tuple of (thead a) :|: (thead b)
  :: map (λ ab, ab.1 :&: ab.2) (zip (behead a) (behead b))
  ].

Definition combination_of (a b c : line) :=
  ∃ (a' b' c' : line), perm_eq a' a ∧ perm_eq b' b ∧ perm_eq c' c ∧ combine a' b' = c'.

Lemma combination_is_sound_helper : ∀ a b c col,
  combine a b = c -> contains_unpermuted col c -> col ∈ a ∨ col ∈ b.
  case/tupleP => ah a.
  case/tupleP => bh b.
  case/tupleP => ch c.
  case/tupleP => colh col.
  move=> []; rewrite !theadE => ahbhch abc.
  rewrite /contains_unpermuted /= -ahbhch => /andP [].
  case/setUP => colhah colc; [left | right].

  apply/existsP; exists [tuple of colh :: col]. apply/andP; split. by [].
  rewrite /contains_unpermuted /= colhah /=.
  rewrite -abc in colc.
  rewrite all2E !size_tuple. apply/andP; split. by [].
  apply/all_tnthP; move=> i.
  rewrite tnth_zip /=.
  move: colc => /all2_tnthP H.
  specialize H with i; move: H; rewrite tnth_map tnth_zip /=.
  by move=> /setIP [].

  apply/existsP; exists [tuple of colh :: col]. apply/andP; split. by [].
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
  move=> [a' [b'] [c'] [pa] [pb] [pc] comb].
  rewrite -(permutation_contains _ pc) => /exists_inP[col' pcol] cu.
  rewrite -(permutation_contains _ pa) -(permutation_contains _ pb) -!(contains_permutation _ pcol).
  eauto using combination_is_sound_helper.
Qed.

Definition subset a b := [forall (x | x ∈ a), x ∈ b].
Notation "a ⊆ b" := (subset a b) (at level 50, no associativity).
Notation "a ⊈ b" := (~~ subset a b) (at level 50, no associativity).
Definition strict_subset a b := (a ⊆ b) && (b ⊈ a).
Notation "a ⊂ b" := (strict_subset a b) (at level 50, no associativity).

Lemma matching_subset (a b : line) :
  (exists a' b' : line, perm_eq a a' ∧ perm_eq b b' ∧ all2 (λ x y : {set color}, x \subset y) a' b') -> a ⊆ b.
Proof.
  move=> [a'] [b'] [ap] [bp] /all2_tnthP sub.
  apply/forall_inP => x.
  rewrite (permutation_contains _ ap) (permutation_contains _ bp).
  move=> /exists_inP[x' px cu].
  apply/exists_inP. exists x'; auto.
  apply/all2_tnthP => i; specialize sub with i.
  move: cu => /all2_tnthP cu; specialize cu with i.
  move: sub => /subsetP sub.
  by apply: sub.
Qed.

Definition singleton (l : line) := ∃ c : coloring, l = [tuple of map set1 c].

Variable input : seq line.
Variable input_nonempty : input <> [::].

Definition valid (l : line) :=
  ∀ x, x ∈ l -> ∃ i, x ∈ i ∧ i \in input.

Definition represented (a : line) := ∃ b : line, b \in input ∧ a ⊆ b.

Lemma valid_singleton_represented a : valid a -> singleton a -> represented a.
  move=> v [c prf].
  pose x := v c; move: x => [].
    apply/existsP; exists c; apply/andP; split; auto.
    rewrite prf. apply/all2_tnthP. move=> i. rewrite tnth_map.
    by rewrite in_set1.
  move=> x [c_in_x x_in].
  exists x; split; auto.

  apply/forallP; move=> c'; apply/implyP; move=> /existsP[c'' /andP[pe up]].
  move: up. rewrite prf /contains_unpermuted => /all2_tnthP ceq.
  suff ee : [forall i, tnth c'' i == tnth c i].
    move: ee; rewrite -eqEtuple => /eqP ee.
    by rewrite -(contains_permutation _ pe) ee.
  apply/forallP; move=> i.
  specialize ceq with i; rewrite tnth_map in ceq.
  by rewrite -in_set1.
Qed.

Definition weight (l : line) := sumn (map_tuple (λ x : {set color}, #|x|) l).

Lemma subset_weight a b : a ⊆ b -> weight a <= weight b.
Abort.

Lemma broken_line_represented l : weight l < Δ -> represented l.
  move => w.
  suff broken : [forall x, ~~ (x ∈ l)].
    rewrite /represented.
    case E : input => [| input1 {}].
      by [].
    exists input1; split. by apply: mem_head.
    move: broken => /forallP broken.
    apply/forallP; move=> x.
    apply/implyP.
    move => t.
    pose br := broken x; move: br.
    by rewrite t.
  apply/forallP => x.
  rewrite negb_exists; apply/forallP => x'; rewrite negb_and.
  apply/orP; right.
Abort.

Lemma val_tcast {T} m n (tc : n = m) (x : n.-tuple T) :
  val (tcast tc x) = val x.
Proof. by case: m / tc. Qed.

Lemma thead_tcast {T} m n (sz : n.+1 = m.+1) (x : n.+1.-tuple T) : thead (tcast sz x) = thead x.
  rewrite /thead tcastE.
  by apply/tnth_nth.
Qed.

Lemma combine_tcast m n (sz : n.+1 = m.+1) a b : combine (tcast sz a) (tcast sz b) = tcast sz (combine a b).
  apply: val_inj; rewrite val_tcast /= !thead_tcast.
  apply eq_from_nth with (x0 := thead a).
    by rewrite !size_tuple sz.
  by case: m.+1 / sz.
Qed.

Lemma perm_eq_tcast {T : eqType} m n (sz : n = m) (x : n.-tuple T) (y : seq T) :
  perm_eq (tcast sz x) y = perm_eq x y.
Proof. by case: m / sz. Qed.

Lemma head_rot T n (l : n.+1.-tuple T) (i : 'I_n.+1) x : head x (rot i l) = tnth l i.
  case E : (i < size l).
    by rewrite /rot (drop_nth x) //= (tnth_nth x).
  by rewrite size_tuple ltn_ord in E.
Qed.

Lemma split_into_colorings (l : line) :
  valid l -> (∃ i : 'I_Δ, #|tnth l i| > 1) -> ∃ a b, combination_of a b l ∧ a ⊂ l ∧ b ⊂ l.
  move=> v [i ith_big].
  case E : (enum (tnth l i)) => [|ai rest].
    by rewrite cardE E in ith_big.
  case E2 : rest => [| bi resti].
    by rewrite cardE E E2 in ith_big.

  pose big := tnth l i.
  pose without_big := [tuple of behead (rot i l)].
  pose a := [tuple of big :\ bi :: without_big].
  pose b := [tuple of big :\ ai :: without_big].
  have sz : Δ.-1.+1 = Δ. by [].

  exists (tcast sz a), (tcast sz b).
  split.
    exists (tcast sz a), (tcast sz b), (tcast sz [tuple of big :: without_big]).
      repeat split; auto.
    rewrite perm_eq_tcast perm_sym.
    apply/perm_consP; exists i, without_big; split; auto.
    rewrite /without_big /=.
    case rsplit : (rot i l).
      have x : size (rot i l) = Δ. by rewrite size_tuple.
      by rewrite rsplit in x.
    by rewrite /= /big -(head_rot l i set0) rsplit.

    apply: val_inj.
    rewrite combine_tcast !val_tcast /=.
    rewrite /a /b !theadE /=.
    rewrite -setDIr.
    suff no_overlap : [set bi] :&: [set ai] = set0.
    rewrite no_overlap setD0.
    suff x : [seq ab.1 :&: ab.2 | ab <- zip (behead (rot i l)) (behead (rot i l))] = behead (rot i l).
      by rewrite x.
    set x := behead (rot i l).
    apply eq_from_nth with (x0 := set0).
      by rewrite !size_tuple.
    rewrite size_tuple => j js.
    rewrite (nth_map (set0, set0));
    by [rewrite nth_zip //= setIid | rewrite size_tuple].
    rewrite /setI.
    give_up.

    split.


  split; apply/andP; split; last first.
  rewrite negb_forall_in.

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
