Require Import Coq.Unicode.Utf8_core.
From mathcomp Require Import all_ssreflect all_fingroup.
Require Import utils.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Lines.

Variable alphabet_size: nat.
Definition color := 'I_alphabet_size.
Variable one_minus_delta: nat.
Definition Δ := one_minus_delta.+1.

Definition nline n := n.-tuple {set color}.
Notation "n .-line" := (nline n) (at level 30, no associativity).
Definition line := Δ.-line.
Definition coloring := Δ.-tuple color.

Definition contains_unpermuted (cl: coloring) (l: line) : bool :=
  all2 (λ c (s : {set color}), c \in s) cl l.

Definition contains (cl : coloring) (line : line) : bool :=
  [exists (p : coloring | perm_eq p cl), contains_unpermuted p line].

Notation "a ∈ L" := (contains a L) (at level 50, no associativity).

Lemma contains_permutation' : ∀ (a a' : coloring) s, perm_eq a a' -> a ∈ s -> a' ∈ s.
  move=> a a' s pe /existsP[x] /andP[pe2 unper].
  fill_ex x; apply/andP; split; rewrite //.
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
  fill_ex [tuple tnth cs (mapping i) | i < Δ].
  apply/andP; split.
    apply: perm_trans; last by apply: pe_cs.
    by apply: any_perm.
  move: q => /all2_tnthP q.
  rewrite smap; apply/all2_tnthP; move=> i.
  rewrite !tnth_map.
  by apply: q.
Qed.

Lemma permutation_contains a (s s' : line) :
  perm_eq s s' -> a ∈ s <-> a ∈ s'.
  by split; [| rewrite perm_sym in H]; apply: permutation_contains'.
Qed.

Definition combine m (n := m.+1) (a : n.-line) (b : n.-line) : n.-line :=
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
  rewrite /contains_unpermuted /= -ahbhch => /andP[].
  rewrite -abc.
  case/setUP => colhah /all2_tnthP colc; [left | right];

  fill_ex [tuple of colh :: col]; split_and;
  apply/all2_tnthP => i; move: (colc i);
  by rewrite !tnth_simpl /= => /setIP[].
Qed.

Theorem combination_is_sound (a b c : line) col :
  combination_of a b c -> col ∈ c -> col ∈ a ∨ col ∈ b.
  move=> [a' [b'] [c'] [pa] [pb] [pc] comb].
  rewrite -(permutation_contains _ pc) => /exists_inP[col' pcol] cu.
  rewrite -(permutation_contains _ pa) -(permutation_contains _ pb) -!(contains_permutation _ pcol).
  eauto using combination_is_sound_helper.
Qed.

Definition subset {n} (a b : n.-line) :=
  [exists a' : n.-line, exists b' : n.-line, perm_eq a a' && perm_eq b b' && all2 (λ x y : {set color}, x \subset y) a' b'].
Notation "a ⊆ b" := (subset a b) (at level 50, no associativity).
Notation "a ⊈ b" := (~~ subset a b) (at level 50, no associativity).
Definition strict_subset {n} (a b : n.-line) := (a ⊆ b) && (b ⊈ a).
Notation "a ⊂ b" := (strict_subset a b) (at level 50, no associativity).

Lemma subset_refl {n} (a : n.-line) : a ⊆ a.
  fill_ex a.
  fill_ex a.
  split_and.
  by apply/all2_tnthP.
Qed.

Lemma subset_trans {n} (a b c : n.-line) : a ⊆ b -> b ⊆ c -> a ⊆ c.
  move=> /existsP[a'] /existsP[b'] /andP[/andP[pa pb] /all2_tnthP ss].
  move=> /existsP[b''] /existsP[c''] /andP[/andP[pb2 pc] /all2_tnthP ss2].
  have /tuple_permP[p pp] : perm_eq b' b''.
    by apply: perm_trans; [rewrite perm_sym; apply pb|].
  fill_ex a'.
  fill_ex [tuple tnth c'' (p i) | i < n].
  split_and.
    move: pc; rewrite perm_sym; move=> /tuple_permP[p2 pp2].
    rewrite (val_inj pp2) mktuple_mktuple perm_sym.
    have ll : (λ i, tnth c (p2 (p i))) =1 λ i, tnth c ((p * p2)%g i).
      by move=> i; rewrite permM.
    by rewrite (eq_mktuple _ ll); apply: any_perm.
  apply/all2_tnthP => i; rewrite tnth_mktuple.
  apply: subset_trans; last apply: ss2.
  move: pp => /val_inj/eqP. rewrite eqEtuple => /forallP.
  by move/(_ i); rewrite tnth_mktuple => /eqP x; rewrite -x.
Qed.

Lemma matching_subset (a b : line) :
  a ⊆ b -> [forall (x | x ∈ a), x ∈ b].
Proof.
  move=> /existsP[a'] /existsP[b'] /andP[/andP[ap bp]] /all2_tnthP sub.
  apply/forall_inP => x.
  rewrite (permutation_contains _ ap) (permutation_contains _ bp).
  move=> /exists_inP[x' px cu].
  fill_ex x'; split_and.
  apply/all2_tnthP => i; move: (sub i) => /subsetP sub'.
  apply: sub'.
  by move: cu => /all2_tnthP.
Qed.

Lemma subset_perm (a b b' : line) : perm_eq b b' -> a ⊆ b -> a ⊆ b'.
  move=> pe /existsP[a' /existsP[b'' /andP[/andP[aa bb] ss]]].
  fill_ex a'; fill_ex b''; split_and.
  by apply: perm_trans; [rewrite perm_sym; eassumption |].
Qed.

Lemma subset_perm2 (a a' b : line) : perm_eq a a' -> a ⊆ b -> a' ⊆ b.
  move=> pe /existsP[a'' /existsP[b' /andP[/andP[aa bb] ss]]].
  fill_ex a''; fill_ex b'; split_and.
  by apply: perm_trans; [rewrite perm_sym; eassumption |].
Qed.

Lemma strict_subset_perm (a b b' : line) : perm_eq b b' -> a ⊂ b -> a ⊂ b'.
  move=> pe /andP[t f].
  split_and.
    by apply: (subset_perm pe).
  rewrite perm_sym in pe.
  case E : (b' ⊆ a) => //.
  inversion f; apply/negPn.
  by apply: (subset_perm2 pe).
Qed.

Variable input : seq line.
Variable input_nonempty : input <> [::].

Definition valid (l : line) :=
  forall x, x ∈ l -> [exists i in input, x ∈ i].

Lemma subset_valid (a b : line) : a ⊆ b -> valid b -> valid a.
  move=> /matching_subset/forall_inP ss vb x x_in_a.
  by apply: vb; apply: ss.
Qed.

Definition weight (l : seq {set color}) := \sum_(i <- l) #|i|.

Lemma sum_map {T} f (a : seq T) : \sum_(i <- a) f i = \sum_(i <- map f a) i.
  elim: a.
    by rewrite -foldrE big_nil.
  move=> a l IH.
  by rewrite /= !big_cons IH.
Qed.

Lemma perm_weight {n} (a a' : n.-line) : perm_eq a a' -> weight a = weight a'.
  move=> pe; rewrite /weight [in RHS]sum_map sum_map -!sumnE.
  by apply: perm_sumn; apply: perm_map.
Qed.

Lemma subset_weight {n} (a b : n.-line) : a ⊆ b -> weight a <= weight b.
  move=> /existsP[a'] /existsP[b'] /andP[/andP[pa pb] /all2_tnthP ss].
  rewrite (perm_weight pa) (perm_weight pb).
  rewrite /weight !big_tuple.
  apply: leq_sum => i _.
  by apply: subset_leq_card.
Qed.

Lemma strict_subset_weight_math a1 a2 b1 b2 c1 c2 :
  a1 <= a2 -> b1 < b2 -> c1 <= c2 -> a1 + (b1 + c1) < a2 + (b2 + c2).
Proof. by sslia. Qed.

Lemma strict_subset_weight (a b : line) : a ⊂ b -> weight a < weight b.
  move=> /andP[] /existsP[a'] /existsP[b'] /andP[/andP[pa pb] /all2_tnthP ss].
  rewrite /subset negb_exists => /forallP; move/(_ b').
  rewrite /subset negb_exists => /forallP; move/(_ a').
  rewrite pa pb /= => /all2_tnthP /forallP/forallPn[badi nss].
  rewrite (perm_weight pa) (perm_weight pb) /weight.

  have separate_bad : ∀ t : line, val t = take badi t ++ tnth t badi :: drop badi.+1 t.
    by intro; rewrite -drop_nth ?size_tuple // cat_take_drop.
  rewrite (separate_bad a') (separate_bad b') !big_cat !big_cons /=.
  apply: strict_subset_weight_math;
    [| by rewrite (ltn_leqif (subset_leqif_card (ss badi))) |];
    apply: subset_weight.

  apply/existsP; exists (take_tuple badi a').
  apply/existsP; exists (take_tuple badi b').
  split_and.
  apply/all2_tnthP => i. rewrite !(tnth_nth set0) !nth_take;
    try (move: (ltn_ord i) (geq_minl badi Δ); sslia).
  move: ss. setoid_rewrite (tnth_nth set0). move/(_ (widen_ord _ i)) => x. apply: x.
  apply: geq_minr.

  apply/existsP; exists (drop_tuple badi.+1 a').
  apply/existsP; exists (drop_tuple badi.+1 b').
  split_and.
  apply/all2_tnthP => i. rewrite !(tnth_nth set0) !nth_drop.
  case E : (badi.+1 + i < Δ).
    move: ss. setoid_rewrite (tnth_nth set0).  move/(_ (inord (badi.+1 + i))). by rewrite inordK.
  by rewrite !nth_default // size_tuple leqNgt E.
Qed.

Definition nonzero := all (λ x : {set color}, #|x| != 0).

Lemma nonzero_rot x i : nonzero x -> nonzero (rot i x).
  move=> v.
  by rewrite /nonzero (@perm_all _  _ x) // perm_rot.
Qed.

Lemma nonzero_behead x : nonzero x -> nonzero (behead x).
Proof. case x. done. by move=> s ll /= /andP[]. Qed.

Lemma size_contradiction a b : a < b -> a >= b -> false.
  by sslia.
Qed.

Lemma head_rot T n (l : n.+1.-tuple T) (i : 'I_n.+1) x : head x (rot i l) = tnth l i.
  case E : (i < size l).
    by rewrite /rot (drop_nth x) //= (tnth_nth x).
  by rewrite size_tuple ltn_ord in E.
Qed.

Lemma split_into_colorings (l : line) :
  valid l -> nonzero l -> (∃ i : 'I_Δ, #|tnth l i| > 1) ->
  ∃ a b, combination_of a b l ∧
  a ⊂ l ∧ b ⊂ l ∧
  nonzero a ∧ nonzero b.
Proof.
  move=> v nz [i ith_big].
  case E : (enum (tnth l i)) => [|ai rest].
    by rewrite cardE E in ith_big.
  case E2 : rest => [| bi resti].
    by rewrite cardE E E2 in ith_big.
  rewrite E2 {E2 rest} in E.

  pose big := tnth l i.
  pose without_big := [tuple of behead (rot i l)].
  pose a := [tuple of big :\ bi :: without_big].
  pose b := [tuple of big :\ ai :: without_big].
  pose l' := [tuple of big :: without_big].

  have lp : perm_eq l' l.
    rewrite perm_sym.
    apply/perm_consP; exists i, without_big; split; auto.
    rewrite /without_big /=.
    case rsplit : (rot i l).
      have x : size (rot i l) = Δ. by rewrite size_tuple.
      by rewrite rsplit in x.
    by rewrite /= /big -(head_rot l i set0) rsplit.

  exists a, b.
  split.
    exists a, b, l'.
      repeat split; auto.

    rewrite /combine !theadE.
    rewrite -setDIr.
    suff no_overlap : [set bi] :&: [set ai] = set0.
      rewrite no_overlap setD0.
      apply: tuple_f_equal => //.
      apply/eqP; rewrite eqEtuple; apply/forallP => j.
      by rewrite !tnth_simpl setIid.
    apply/setP/eqfunP/forallP => x.
    rewrite in_set0 in_setI !in_set1.
    suff ne: bi != ai.
      case X: (x == bi) => //. by move: X => /eqP X; rewrite X eqbF_neg.
    have unik := enum_uniq (tnth l i); move: unik.
    rewrite E /= => /andP[] /memPn bi_not_ai _.
    by apply: bi_not_ai; rewrite inE; apply/orP; left.

    have proper x (xl := [tuple of big :\ x :: without_big]) : x \in big -> xl ⊂ l'.
      move=> x_in_big.
      split_and.
        apply/existsP; exists xl; apply/existsP; exists l'.
        split_and.
          by apply: subD1set.
        by apply/all2_tnthP.
      case contra : (l' ⊆ xl) => //.
      move: (subset_weight contra).
      rewrite /weight /= !big_cons leq_add2r.
      apply: size_contradiction.
      by apply: proper_card; apply: properD1.
    
    split.
      apply: (strict_subset_perm lp); apply: (proper bi).
      by rewrite -mem_enum E inE; apply/orP; right; rewrite inE eq_refl.
    split.
      apply: (strict_subset_perm lp); apply: (proper ai).
      by rewrite -mem_enum E inE eq_refl.
    split_and.
      move: (@cardsD1 _ bi big) ith_big.
      by case (bi \in big); rewrite /big /=; sslia.
      by apply: nonzero_behead; apply: nonzero_rot.
      move: (@cardsD1 _ ai big) ith_big.
      by case (ai \in big); rewrite /big /=; sslia.
      by apply: nonzero_behead; apply: nonzero_rot.
Qed.

Lemma strict_subset_wf' : ∀ len (a : line), weight a < len -> Acc strict_subset a.
  elim; first done.
  move=> n IH a wa.
  apply: Acc_intro => y /strict_subset_weight ywo; apply: IH.
  move: wa ywo; sslia.
Defined.

Lemma strict_subset_wf : well_founded (@strict_subset Δ).
  red; eauto using strict_subset_wf'.
Defined.

Lemma bigger_is_better' (a a' b b' : line) :
  all2 (λ x y : {set color}, x \subset y) a a' ->
  all2 (λ x y : {set color}, x \subset y) b b' ->
  all2 (λ x y : {set color}, x \subset y) (combine a b) (combine a' b').
Proof.
  rewrite /combine => /all2_tnthP-aa /all2_tnthP-bb /=.
  split_and.
    by rewrite /thead setUSS.
  apply/all2_tnthP => i. by rewrite !tnth_simpl !tnth_behead /= setISS.
Qed.

Lemma bigger_is_better a b c a' b' : a ⊆ a' -> b ⊆ b' -> combination_of a b c -> ∃ c', combination_of a' b' c' ∧ c ⊆ c'.
  move=> /existsP[a_] /existsP[a'_] /andP[/andP[peaa a'_sub]] a2
         /existsP[b_] /existsP[b'_] /andP[/andP[pebb b'_sub]] b2 comb.
  move: (tuple_permP peaa) => [a_sub a_subp].
  move: (tuple_permP pebb) => [b_sub b_subp].
  move: comb => [ac][bc][cc][/tuple_permP[comb_a comb_ap]][/tuple_permP[comb_b comb_bp]][/tuple_permP[comb_c comb_cp]] comb.
  pose comb_a' := (comb_a * a_sub)%g.
  pose comb_b' := (comb_b * b_sub)%g.
  pose a'' := [tuple tnth a'_ (comb_a' i) | i < Δ].
  pose b'' := [tuple tnth b'_ (comb_b' i) | i < Δ].
  exists (combine a'' b''); split.
    exists a'', b''.
    exists (combine a'' b''); split_and.
      rewrite perm_sym. apply: perm_trans. exact a'_sub.
      rewrite perm_sym.
      by apply/tuple_permP; exists comb_a'.
    rewrite perm_sym. apply: perm_trans. exact b'_sub.
    rewrite perm_sym.
    by apply/tuple_permP; exists comb_b'.

  have hlp (p1 p2 : 'S_Δ) x : (λ i, tnth x (p2 (p1 i))) =1 λ i, tnth x ((p1 * p2)%g i).
    by intros; rewrite /eqfun => i; rewrite permM.

  fill_ex [tuple tnth c (comb_c i) | i < Δ].
  fill_ex (combine a'' b'').
  split_and.
    by rewrite perm_sym; apply: any_perm.
  rewrite -comb_cp -comb; apply: bigger_is_better'.

  rewrite comb_ap /a'' /comb_a'.
  rewrite (val_inj a_subp) mktuple_mktuple.
  by rewrite (eq_mktuple _ (hlp _ _ _ _)) -all2_perm.

  rewrite comb_bp /b'' /comb_b'.
  rewrite (val_inj b_subp) mktuple_mktuple.
  by rewrite (eq_mktuple _ (hlp _ _ _ _)) -all2_perm.
Qed.

Inductive iterated_combination : line -> Prop :=
    present : ∀ a, a \in input -> nonzero a -> iterated_combination a
  | combined : ∀ (a b c : line), iterated_combination a -> iterated_combination b ->
      combination_of a b c -> nonzero c -> iterated_combination c.

Definition color_of_set1 (s : {set color}) (prf : #|s| = 1) : color :=
  thead (eq_rect _ (tuple_of^~ color) (enum_tuple s) _ prf).

Lemma set1_color_of_set1 s p : set1 (@color_of_set1 s p) = s.
  rewrite /color_of_set1.
  pose p2 := p; move: p2 => /eqP/cards1P[x xe].
  rewrite {3}xe /thead (tnth_nth x). destruct p. simpl.
  by rewrite xe enum_set1.
Qed.

Definition coloring_of_singleton (l : line) (prf : ∀ i, #|tnth l i| = 1) :=
  [tuple color_of_set1 (prf i) | i < Δ].

Lemma coloring_in_singleton (l : line) :
  (∀ i : 'I_Δ, #|tnth l i| == 1) -> ∃ c, l = map_tuple set1 c.
  setoid_rewrite <- (rwP eqP); move=> sz.
  exists (coloring_of_singleton sz).
  apply/eqP; rewrite /coloring_of_singleton eqEtuple; apply/forallP => i.
  by rewrite !tnth_map set1_color_of_set1 tnth_ord_tuple.
Qed.

Lemma bigger_nonzero (a b : line) : a ⊆ b -> nonzero a -> nonzero b.
  move=> /existsP[a'] /existsP[b'] /andP[/andP[pa pb] /all2_tnthP ss].
  rewrite /nonzero (perm_all _ pb) (perm_all _ pa) => /all_tnthP nz.
  apply/all_tnthP => i; move: (ss i) (nz i) => /subset_leq_card.
  by case: #|tnth b' i|; case: #|tnth a' i|.
Qed.

Theorem combination_is_complete :
  ∀ line, valid line -> nonzero line -> ∃ line', iterated_combination line' ∧ line ⊆ line'.
  elim/(well_founded_induction strict_subset_wf) => orig IH vorig nz.
  case E : [exists i : 'I_Δ, #|tnth orig i| > 1].
    move=> /existsP in E.
    move: (split_into_colorings vorig nz E) => [a][b][comb][lta][ltb][nza nzb].
    move: (IH a) => []//. apply: subset_valid. move: lta => /andP[]; eauto. done. move=> a' [a'c a'b].
    move: (IH b) => []//. apply: subset_valid. move: ltb => /andP[lol _]. apply: lol. by []. move=> b' [b'c b'b].
    move: (bigger_is_better a'b b'b comb) => [c'][comb' sz].
    exists c'; split_and.
    by apply: (combined a'c b'c) => //; apply: (bigger_nonzero sz).

  move=> /existsPn in E.
  have sz: ∀ i, #|tnth orig i| == 1. move=> i.
    move=> /all_tnthP in nz.
    by move: (E i) (nz i); case (#|tnth orig i|) => [//|]; case.

  move: (coloring_in_singleton sz) => [col col_line].
  have col_good : col ∈ orig.
    rewrite col_line; fill_ex col; split_and.
    by apply/all2_tnthP => i; rewrite !tnth_simpl; apply: set11.

  move: (vorig col col_good) => /exists_inP[inp inp2 /exists_inP[col' colp up]].
  exists inp.
  have orig_lt_inp: orig ⊆ inp.
    fill_ex (map_tuple set1 col'); fill_ex inp.
    split_and.
      by rewrite col_line perm_map // perm_sym.
    apply/all2_tnthP => i; rewrite !tnth_simpl.
    move: up => /all2_tnthP up; move: (up i).
    by rewrite sub1set.
  split_and.
  by constructor => //; apply: bigger_nonzero; eauto.
Qed.

Definition missing x := [forall y in input, x ⊈ y].

Lemma bigger_missing a b : a ⊆ b -> missing a -> missing b.
  move=> ab /forall_inP m.
  apply/forall_inP => i ii.
  move: (m i ii).
  case E : (b ⊈ i) => //.
  move: E => /eqP. rewrite eqbF_neg => /negPn bi.
  move: (subset_trans ab bi) => lol.
  by rewrite lol.
Qed.

Lemma combination_chain x : iterated_combination x ->
  (∃ x', x ⊆ x' ∧ x' \in input) ∨ ∃ a b c, a \in input ∧ b \in input ∧ combination_of a b c ∧ nonzero c ∧ missing c.
  elim.
    move=> a aa; left; exists a; split; by [apply: subset_refl |].
  move=> a b c ica [IHa|IHa] icb [IHb|IHb] comb; [|by right|by right|by right].
  case E : (missing c); last first.
    move: E => /forall_inPn[c' cin /negPn cc]; left; exists c'; by split.
  move: IHa IHb => [a' [asub ain]] [b' [bsub bin]].
  move: (bigger_is_better asub bsub comb) => [c' [comb' cc]].
  right; exists a', b', c'; split_and.
    by apply: (bigger_nonzero cc).
  by apply: (bigger_missing cc).
Qed.

Theorem combining_two_suffices (x : line):
  missing x -> nonzero x -> valid x ->
  ∃ a b c, a \in input ∧ b \in input ∧ combination_of a b c ∧ nonzero c ∧ missing c.
Proof.
  move=> missing_prf missingnz missingv.
  move: (combination_is_complete missingv missingnz) => [missing_super][ic super].
  move: (combination_chain ic) => [[super2 [super2' super2in]]|] => //.
  exfalso.
  have /forall_inP : missing super2.
    by apply: (bigger_missing super2'); apply: (bigger_missing super).
  move/ (_ super2 super2in).
  by rewrite subset_refl.
Qed.

End Lines.