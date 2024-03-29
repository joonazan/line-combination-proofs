Require Import Coq.Unicode.Utf8_core.
From mathcomp Require Import all_ssreflect all_fingroup.
Require Import utils.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Lines.

Variable alphabet_size: nat.
Definition color := 'I_alphabet_size.
Variable delta_minus_one: nat.
Definition Δ := delta_minus_one.+1.

Definition nline n := n.-tuple {set color}.
Notation "n .-line" := (nline n) (at level 30, no associativity).
Definition line := Δ.-line.
Definition configuration := Δ.-tuple color.

Definition contains_unpermuted (cl: configuration) (l: line) : bool :=
  all2 (λ c (s : {set color}), c \in s) cl l.

Definition contains (cl : configuration) (line : line) : bool :=
  [exists (p : configuration | perm_eq p cl), contains_unpermuted p line].

Notation "a ∈ L" := (contains a L) (at level 50, no associativity).

Lemma perm_rew_helper n (T : eqType) (P : pred (n.-tuple T)) :
  (∀ (a b : n.-tuple T), perm_eq a b -> P a -> P b) ->
  ∀ (a b : n.-tuple T), perm_eq a b -> P a = P b.
  apply: sym_impl_is_eq.
  by apply: perm_sym.
Qed.

Lemma perm_rew_helper2 n (T : eqType) U (P2 : n.-tuple T -> U -> bool) :
  (∀ (a a' : n.-tuple T) b, perm_eq a a' -> P2 a b -> P2 a' b) ->
  ∀ (a a' : n.-tuple T) b, perm_eq a a' -> P2 a b = P2 a' b.
  move=> one_way a a' b.
  apply: (@perm_rew_helper _ _ (P2^~ b)) => aa aa'.
  by apply: one_way.
Qed.

Lemma contains_permutation : ∀ (a a' : configuration) s, perm_eq a a' -> a ∈ s = a' ∈ s.
  apply: perm_rew_helper2.
  move=> a a' s pe /existsP[x] /andP[pe2 unper].
  fill_ex x; apply/andP; split; rewrite //.
  by apply: perm_trans; eassumption.
Qed.

Lemma permutation_contains : ∀ a (s s' : line), perm_eq s s' -> a ∈ s = a ∈ s'.
  move=> c.
  apply: perm_rew_helper => s s' pe.
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

Definition combine m (n := m.+1) (a : n.-line) (b : n.-line) : n.-line :=
  [tuple of (thead a) :|: (thead b)
  :: map (λ ab, ab.1 :&: ab.2) (zip (behead a) (behead b))
  ].

Definition combination_of (a b c : line) :=
  ∃ (a' b' c' : line),
    perm_eq a' a ∧ perm_eq b' b ∧ perm_eq c' c ∧ combine a' b' = c'.

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

Definition dominates {n} (b a : n.-line) :=
  [exists a' : n.-line, exists b' : n.-line, perm_eq a a' && perm_eq b b' &&
    all2 (λ x y : {set color}, x \subset y) a' b'].
Notation "a ⊆ b" := (dominates b a) (at level 50, no associativity).
Notation "a ⊈ b" := (~~ dominates b a) (at level 50, no associativity).
Definition strictly_dominates {n} (b a : n.-line) := (a ⊆ b) && (b ⊈ a).
Notation "a ⊂ b" := (strictly_dominates b a) (at level 50, no associativity).

Lemma dominates_refl {n} (a : n.-line) : a ⊆ a.
  fill_ex a.
  fill_ex a.
  split_and.
  by apply/all2_tnthP.
Qed.

Lemma dominates_trans {n} (a b c : n.-line) : a ⊆ b -> b ⊆ c -> a ⊆ c.
  move=> /existsP[a'] /existsP[b'] /andP[/andP[pa pb] /all2_tnthP ss].
  move=> /existsP[b''] /existsP[c''] /andP[/andP[pb2 pc] /all2_tnthP ss2].
  have /tuple_permP[p pp] : perm_eq b' b''.
    by apply: perm_trans; [rewrite perm_sym; apply pb|].
  fill_ex a'.
  fill_ex [tuple tnth c'' (p i) | i < n].
  split_and.
    by apply: (perm_trans pc); rewrite perm_sym any_perm.
  apply/all2_tnthP => i; rewrite tnth_mktuple.
  apply: subset_trans; last apply: ss2.
  apply: subset_trans; first apply: ss.
  by move: pp => /val_inj pp; rewrite pp tnth_mktuple.
Qed.

Lemma dominates_configurations (a b : line) :
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

Lemma dominates_perm a : ∀ (b b' : line), perm_eq b b' -> a ⊆ b = a ⊆ b'.
  apply: perm_rew_helper.
  move=> b b' pe /existsP[a' /existsP[b'' /andP[/andP[aa bb] ss]]].
  fill_ex a'; fill_ex b''; split_and.
  by apply: perm_trans; [rewrite perm_sym; eassumption |].
Qed.

Lemma dominates_perm2 : ∀ (b a a' : line), perm_eq a a' -> a ⊆ b = a' ⊆ b.
  move=> b.
  apply: perm_rew_helper => a a' pe.
  move=> /existsP[a'' /existsP[b' /andP[/andP[aa bb] ss]]].
  fill_ex a''; fill_ex b'; split_and.
  by apply: perm_trans; [rewrite perm_sym; eassumption |].
Qed.

Lemma strictly_dominates_perm (a b b' : line) : perm_eq b b' -> a ⊂ b = a ⊂ b'.
  move=> pe.
  rewrite /strictly_dominates (dominates_perm2 _ pe).
  rewrite perm_sym in pe.
  by rewrite (dominates_perm _ pe).
Qed.

Lemma strictly_dominates_perm2 (a a' b : line) : perm_eq a a' -> a ⊂ b = a' ⊂ b.
  move=> pe.
  rewrite /strictly_dominates (dominates_perm2 _ pe).
  rewrite perm_sym in pe.
  by rewrite (dominates_perm _ pe).
Qed.

Definition weight (l : seq {set color}) := \sum_(i <- l) #|i|.

Lemma sum_map {n T} f (a : n.-tuple T) : \sum_(i <- a) f i = \sum_(i <- map_tuple f a) i.
  by rewrite big_map.
Qed.

Lemma perm_weight {n} (a a' : n.-line) : perm_eq a a' -> weight a = weight a'.
  move=> pe; rewrite /weight [in RHS]sum_map sum_map -!sumnE.
  by apply: perm_sumn; apply: perm_map.
Qed.

Lemma dominates_weight {n} (a b : n.-line) : a ⊆ b -> weight a <= weight b.
  move=> /existsP[a'] /existsP[b'] /andP[/andP[pa pb] /all2_tnthP ss].
  rewrite (perm_weight pa) (perm_weight pb).
  rewrite /weight !big_tuple.
  apply: leq_sum => i _.
  by apply: subset_leq_card.
Qed.

Lemma strictly_dominates_weight_math a1 a2 b1 b2 c1 c2 :
  a1 <= a2 -> b1 < b2 -> c1 <= c2 -> a1 + (b1 + c1) < a2 + (b2 + c2).
Proof. by sslia. Qed.

Lemma strictly_dominates_weight (a b : line) : a ⊂ b -> weight a < weight b.
  move=> /andP[] /existsP[a'] /existsP[b'] /andP[/andP[pa pb] /all2_tnthP ss].
  rewrite /dominates negb_exists => /forallP; move/(_ b').
  rewrite /dominates negb_exists => /forallP; move/(_ a').
  rewrite pa pb /= => /all2_tnthP /forallP/forallPn[badi nss].
  rewrite (perm_weight pa) (perm_weight pb) /weight.

  have separate_bad : ∀ t : line, val t = take badi t ++ tnth t badi :: drop badi.+1 t.
    by intro; rewrite -drop_nth ?size_tuple // cat_take_drop.
  rewrite (separate_bad a') (separate_bad b') !big_cat !big_cons /=.
  apply: strictly_dominates_weight_math;
    [| by rewrite (ltn_leqif (subset_leqif_card (ss badi))) |];
    apply: dominates_weight.

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

Lemma split_into_configurations (l : line) :
  nonzero l -> (∃ i : 'I_Δ, #|tnth l i| > 1) ->
  ∃ a b, combination_of a b l ∧
  a ⊂ l ∧ b ⊂ l ∧
  nonzero a ∧ nonzero b.
Proof.
  move=> nz [i ith_big].
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

  have lp : perm_eq l l'.
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
      by rewrite perm_sym.

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
      move: (dominates_weight contra).
      rewrite /weight /= !big_cons leq_add2r.
      apply: size_contradiction.
      by apply: proper_card; apply: properD1.
    
    split.
      rewrite (strictly_dominates_perm _ lp); apply: (proper bi).
      by rewrite -mem_enum E inE; apply/orP; right; rewrite inE eq_refl.
    split.
      rewrite (strictly_dominates_perm _ lp); apply: (proper ai).
      by rewrite -mem_enum E inE eq_refl.
    split_and.
      move: (@cardsD1 _ bi big) ith_big.
      by case (bi \in big); rewrite /big /=; sslia.
      by apply: nonzero_behead; apply: nonzero_rot.
      move: (@cardsD1 _ ai big) ith_big.
      by case (ai \in big); rewrite /big /=; sslia.
      by apply: nonzero_behead; apply: nonzero_rot.
Qed.

Definition strictly_dominated (a b : line) := strictly_dominates b a.

Lemma strictly_dominated_wf' : ∀ len (a : line), weight a < len -> Acc strictly_dominated a.
  elim; first done.
  move=> n IH a wa.
  apply: Acc_intro => y /strictly_dominates_weight ywo; apply: IH.
  move: wa ywo; sslia.
Defined.

Lemma strictly_dominated_wf : well_founded strictly_dominated.
  red; eauto using strictly_dominated_wf'.
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

Variable input : seq line.
Variable input_nonzero: ∀ x, x \in input -> nonzero x.

Definition valid (l : line) :=
  [forall (x | x ∈ l), [exists i in input, x ∈ i]].

Lemma dominated_valid (a b : line) : a ⊆ b -> valid b -> valid a.
  move=> /dominates_configurations/forall_inP subset vb.
  apply/forall_inP => x x_in_a. apply: (forall_inP vb).
  by apply: subset.
Qed.

Inductive iterated_combination : line -> Prop :=
    present : ∀ a, a \in input -> iterated_combination a
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

Definition configuration_of_singleton (l : line) (prf : ∀ i, #|tnth l i| = 1) :=
  [tuple color_of_set1 (prf i) | i < Δ].

Lemma configuration_in_singleton (l : line) :
  (∀ i : 'I_Δ, #|tnth l i| == 1) -> ∃ c, l = map_tuple set1 c.
  setoid_rewrite <- (rwP eqP); move=> sz.
  exists (configuration_of_singleton sz).
  apply/eqP; rewrite /configuration_of_singleton eqEtuple; apply/forallP => i.
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
  elim/(well_founded_induction strictly_dominated_wf) => orig IH vorig nz.
  case E : [exists i : 'I_Δ, #|tnth orig i| > 1].
    move=> /existsP in E.
    move: (split_into_configurations nz E) => [a][b][comb][lta][ltb][nza nzb].
    move: (IH a) => []//. apply: dominated_valid. move: lta => /andP[]; eauto. done. move=> a' [a'c a'b].
    move: (IH b) => []//. apply: dominated_valid. move: ltb => /andP[lol _]. apply: lol. by []. move=> b' [b'c b'b].
    move: (bigger_is_better a'b b'b comb) => [c'][comb' sz].
    exists c'; split_and.
    by apply: (combined a'c b'c) => //; apply: (bigger_nonzero sz).

  move=> /existsPn in E.
  have sz: ∀ i, #|tnth orig i| == 1. move=> i.
    move=> /all_tnthP in nz.
    by move: (E i) (nz i); case (#|tnth orig i|) => [//|]; case.

  move: (configuration_in_singleton sz) => [col col_line].
  have col_good : col ∈ orig.
    rewrite col_line; fill_ex col; split_and.
    by apply/all2_tnthP => i; rewrite !tnth_simpl; apply: set11.

  move: ((forall_inP vorig) col col_good) => /exists_inP[inp inp2 /exists_inP[col' colp up]].
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
  move: (dominates_trans ab bi) => lol.
  by rewrite lol.
Qed.

Lemma missing_perm (a b : line) : perm_eq a b -> missing a -> missing b.
  move=> pe /forall_inP ma.
  apply/forall_inP => x /(ma x).
  by rewrite (dominates_perm2 _ pe).
Qed.

Lemma combination_chain x : iterated_combination x -> missing x ->
  ∃ a b c, a \in input ∧ b \in input ∧ combination_of a b c ∧ nonzero c ∧ missing c.
  elim.
    by move=> a aa /forallP; move/(_ a); rewrite aa dominates_refl.
  move=> a b c ica IHa icb IHb comb nzc mc.
  case Ea : (missing a). by apply: IHa.
  move: Ea => /forall_inPn[a' a'i /negPn a'd].
  case Eb : (missing b). by apply: IHb.
  move: Eb => /forall_inPn[b' b'i /negPn b'd].
  move: (bigger_is_better a'd b'd comb) => [c' [c'c c'd]].
  exists a', b', c'.
  split_and.
    by apply: (bigger_nonzero c'd).
  by apply: (bigger_missing c'd).
Qed.

Theorem combining_two_suffices (x : line):
  missing x -> nonzero x -> valid x ->
  ∃ a b c, a \in input ∧ b \in input ∧ combination_of a b c ∧ nonzero c ∧ missing c.
Proof.
  move=> missing_prf missingnz missingv.
  move: (combination_is_complete missingv missingnz) => [missing_super][ic super].
  apply: (combination_chain ic).
  by apply: (bigger_missing super).
Qed.

Definition tuple_permutations n T (t : n.-tuple T) :=
  [seq [tuple tnth t (aperm i p) | i < n] | p <- enum 'S_n].

Lemma tuple_permutations_correct (a a' : line) : a' \in tuple_permutations a <-> perm_eq a a'.
  split.
    move=> /mapP[p pe e].
    rewrite perm_sym; apply/tuple_permP; exists p.
    by rewrite e.
  rewrite perm_sym.
  move=> /tuple_permP[p] pe.
  apply/mapP; exists p.
    by apply/mapP; exists p.
  by rewrite (val_inj pe).
Qed.

Definition rotations n T (t : n.-tuple T) : seq (n.-tuple T) :=
  [seq rot_tuple (val i) t | i <- enum 'I_n].

Definition all_combinations (a b : line) :=
  flatten (map (λ a', map (combine a') (rotations b)) (tuple_permutations a)).

Lemma all_combinations_correct a b :
  ∀ c : line, (∃ c' : line, perm_eq c c' ∧ c' \in all_combinations a b) <-> combination_of a b c.
Proof.
  split.
    move=> [c'][pe] /flatten_mapP/=[a' ap /mapP/=[b' /mapP[i ii br] comb]].
    exists a', b', c'; split_and.
      by rewrite perm_sym -tuple_permutations_correct.
      by rewrite br; rewrite perm_rot.
      by rewrite perm_sym.
  move=> [a'][b'][c'][].
  case/tupleP: a' => a'h a't.
  case/tupleP: b' => b'h b't.
  rewrite perm_sym => [pa][pb].
  suff: ∃ (i : 'I_Δ) (b't' : delta_minus_one.-line), perm_eq b't b't' ∧ rot i b = [tuple of b'h :: b't'].
    move=> [i][b't'][peb rb][pc] comb.
    move: peb; rewrite perm_sym => /tuple_permP[p ppb].
    exists (combine [tuple of a'h :: [tuple tnth a't (p i) | i < delta_minus_one]] [tuple of b'h :: b't']); split_and.
      apply: perm_trans; first by rewrite perm_sym; apply: pc.
      rewrite -comb /combine !theadE tuple_perm_cons.
      rewrite perm_sym; apply/tuple_permP; exists p.
      by rewrite (val_inj ppb) !tnth_simpl tuple_zip_map tuple_tnth_map.
    apply/flatten_mapP; exists [tuple of a'h :: [tuple tnth a't (p i0) | i0 < delta_minus_one]].
      apply tuple_permutations_correct.
      apply: perm_trans; first by apply: pa.
      by rewrite perm_cons perm_sym; apply: any_perm.
    apply/mapP. exists [tuple of b'h :: b't'] => //.
    apply/mapP; exists i.
      by rewrite mem_enum.
    by apply: val_inj => /=.  
  move: pb; rewrite perm_sym => /tuple_perm_consP[i][b't'][rt pet].
  exists i; exists b't'; split.
    by rewrite perm_sym.
  by rewrite -rt.
Qed.

Definition cannot_find_more :=
  [forall a in input, [forall b in input,
    [forall c in all_combinations a b, ~~ (missing c && nonzero c)]]].

Definition none_dominated :=
  [forall a in input, forall b in input, ~~ (a ⊂ b)].

Definition is_maximal_form :=
  cannot_find_more && none_dominated.

Definition maximal x := valid x && [forall (y | valid y), ~~ (x ⊂ y)].

Lemma input_valid x : x \in input -> valid x.
  move => inp.
  apply/forall_inP => c cinx.
  fill_ex x; split_and.
Qed.

Lemma perm_le_eq (a b : Δ.-tuple nat) :
  perm_eq a b ->
  (∀ i, tnth a i <= tnth b i) -> a == b.
Proof.
  move=> pe.
  have: \sum_(i <- a) i = \sum_(i <- b) i.
    by apply: perm_big.
  move: pe => _; move: a b.
  elim Δ.
    by move=> a b _ _; rewrite -(rwP eqP) [in RHS]tuple0 tuple0.
  move=> n ih a b.
  case/tupleP: a => ah a.
  case/tupleP: b => bh b.
  rewrite !big_cons => eq_sum /all2_tnthP. rewrite all2Et => /= /andP[le_h].
  rewrite -all2Et => /all2_tnthP le_ab.
  suff: \sum_(i <- a) i <= \sum_(i <- b) i.
    rewrite leq_eqVlt => /orP[]; last first.
      by move: eq_sum le_h; sslia.
    move=> /eqP eq_sum_ab.
    apply/eqP; apply: tuple_f_equal.
      by move: eq_sum eq_sum_ab; sslia.
    by apply/eqP; apply: ih.
  by rewrite !big_tuple; apply: leq_sum => i _.
Qed.

Lemma perm_card_le_eq (a b : line) :
  perm_eq a b ->
  (∀ i, #|tnth a i| <= #|tnth b i|) -> ∀ i, #|tnth a i| == #|tnth b i|.
Proof.
  move=> pe le.
  have precompute: ∀ (x : line) i, #|tnth x i| = tnth [tuple #|tnth x i| | i < Δ] i.
    by intros; rewrite !tnth_simpl.
  move=> i.
  rewrite !precompute.
  move: i; apply/forallP; rewrite -eqEtuple; apply: perm_le_eq.
    have asd: ∀ t : line, val [tuple #|tnth t i| | i < Δ] = [seq #|x| | x : {set color} <- val t].
      move=> t.
      have: [seq #|tnth t i| | i <- enum 'I_Δ] = [seq #|x| | x : {set color} <- [seq tnth t i | i <- enum 'I_Δ]].
        by rewrite -map_comp.
      by rewrite map_tnth_enum.
    by rewrite !asd; apply: perm_map.
  by move=> i; rewrite !tnth_simpl.
Qed.

Lemma dominates_antisym (a b : line) : a ⊆ b -> b ⊆ a -> perm_eq a b.
  move=> /existsP[a'] /existsP[b'] /andP[]/andP[] pa' pb' /all2_tnthP ainb.
  move=> /existsP[b''] /existsP[a''] /andP[]/andP[] pb'' pa'' /all2_tnthP bina.
  simpl in *.
  have /tuple_permP[p pp] : perm_eq b' b''.
    apply: perm_trans; last apply: pb''.
    by rewrite perm_sym.
  suff a_eq_b : a' == b'.
    apply: (perm_trans pa').
    by rewrite (eqP a_eq_b) perm_sym.
  have bina2: ∀ i, tnth b' i \subset tnth a'' (p i).
    move=> i.
    move: pp => /val_inj/eqP. rewrite eqEtuple => /forallP pp. move:(pp i).
    rewrite !tnth_simpl => /eqP pp2.
    by rewrite pp2.
  have asuba: ∀ i, tnth a' i \subset tnth a'' (p i).
    by move=> i; apply: subset_trans; first apply: ainb.
  have eq_aa': a' == [tuple tnth a'' (p j) | j < Δ].
    rewrite eqEtuple; apply/forallP => i.
    apply/eqP/setP/subset_cardP.
    apply/eqP; apply perm_card_le_eq.
      have /tuple_permP[ap app]: perm_eq a'' a'.
        rewrite perm_sym. apply: perm_trans; last apply: pa''.
        by rewrite perm_sym.
      rewrite (val_inj app).
      rewrite mktuple_mktuple.
      rewrite perm_sym.
      apply/tuple_permP. exists (p * ap)%g.
      have hlp: (λ x, tnth a' (ap (p x))) =1 λ x, tnth a' ((p * ap)%g x).
        by move=> k; rewrite permM.
      by apply/eqP; rewrite (eq_mktuple _ hlp).
      move=> j.
      rewrite !tnth_simpl.
      by apply: subset_leq_card.
    by rewrite !tnth_simpl.
  rewrite eqEtuple; apply/forallP => i.
  rewrite eqEsubset; split_and.
  by rewrite (eqP eq_aa') !tnth_simpl.
Qed.

Definition weight_max := Δ * alphabet_size.

Lemma weight_max_max (x : line) : weight x <= weight_max.
  unfold weight.
  suff X: weight_max = \sum_(i <- x) alphabet_size.
    rewrite X.
    apply: leq_sum => i _.
    by move: (max_card i); rewrite card_ord.
  by rewrite big_tuple sum_nat_const card_ord.
Qed.

Lemma maximals_cover (x : line) :
  valid x -> ∃ y, maximal y ∧ x ⊆ y.
Proof.
  have [n wx] := ubnP (weight_max - weight x); elim: n => // n IH in x wx *.
  move=> vx.
  case E: (maximal x).
    exists x. split_and.
    by apply: dominates_refl.
  rewrite /maximal in E.
  move: E; rewrite (rwP negPf) negb_and => /orP[].
    by rewrite vx.
  move=> /forallPn[y]. rewrite negb_imply => /andP[vy]/negPn dom_yx.
  move: (IH y) => []//.
    move: wx; rewrite !ltn_subLR;
    first (move: (strictly_dominates_weight dom_yx); sslia);
    apply: weight_max_max.
  move=> x' [mx' domy].
  exists x'; split_and.
  apply: (dominates_trans _ domy).
  by move: dom_yx => /andP[].
Qed.

Lemma nonzero_perm : ∀ (a b : line), perm_eq a b -> nonzero a = nonzero b.
  apply: perm_rew_helper.
  move=> a b pe nza.
  apply: bigger_nonzero; last apply: nza.
  by rewrite (dominates_perm2 _ pe); apply: dominates_refl.
Qed.

Lemma cannot_find_more_works :
  cannot_find_more <->
  (∀ x : line, nonzero x -> maximal x -> [exists y in input, perm_eq x y]).
Proof.
  split.
    move=> cfm x nz /andP[vx mx].
    case E : [exists y in input, perm_eq x y] => //.
    move: E => /exists_inPn /= not_in_input.
    have miss: missing x.
      apply/forall_inP => y yin.
      case C : (x ⊆ y) => //=.
      case D : (y ⊆ x).
        move: (not_in_input y yin) => /negPf <-.
        by apply: dominates_antisym.
      suff: (~~ (x ⊂ y)).
        move=> /negPf <-.
        split_and.
        by apply/negPf.
      apply: (forall_inP mx).
      by apply: input_valid.
    move: (combining_two_suffices miss nz vx) => [a][b][c][ain][bin][cin][nzc mc].
    move: cin; rewrite <- all_combinations_correct. move=> [c'][pec]cin.
    move: (forall_inP cfm a ain) => /forall_inP/(_ b bin)/forall_inP/(_ c' cin).
    by rewrite -(nonzero_perm pec) nzc (missing_perm pec).
  move=> has_maximals.
  apply/forall_inP => a ain.
  apply/forall_inP => b bin.
  apply/forall_inP => c cin.
  move: (@maximals_cover c) => [].
    rewrite -(rwP forall_inP) => x in_xc.
    move: (@combination_is_sound a b c x) => [] //.
      apply all_combinations_correct.
      by exists c; split_and.
    by intro; fill_ex a; split_and.
    by intro; fill_ex b; split_and.
  move=> m [mm in_cm].
  case E: (nonzero c); apply/nandP; [left | by right].
  move: (bigger_nonzero in_cm E) => nzm.
  move: (has_maximals m nzm mm) => /exists_inP[m' m'_in pe_m'].
  apply/forallPn => /=; exists m'.
  rewrite m'_in => /=; apply/negPn.
  by rewrite -(dominates_perm _ pe_m').
Qed.

Theorem is_maximal_form_works :
  is_maximal_form <-> (∀ x : line, nonzero x -> [exists y in input, perm_eq x y] <-> maximal x).
Proof.
  split.
    move=> /andP[/cannot_find_more_works cfm nd] x nzx.
    split.
      move=> /exists_inP[y yin pey].
      split_and.
        apply: dominated_valid; last first.
          by apply: input_valid; apply: yin.
        by rewrite (dominates_perm2 _ pey); apply dominates_refl.
      rewrite -(rwP forall_inP) => a va.
      move: nd => /(forall_inPP _ (λ x, forall_inP)) /= nd.
      rewrite (strictly_dominates_perm2 _ pey).
      move: (maximals_cover va) => [ma [mma dom_ama]].
      case E: (y ⊂ a) => //.
      have nzy: nonzero y.
        by apply: input_nonzero.
      have nzma: nonzero ma.
        apply: bigger_nonzero; last apply: nzy.
        apply: dominates_trans; last apply: dom_ama.
        by move: E => /andP[].
      move: (cfm ma nzma mma) => /exists_inP[ma' inma' pema'].
      suff: y ⊂ ma'.
        by move=> <-; apply: nd.
      rewrite -(strictly_dominates_perm _ pema').
      split_and.
        apply: dominates_trans; last apply: dom_ama.
        by move: E => /andP[].
      move: E => /andP[_].
      case E: (ma ⊆ y) => //.
      have: (a ⊆ y).
        by apply: dominates_trans; [apply: dom_ama |].
      by move=> <-.
    by apply: cfm.
  move=> input_maximal.
  split_and.
    by apply cannot_find_more_works; apply input_maximal.
  rewrite /none_dominated.
  apply/forall_inP => a ain.
  apply/forall_inP => b bin.
  suff: maximal a.
    move=> /andP[_ /forall_inP max].
    by apply: max; apply: input_valid.
  apply input_maximal.
    by apply: input_nonzero.
  apply/exists_inP.
  by exists a.
Qed.

Definition maximize_step res new :=
  if all (λ x, new ⊈ x) res then
    ( new :: filter (λ x, x ⊈ new) res
    , flatten [seq all_combinations x new | x <- res]
    )
  else
    (res, [::]).

Definition maximality_le (a b : seq line) :=
  [forall x in a, [exists y in b, x ⊆ y]].

Definition less_maximal a b := maximality_le a b && ~~ maximality_le b a.

Require Import Program.

Definition maximize_progress (a b : seq line * seq line) :=
  let: (res, todo) := a in
  let: (res2, todo2) := b in less_maximal res2 res ∨ res = res2 ∧ length todo < length todo2.

Program Fixpoint maximize' res todo {measure (res, todo) maximize_progress} :=
  match todo with
  | h :: t => let: (res', jobs) := maximize_step res h in maximize' res' (jobs ++ t)
  | [::] => res
  end.

Next Obligation.
move: Heq_anonymous; rewrite /maximize_step.
case E : (all (λ x : line, h ⊈ x) res);
  last by move=> []; elim => a; right; rewrite a.
move=> [a _]; left; rewrite {}a.
rewrite /less_maximal; split_and; rewrite /maximality_le; last first.
  apply/forall_inPn; exists h.
    by rewrite mem_head.
  by apply/exists_inPn => x /allP xin; apply xin in E.
apply/forall_inP => x xin.
apply/exists_inP.
case E2 : (x ⊆ h).
  by exists h => //; rewrite mem_head.
exists x.
  by rewrite inE; apply/orP; right; rewrite mem_filter E2.
by apply dominates_refl.
Qed.

Definition missing_from (lines : seq line) :=
  #|[set x | [forall y in lines, x ⊈ y]]|.

Lemma less_maximal_missing_from :
  ∀ a b, less_maximal a b -> missing_from b < missing_from a.
Proof.
  move=> a b /andP[le nle].
  apply proper_card; rewrite properE.
  split_and.
    apply/subsetPn; case => /= x;
    rewrite !in_set => x_notin_b /forall_inPn[y y_in_a] /negPn.
    move: le => /forall_inP. move/ (_ y y_in_a) => /exists_inP[y' y'b yy xy].
    move: (dominates_trans xy yy) => tru. move: x_notin_b => /forall_inP. move/ (_ y' y'b).
    by rewrite tru.
  apply/subsetPn; move: nle => /forall_inPn[bad bad_in_b] /exists_inPn bad_a.
  exists bad; rewrite in_set.
    by apply/forall_inP.
  apply/forall_inPn. exists bad => //.
  by apply/negPn; apply dominates_refl.
Qed.

Lemma maximize_progress_wf' : ∀ n m res todo,
  missing_from res < n -> length todo < m -> Acc maximize_progress (res, todo).
Proof.
  elim; first done; move=> n IHn.
  elim; first done; move=> m IHm res todo mf len.
  constructor => y. destruct y.
  move=> []; last first.
    move=> [eq] lens. rewrite {}eq. apply IHm => //. by move: len lens; sslia.
  move=> /less_maximal_missing_from mf2.
  apply (IHn (length l0).+1) => //.
  by move: mf mf2; sslia.
Qed.

Next Obligation.
apply measure_wf; red => a. destruct a.
eauto using maximize_progress_wf'.
Qed.

Definition maximized := maximize' [::] input.

(* Theorem maximize_works : ∀ x, x \in maximized <-> maximal x. *)

End Lines.
