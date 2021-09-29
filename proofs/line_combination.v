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

Lemma subset_perm {n} {T : finType} (p : 'S_n) (a b : n.-tuple {set T}) :
  all2 (λ x y : {set T}, x \subset y) a b <->
  all2 (λ x y : {set T}, x \subset y) [tuple tnth a (p i)  | i < n] [tuple tnth b (p i)  | i < n].
  split; move=> /all2_tnthP => pre; apply/all2_tnthP => i.
    rewrite !tnth_map tnth_ord_tuple; by apply: pre.
  move: (pre (p^-1 i)%g); rewrite !tnth_map tnth_ord_tuple.
  by rewrite permKV.
Qed.

Lemma mktuple_mktuple {n T} (a : n.-tuple T) f g :
  [tuple tnth [tuple tnth a (g i0)  | i0 < n] (f i) | i < n] = [tuple tnth a (g (f i)) | i < n].
  apply: eq_mktuple.
  by rewrite /eqfun => i; rewrite tnth_mktuple.
Qed.

Ltac liafy := rewrite -?(rwP leP) -?(rwP ltP) -?(rwP negP) -?(rwP eqP) -?plusE.
Ltac sslia := liafy; lia.

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

Definition subset {n} (a b : n.-line) :=
  [exists a' : n.-line, exists b' : n.-line, perm_eq a a' && perm_eq b b' && all2 (λ x y : {set color}, x \subset y) a' b'].
Notation "a ⊆ b" := (subset a b) (at level 50, no associativity).
Notation "a ⊈ b" := (~~ subset a b) (at level 50, no associativity).
Definition strict_subset {n} (a b : n.-line) := (a ⊆ b) && (b ⊈ a).
Notation "a ⊂ b" := (strict_subset a b) (at level 50, no associativity).

Lemma subset_refl {n} (a : n.-line) : a ⊆ a.
  apply/existsP; exists a.
  apply/existsP; exists a.
  apply/andP; split; first by apply/andP; split.
  by apply/all2_tnthP.
Qed.

Lemma matching_subset (a b : line) :
  a ⊆ b -> [forall (x | x ∈ a), x ∈ b].
Proof.
  move=> /existsP[a'] /existsP[b'] /andP[/andP[ap bp]] /all2_tnthP sub.
  apply/forall_inP => x.
  rewrite (permutation_contains _ ap) (permutation_contains _ bp).
  move=> /exists_inP[x' px cu].
  apply/exists_inP. exists x'; auto.
  apply/all2_tnthP => i; specialize sub with i.
  move: cu => /all2_tnthP cu; specialize cu with i.
  move: sub => /subsetP sub.
  by apply: sub.
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
  rewrite pa pb /= => /all2_tnthP nss.
  rewrite (perm_weight pa) (perm_weight pb) /weight.
  move: nss => /forallP/forallPn[badi nss].
  have problem : #|tnth a' badi| < #|tnth b' badi|.
    by rewrite (ltn_leqif (subset_leqif_card (ss badi))).

  have apcs : val a' = take badi a' ++ tnth a' badi :: drop badi.+1 a'.
    by rewrite -drop_nth ?size_tuple // cat_take_drop.
  have bpcs : val b' = take badi b' ++ tnth b' badi :: drop badi.+1 b'.
    by rewrite -drop_nth ?size_tuple // cat_take_drop.
  rewrite apcs bpcs !big_cat !big_cons /=.
  apply: strict_subset_weight_math; rewrite // subset_weight //.

  apply/existsP; exists (take_tuple badi a').
  apply/existsP; exists (take_tuple badi b').
  apply/andP; split; first (apply/andP; by split).
  apply/all2_tnthP => i. rewrite !(tnth_nth set0) !nth_take;
    try (move: (ltn_ord i) (geq_minl badi Δ); sslia).
  move: ss. setoid_rewrite (tnth_nth set0). move/(_ (widen_ord _ i)) => x. apply: x.
  apply: geq_minr.

  apply/existsP; exists (drop_tuple badi.+1 a').
  apply/existsP; exists (drop_tuple badi.+1 b').
  apply/andP; split; first (apply/andP; by split).
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
  rewrite E2 in E.

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

    apply: val_inj.
    rewrite /=.
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
    apply/setP/eqfunP/forallP => x.
    rewrite in_set0 in_setI !in_set1.
    suff ne: bi != ai.
      case X: (x == bi). by move: X => /eqP X; rewrite X eqbF_neg. by [].
    have unik := enum_uniq (tnth l i); move: unik.
    rewrite E /= => /andP[] /memPn bi_not_ai trash.
    by apply: bi_not_ai; rewrite inE; apply/orP; left.

    rewrite perm_sym in lp.
    rewrite /strict_subset; split; [apply/andP; split | split; [apply/andP; split | split]].
      apply/existsP; exists a; apply/existsP; exists l'.
      apply/andP; split.
        by apply/andP; split; auto.
      rewrite all2Et /=.
      apply/andP; split.
        by apply: subD1set.
      apply/all_tnthP => j.
      by rewrite tnth_zip /=.

      case l_in_a: (l ⊆ a); last by [].
      apply subset_weight in l_in_a.
      move: l_in_a.
      rewrite (perm_weight lp) /weight /= !big_cons leq_add2r.
      apply: size_contradiction.
      apply: proper_card.
      apply: properD1.
      rewrite -mem_enum E.
      by rewrite inE; apply/orP; right; rewrite inE; apply/orP; left.

      apply/existsP; exists b; apply/existsP; exists l'.
      apply/andP; split.
        by apply/andP; split; auto.
      rewrite all2Et /=.
      apply/andP; split.
        by apply: subD1set.
      apply/all_tnthP => j.
      by rewrite tnth_zip /=.

      case l_in_a: (l ⊆ b); last by [].
      apply subset_weight in l_in_a.
      move: l_in_a.
      rewrite (perm_weight lp) /weight /= !big_cons leq_add2r.
      apply: size_contradiction.
      apply: proper_card.
      apply: properD1.
      rewrite -mem_enum E.
      by rewrite inE; apply/orP; left.

      rewrite /=; apply/andP; split.
        move: (@cardsD1 _ bi big) ith_big.
        case (bi \in big); rewrite /big /=; sslia.
      by apply: nonzero_behead; apply: nonzero_rot.

      rewrite /=; apply/andP; split.
        move: (@cardsD1 _ ai big) ith_big.
        case (ai \in big); rewrite /big /=; sslia.
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
  apply/andP; split.
    by rewrite /thead setUSS.
  apply/all2_tnthP => i; by rewrite !tnth_map !tnth_zip !tnth_behead /= setISS.
Qed.

Lemma bigger_is_better a b c a' b' : a ⊆ a' -> b ⊆ b' -> combination_of a b c -> ∃ c', combination_of a' b' c' ∧ c ⊆ c'.
  move=> /existsP[a_] /existsP[a'_] /andP[/andP[peaa a'_sub]] a2
         /existsP[b_] /existsP[b'_] /andP[/andP[pebb b'_sub]] b2 comb.
  move: (tuple_permP peaa) => [a_sub a_subp].
  move: (tuple_permP pebb) => [b_sub b_subp].
  move: a'_sub; rewrite perm_sym => /tuple_permP[sub_a' sub_a'p].
  move: b'_sub; rewrite perm_sym => /tuple_permP[sub_b' sub_b'p].
  move: comb => [ac][bc][cc][/tuple_permP[comb_a comb_ap]][/tuple_permP[comb_b comb_bp]][/tuple_permP[comb_c comb_cp]] comb.
  pose comb_a' := (comb_a * a_sub * sub_a')%g.
  pose comb_b' := (comb_b * b_sub * sub_b')%g.
  pose a'' := [tuple tnth a' (comb_a' i) | i < Δ].
  pose b'' := [tuple tnth b' (comb_b' i) | i < Δ].
  exists (combine a'' b''); split.
  exists a'', b''.
  exists (combine a'' b''); split.
    by apply/tuple_permP; exists comb_a'.
  split. by apply/tuple_permP; exists comb_b'.
  by split.
  apply/existsP; exists [tuple tnth c (comb_c i) | i < Δ].
  apply/existsP; exists (combine a'' b'').
  apply/andP; split.
  apply/andP; split.
    by rewrite perm_sym; apply/tuple_permP; exists comb_c.
  by [].
  rewrite -comb_cp -comb.
  apply: bigger_is_better'.

  rewrite comb_ap /a'' /comb_a'.
  move: a2. rewrite sub_a'p.
  move: peaa; rewrite perm_sym => /tuple_permP[a_sub_ a_subp_]; rewrite a_subp_.
  rewrite (subset_perm (a_sub)) !mktuple_mktuple (subset_perm comb_a) !mktuple_mktuple.
  have hlp : (λ i, tnth a' ((comb_a * a_sub * sub_a')%g i)) =1 λ i, tnth a' (sub_a' (a_sub (comb_a i))).
    by rewrite /eqfun => i; rewrite !permM.
  have hlp2 : (λ i, tnth a (a_sub_ (a_sub (comb_a i)))) =1 (λ i, tnth a (comb_a i)).
    rewrite /eqfun => i.
    by rewrite {2}(val_inj a_subp) tnth_map (val_inj a_subp_) tnth_map !tnth_ord_tuple.
  by rewrite (eq_mktuple _ hlp) (eq_mktuple _ hlp2).

  rewrite comb_bp /b'' /comb_b'.
  move: b2. rewrite sub_b'p.
  move: pebb; rewrite perm_sym => /tuple_permP[b_sub_ b_subp_]; rewrite b_subp_.
  rewrite (subset_perm (b_sub)) !mktuple_mktuple (subset_perm comb_b) !mktuple_mktuple.
  have hlp : (λ i, tnth b' ((comb_b * b_sub * sub_b')%g i)) =1 λ i, tnth b' (sub_b' (b_sub (comb_b i))).
    by rewrite /eqfun => i; rewrite !permM.
  have hlp2 : (λ i, tnth b (b_sub_ (b_sub (comb_b i)))) =1 (λ i, tnth b (comb_b i)).
    rewrite /eqfun => i.
    by rewrite {2}(val_inj b_subp) tnth_map (val_inj b_subp_) tnth_map !tnth_ord_tuple.
  by rewrite (eq_mktuple _ hlp) (eq_mktuple _ hlp2).
Qed.

Inductive iterated_combination : line -> Prop :=
    present : ∀ a, a \in input -> iterated_combination a
  | combined : ∀ (a b c : line), iterated_combination a -> iterated_combination b ->
      combination_of a b c -> iterated_combination c.

Definition color_of_set1 (s : {set color}) (prf : #|s| = 1) : color :=
  thead (eq_rect _ (tuple_of^~ color) (enum_tuple s) _ prf).

Lemma set1_color_of_set1 s p : set1 (@color_of_set1 s p) = s.
  rewrite /color_of_set1.
  pose p2 := p; move: p2 => /eqP/cards1P[x xe].
  rewrite {3}xe.
  rewrite /thead (tnth_nth x). destruct p. simpl.
  by rewrite xe enum_set1.
Qed.

Definition coloring_of_singleton (l : line) (prf : ∀ i, #|tnth l i| = 1) :=
  [tuple color_of_set1 (prf i) | i < Δ].

Lemma coloring_in_singleton (l : line) : (∀ i : 'I_Δ, #|tnth l i| == 1) -> ∃ c, l = map_tuple set1 c.
  setoid_rewrite <- (rwP eqP); move=> sz.
  exists (coloring_of_singleton sz).
  apply/eqP; rewrite /coloring_of_singleton eqEtuple; apply/forallP => i.
  by rewrite !tnth_map set1_color_of_set1 tnth_ord_tuple.
Qed.

Theorem combination_is_complete :
  ∀ line, valid line -> nonzero line -> ∃ line', iterated_combination line' ∧ line ⊆ line'.
  elim/(well_founded_induction strict_subset_wf) => orig IH vorig nz.
  case E : [exists i : 'I_Δ, #|tnth orig i| > 1].
    move=> /existsP in E.
    move: (split_into_colorings vorig nz E) => [a][b][comb][lta][ltb][nza nzb].
    move: (IH a) => []//. apply: subset_valid. move: lta => /andP[]. by eauto. by []. move=> a' [a'c a'b].
    move: (IH b) => []//. apply: subset_valid. move: ltb => /andP[lol _]. apply: lol. by []. move=> b' [b'c b'b].
    move: (bigger_is_better a'b b'b comb) => [c'][comb' sz].
    exists c'; split.
      by apply: (combined a'c b'c).
    done.

  move=> /existsPn in E.
  have sz: ∀ i, #|tnth orig i| == 1. move=> i.
    move=> /all_tnthP in nz.
    move: (E i) (nz i); case (#|tnth orig i|) => [//|]; by case.
  move:(coloring_in_singleton sz) => [col col_line].
  have col_good : col ∈ orig.
    rewrite col_line; apply/exists_inP; exists col. done.
    apply/all2_tnthP => i. rewrite tnth_map. by apply: set11.

  move: (vorig col col_good) => /exists_inP[inp inp2 /exists_inP[col' colp up]].
  exists inp; split.
    by apply: present.
  apply/existsP; exists (map_tuple set1 col').
  apply/existsP; exists inp.
  apply/andP; split; [apply/andP; split; [|done]| apply/all2_tnthP => i].
    by rewrite col_line perm_map // perm_sym.
  rewrite tnth_map.
  move: up => /all2_tnthP up; move: (up i).
  by rewrite sub1set.
Qed.

Theorem combining_two_suffices {N} (lines : list (@Line (S N))) (missing : @Line (S N)):
(∀ line, set_In line lines -> missing ⊈ line) -> valid missing lines ->
  ∃ a b c, set_In a lines ∧ set_In b lines ∧ IsCombinationOfTwo a b c ∧ ∀ line, set_In line lines -> c ⊈ line.
