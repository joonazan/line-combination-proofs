Require Import Coq.Unicode.Utf8_core Lia.
From mathcomp Require Import all_ssreflect all_fingroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma tnth_zip n S T (a : n.-tuple T) (b : n.-tuple S) i :
  tnth (zip_tuple a b) i = (tnth a i, tnth b i).
  by rewrite /tnth -nth_zip; [apply: set_nth_default|]; rewrite !size_tuple.
Qed.

Lemma tuple_f_equal n T (h h' : T) (t t' : n.-tuple T) :
  h = h' -> t = t' -> [tuple of h :: t] = [tuple of h' :: t'].
Proof. by intros; subst. Qed.

Lemma tnth_behead2 n (T: eqType) h (t : n.-tuple T) : behead_tuple [tuple of h :: t] = t.
Proof. by apply val_inj. Qed.

Definition tnth_simpl := (tnth_map, tnth_zip, tnth_ord_tuple, tnth_behead2).

Lemma all2Et n T S r (t : n.-tuple T) (s : n.-tuple S) : all2 r t s = all [pred xy | r xy.1 xy.2] (zip t s).
  by rewrite all2E !size_tuple eq_refl.
Qed.

Lemma all2_tnthP n T S (p : T -> S -> bool) (t : n.-tuple T) (s : n.-tuple S) :
  reflect (∀ i, p (tnth t i) (tnth s i)) (all2 p t s).
  rewrite all2Et.
  apply: (iffP all_tnthP);
  by move=> H i; move: (H i); rewrite tnth_simpl.
Qed.

Lemma all2_perm {n} {T} (p : 'S_n) (a b : n.-tuple T) f :
  all2 f a b <->
  all2 f [tuple tnth a (p i)  | i < n] [tuple tnth b (p i)  | i < n].
  split; move=> /all2_tnthP pre; apply/all2_tnthP => i.
    rewrite !tnth_simpl; by apply: pre.
  by move: (pre (p^-1 i)%g); rewrite !tnth_simpl permKV.
Qed.

Lemma any_perm n {T : finType} (p : 'S_n) (c : n.-tuple T) :
  perm_eq [tuple tnth c (p i) | i < n] c.
Proof. by apply/tuple_permP; exists p. Qed.

Lemma mktuple_mktuple {n T} (a : n.-tuple T) f g :
  [tuple tnth [tuple tnth a (g i0)  | i0 < n] (f i) | i < n] = [tuple tnth a (g (f i)) | i < n].
  apply: eq_mktuple.
  by rewrite /eqfun => i; rewrite tnth_mktuple.
Qed.

Lemma sym_impl_is_eq T (S : T -> T -> bool) (s : symmetric S) (P : pred T) :
  (∀ (a b : T), S a b -> P a -> P b) ->
  ∀ (a b : T), S a b -> P a = P b.
  move=> one_way a b sab.
  case E: (P b).
    apply: one_way; last apply: E.
    by rewrite s.
  case C: (P a) => //.
  by move: (one_way a b sab C); rewrite E.
Qed.

Lemma tuple_perm_cons : ∀ n (T : eqType) (x : T) (s1 s2 : n.-tuple T),
  perm_eq (x :: s1) (x :: s2) = perm_eq s1 s2.
Proof. by intros; apply: perm_cons. Qed.

Lemma tuple_zip_map : ∀ n (T : eqType) f (a b : n.-tuple T),
  zip_tuple [tuple tnth a (f i) | i < n] [tuple tnth b (f i) | i < n]
  = [tuple tnth (zip_tuple a b) (f i) | i < n].
Proof.
  intros.
  apply/eqP; rewrite eqEtuple; apply/forallP => i.
  by rewrite !tnth_simpl.
Qed.

Lemma tuple_tnth_map : ∀ n (T U : eqType) (f : T -> U) p (t : n.-tuple T),
  [tuple tnth (map_tuple f t) (p i) | i < n] = map_tuple f [tuple tnth t (p i) | i < n].
Proof.
  intros.
  apply/eqP; rewrite eqEtuple; apply/forallP => i.
  by rewrite !tnth_simpl.
Qed.

Ltac liafy := rewrite -?(rwP leP) -?(rwP ltP) -?(rwP negP) -?(rwP eqP) -?plusE.
Ltac sslia := liafy; lia.

Ltac split_and := repeat (split || (apply/andP; split); try done).
Ltac fill_ex x := apply/existsP; exists x.

Lemma tuple_perm_consP :
  ∀ n (T : eqType) (x : T) (s : n.-tuple T) (t : n.+1.-tuple T),
  perm_eq t [tuple of x :: s] ->
  (∃ (i : 'I_n.+1) (u : n.-tuple T), rot_tuple i t = [tuple of x :: u] ∧ perm_eq u s).
Proof.
  move=> n T x s t /perm_consP[i][u][r p].
  move: (perm_size p); rewrite size_tuple => /eqP sz.
  case E: (i < n.+1).
    exists (inord i); exists (Tuple sz); split_and.
    by apply: val_inj; rewrite inordK.
  exists ord0; exists (Tuple sz); split_and.
  apply: val_inj => /=; rewrite rot0.
  move: r; rewrite rot_oversize; first by move=> ->.
  by rewrite size_tuple leqNgt E.
Qed.