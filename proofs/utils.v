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

Ltac liafy := rewrite -?(rwP leP) -?(rwP ltP) -?(rwP negP) -?(rwP eqP) -?plusE.
Ltac sslia := liafy; lia.

Ltac split_and := repeat (split || (apply/andP; split); try done).
Ltac fill_ex x := apply/existsP; exists x.