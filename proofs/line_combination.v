Require Import Coq.Lists.ListSet.

Fixpoint Vec A n : Type :=
  match n with
  | 0 => unit
  | S n => A * Vec A n
  end.

Fixpoint map2 {N A B C} (f: A -> B -> C) (a: Vec A N) (b: Vec B N) :=
  match N as n return Vec A n -> Vec B n -> Vec C n with
    | 0 => fun _ _ => tt
    | S N => fun a b => match a, b with
      | (ah, a), (bh, b) => (f ah bh, map2 f a b)
    end
  end a b.

Fixpoint All {N} (xs: Vec Prop N) :=
  match N as n return Vec Prop n -> Prop with
  | 0 => fun _ => True
  | S _ => fun xs => match xs with
    | (h, t) => h /\ All t
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

Definition Line {N} := Vec (list nat) (S N).

Definition Coloring {N} := Vec nat (S N).

Definition generates {N} (coloring: @Coloring N) (line: @Line N) : Prop :=
  Forall2 coloring line (fun c l => set_In c l).

Definition nat_eq_dec: forall a b : nat, {a = b} + {a <> b}.
  decide equality.
Defined.

Definition combination {N} (a : @Line N) (b : @Line N) :=
  ( set_union nat_eq_dec (hd a) (hd b)
  , map2 (set_inter nat_eq_dec) (tl a) (tl b)
  ).

Theorem combination_is_sound {N} (a : @Line N) (b : @Line N):
forall c, generates c (combination a b) -> generates c a \/ generates c b.
  intros.
  destruct a, b, c.
  destruct H.
  apply set_union_elim in H; destruct H.
  
  left.
  split. assumption.
  induction N;
  destruct v, v0, v1, H0;
  split; eauto using set_inter_elim1.

  right.
  split. assumption.
  induction N;
  destruct v, v0, v1, H0;
  split; eauto using set_inter_elim2.
Qed.
