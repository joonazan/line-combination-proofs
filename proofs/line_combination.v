Require Coq.Vectors.Vector.
Require Import Coq.Lists.ListSet.
Require Import Program.

Definition Line {N} := Vector.t (list nat) (S N).

Definition Coloring {N} := Vector.t nat (S N).

Definition generates {N} (coloring: @Coloring N) (line: @Line N) :=
  Vector.Forall2 (fun col s => set_In col s) coloring line.

Definition nat_eq_dec: forall a b : nat, {a = b} + {a <> b}.
  decide equality.
Defined.

Definition combination {N} (a: @Line N) (b: @Line N) :=
  Vector.cons _ (set_union nat_eq_dec (Vector.hd a) (Vector.hd b))
              N (Vector.map2 (set_inter nat_eq_dec) (Vector.tl a) (Vector.tl b)).

Theorem combination_is_sound {N} (a : @Line N) (b : @Line N): forall c, generates c (combination a b) -> generates c a \/ generates c b.
  intros.
  unfold combination in H.
  unfold Line in a, b.
  unfold Coloring in c.
  dependent destruction c.
  dependent destruction a.
  dependent destruction b.
  cbn in H.

  unfold generates in H.
  dependent destruction H.
  unfold generates.
  apply set_union_elim in H; destruct H.

  left.
  apply Vector.Forall2_cons. assumption.
  induction c.
  dependent destruction a; apply Vector.Forall2_nil.
  dependent destruction H0.

  dependent destruction a.
  dependent destruction b.
  dependent destruction x.
  eauto using Vector.Forall2_cons, set_inter_elim1.

  right.
  apply Vector.Forall2_cons. assumption.
  induction c.
  dependent destruction b; apply Vector.Forall2_nil.
  dependent destruction H0.

  dependent destruction a.
  dependent destruction b.
  dependent destruction x.
  eauto using Vector.Forall2_cons, set_inter_elim2.
Qed.
