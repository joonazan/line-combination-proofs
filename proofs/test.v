Require Import Coq.Unicode.Utf8_core.
From mathcomp Require Import all_ssreflect all_fingroup.
Require Import line_combination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition a_b : line 3 1 := [tuple set1 ord0; set1 (inord 1)].

Compute (permutations a_b).

Compute (is_maximal_form [:: a_b]).
