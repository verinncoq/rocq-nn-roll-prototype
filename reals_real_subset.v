From Coq Require Import Reals Lra.
From Verinncoq Require Import real_subsets.

Open Scope R_scope.

Section RealsRSOPM.

(* Reals are in separate file, because using them as a subset instance
   can alter results of RSOPM_* tactics  *)

Definition Rid (r: R) := r.

Definition Rle_bool (r1 r2: R) := 
    match Rle_dec r1 r2 with
    | left _ => true 
    | right _ => false
    end.

Lemma R_ax_equality: 
    forall x y,
        Rid x = Rid y -> x = y.
Proof.
    intros x y H.
    unfold Rid in H; exact H.
Qed.

Lemma R_ax_zero_is_zero:
    Rid 0 = 0.
Proof.
  reflexivity.
Qed.

Lemma R_ax_one_is_one:
    Rid 1 = 1.
Proof.
  reflexivity.
Qed.


Lemma R_ax_opp_is_opp:
    forall x,
        Rid (- x) = - Rid x.
Proof.
    reflexivity.
Qed.

Lemma R_ax_real_equals_true: 
    forall x y,
        Rle_bool x y = true <-> Rle (Rid x) (Rid y).
Proof.
    intros x y.
    unfold Rle_bool; unfold Rid.
    destruct Rle_dec; split; try auto.
    intros H; inversion H.
Qed.

Lemma R_ax_real_equals_false: 
    forall x y,
        Rle_bool x y = false <-> Rlt (Rid y) (Rid x).
Proof.
    intros x y.
    unfold Rle_bool; unfold Rid.
    destruct Rle_dec; split; lra.
Qed.

Lemma R_ax_real_plus: 
    forall x y,
        Rid (Rplus x y) = Rplus (Rid x) (Rid y).
Proof.
    intros x y.
    unfold Rid.
    reflexivity.
Qed.

Lemma R_ax_real_mult: 
    forall x y,
        Rid (Rmult x y) = Rmult (Rid x) (Rid y).
Proof.
    intros x y.
    unfold Rid.
    reflexivity.
Qed.

Canonical R_RSOPM : RealSubsetOPM := BuildRSOPM
    R Rid 0 1 Ropp Rle_bool Rplus Rmult
    R_ax_equality
    R_ax_zero_is_zero
    R_ax_one_is_one
    R_ax_opp_is_opp
    R_ax_real_equals_true
    R_ax_real_equals_false
    R_ax_real_plus
    R_ax_real_mult.

End RealsRSOPM.