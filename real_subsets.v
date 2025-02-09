From Coq Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

Section RealSubsetsTypes.

(* Real Subset - Order, Plus and Multiplication *)
Record RealSubsetOPM := BuildRSOPM {
    T: Type;
    INJ_RSOPM: T -> R;
    RSOPM_zero: T;
    RSOPM_one: T;
    RSOPM_opp: T -> T;
    RSOPM_le: T -> T -> bool;
    RSOPM_plus: T -> T -> T;
    RSOPM_mult: T -> T -> T;
    ax_equality: forall x y,
        INJ_RSOPM x = INJ_RSOPM y -> x = y;
    ax_zero_is_zero:
        INJ_RSOPM RSOPM_zero = 0%R;
    ax_one_is_one:
        INJ_RSOPM RSOPM_one = 1%R;
    ax_opp_is_opp: forall x,
        INJ_RSOPM (RSOPM_opp x) = Ropp (INJ_RSOPM x); 
    ax_real_leq_true: forall x y,
        RSOPM_le x y = true <-> Rle (INJ_RSOPM x) (INJ_RSOPM y);
    ax_real_leq_false: forall x y,
        RSOPM_le x y = false <-> Rlt (INJ_RSOPM y) (INJ_RSOPM x);
    ax_real_plus: forall x y,
        INJ_RSOPM (RSOPM_plus x y) = Rplus (INJ_RSOPM x) (INJ_RSOPM y);
    ax_real_mult: forall x y,
        INJ_RSOPM (RSOPM_mult x y) = Rmult (INJ_RSOPM x) (INJ_RSOPM y) 
}.

End RealSubsetsTypes.

Section RealSubsetExtensions.

Context {RSOPM: RealSubsetOPM}.

Definition RSeq (x y: (T RSOPM)) :=
    match RSOPM_le RSOPM x y, RSOPM_le RSOPM y x with
    | true, true => true
    | _, _ => false
    end.

Definition RSlt (x y: (T RSOPM)) :=
    match RSOPM_le RSOPM x y, RSOPM_le RSOPM y x with
    | true, false => true
    | _, _ => false
    end.

Definition RSge (x y: (T RSOPM)) :=
    RSOPM_le RSOPM y x.

Definition RSgt (x y: (T RSOPM)) :=
    RSlt y x.
    
End RealSubsetExtensions.


Module RealSubsetNotations.
    
Declare Scope RSOPM_scope.
Delimit Scope RSOPM_scope with RS. 

Definition RS {RSOPM: RealSubsetOPM} := T RSOPM.

Definition RSzero {RSOPM: RealSubsetOPM} := RSOPM_zero RSOPM.
Notation "0" := RSzero: RSOPM_scope.

Definition RSone {RSOPM: RealSubsetOPM} := RSOPM_one RSOPM.
Notation "1" := RSone: RSOPM_scope.

Definition RSopp {RSOPM: RealSubsetOPM} := RSOPM_opp RSOPM.
Notation "- x" := (RSopp x) : RSOPM_scope.

Definition RSle {RSOPM: RealSubsetOPM} := RSOPM_le RSOPM.
Infix "<=" := RSle : RSOPM_scope.

Infix "<" := RSlt : RSOPM_scope.
Infix ">=" := RSge : RSOPM_scope.
Infix ">" := RSgt : RSOPM_scope.
Infix "==" := RSeq (at level 70, no associativity): RSOPM_scope.

Definition RSplus {RSOPM: RealSubsetOPM} := RSOPM_plus RSOPM.
Infix "+" := RSplus : RSOPM_scope.

Definition RSmult {RSOPM: RealSubsetOPM} := RSOPM_mult RSOPM.
Infix "*" := RSmult : RSOPM_scope.

End RealSubsetNotations.

Import RealSubsetNotations.
Open Scope RSOPM_scope.

Ltac RSOPM_realize :=
    repeat (
        rewrite ax_zero_is_zero ||
        rewrite ax_one_is_one ||
        rewrite ax_real_plus ||
        rewrite ax_opp_is_opp ||
        rewrite ax_real_mult
    ).

Ltac RSOPM_realize_eq :=
    repeat intro;
    apply ax_equality;
    RSOPM_realize.

Ltac RSOPM_solve :=
    RSOPM_realize_eq; lra.

Section SubsetsLemmas.

Context {RSOPM: RealSubsetOPM}.

Lemma RSOPM_plus_comm:
    forall (x y: T RSOPM),
        x + y = y + x.
Proof.
    intros x y. apply ax_equality.
    RSOPM_realize; apply Rplus_comm.
Qed.

Lemma RSOPM_plus_assoc:
    forall (x y z: T RSOPM),
        x + (y + z) = (x + y) + z.
Proof.
    intros x y z. apply ax_equality.
    RSOPM_realize; symmetry; apply Rplus_assoc.
Qed.

Lemma RSOPM_plus_0_r:
    forall (x : T RSOPM),
        x + 0 = x.
Proof.
    intros x. apply ax_equality.
    RSOPM_realize; apply Rplus_0_r.
Qed.

Lemma RSOPM_plus_opp:
    forall (x: T RSOPM),
        x + - x = 0.
Proof.
    intros x. apply ax_equality.
    RSOPM_realize.
    apply Rplus_opp_r.
Qed.

Lemma RSOPM_mult_assoc:
    forall (x y z: T RSOPM),
        x * (y * z) = (x * y) * z.
Proof.
    intros x y z. apply ax_equality.
    RSOPM_realize.
    symmetry.
    apply Rmult_assoc.
Qed.

Lemma RSOPM_mult_one_r:
    forall (x: T RSOPM),
        x * 1 = x.
Proof.
    intros x. apply ax_equality.
    RSOPM_realize.
    apply Rmult_1_r.
Qed.

Lemma RSOPM_mult_one_l:
    forall (x: T RSOPM),
        1 * x = x.
Proof.
    intros x. apply ax_equality.
    RSOPM_realize.
    apply Rmult_1_l.
Qed.

Lemma RSOPM_mult_plus_distr_r:
    forall (x y z: T RSOPM),
        (x + y) * z = (x * z) + (y * z).
Proof.
    intros x y z. apply ax_equality.
    RSOPM_realize.
    apply Rmult_plus_distr_r.
Qed.

Lemma RSOPM_mult_plus_distr_l:
    forall (x y z: T RSOPM),
        x * (y + z) = (x * y) + (x * z).
Proof.
    intros x y z. apply ax_equality.
    RSOPM_realize.
    apply Rmult_plus_distr_l.
Qed.

End SubsetsLemmas.

Section SubsetsInHierarchy.

(* RSOPM is always an abelian monoid *)

Definition RSOPM_AbelianMonoid_Mixin (RSOPM: RealSubsetOPM)
    : AbelianMonoid.class_of (T RSOPM) :=
    AbelianMonoid.Mixin (T RSOPM) (RSOPM_plus RSOPM) 
        (RSOPM_zero RSOPM) (RSOPM_plus_comm)
        (RSOPM_plus_assoc) (RSOPM_plus_0_r).

Definition RSOPM_AbelianMonoid (RSOPM: RealSubsetOPM): AbelianMonoid :=
    AbelianMonoid.Pack (T RSOPM) (RSOPM_AbelianMonoid_Mixin RSOPM) (T RSOPM).

(* RSOPM is always an abelian group *)

Definition RSOPM_AbelianGroup_Mixin (RSOPM: RealSubsetOPM)
    : AbelianGroup.mixin_of (RSOPM_AbelianMonoid RSOPM) :=
    AbelianGroup.Mixin (RSOPM_AbelianMonoid RSOPM) (RSOPM_opp RSOPM) RSOPM_plus_opp.

Definition RSOPM_AbelianGroup_Class (RSOPM: RealSubsetOPM)
    : AbelianGroup.class_of (T RSOPM) 
    :=
    AbelianGroup.Class (T RSOPM) (RSOPM_AbelianMonoid_Mixin RSOPM) 
        (RSOPM_AbelianGroup_Mixin RSOPM).

Definition RSOPM_AbelianGroup (RSOPM: RealSubsetOPM): AbelianGroup :=
    AbelianGroup.Pack (T RSOPM) (RSOPM_AbelianGroup_Class RSOPM) (T RSOPM).

(* RSOPM is always a ring *)

Definition RSOPM_Ring_Mixin (RSOPM: RealSubsetOPM) 
    : Ring.mixin_of (RSOPM_AbelianGroup RSOPM) 
    :=
    Ring.Mixin (RSOPM_AbelianGroup RSOPM) (RSOPM_mult RSOPM) (RSOPM_one RSOPM)
        RSOPM_mult_assoc RSOPM_mult_one_r RSOPM_mult_one_l
        RSOPM_mult_plus_distr_r RSOPM_mult_plus_distr_l.

Definition RSOPM_Ring_Class (RSOPM: RealSubsetOPM) : Ring.class_of (T RSOPM) :=
    Ring.Class (T RSOPM) (RSOPM_AbelianGroup_Class RSOPM) (RSOPM_Ring_Mixin RSOPM).

Definition RSOPM_Ring (RSOPM: RealSubsetOPM): Ring :=
    Ring.Pack (T RSOPM) (RSOPM_Ring_Class RSOPM) (T RSOPM).

Coercion RSOPM_Ring : RealSubsetOPM >-> Ring.

End SubsetsInHierarchy.

Section RSOPMMiscLemmata.

Context {RSOPM: RealSubsetOPM}.

Lemma RSOPM_le_plus_opp_r:
    forall (x y z: T RSOPM),
      (x + y <= z) = true ->
      x <= z + (- y) = true.
Proof.
    intros x y z H.
    apply ax_real_leq_true.
    RSOPM_realize.
    rewrite <- Rminus_def.
    rewrite Rle_minus_r.
    apply ax_real_leq_true in H.
    rewrite <- ax_real_plus.
    apply H.
Qed.

Lemma RSOPM_le_opp_plus_r:
    forall (x y z: T RSOPM),
        x <= z + (- y) = true ->
        (x + y <= z) = true.
Proof.
    intros x y z H.
    apply ax_real_leq_true.
    RSOPM_realize.
    rewrite <- Rle_minus_r.
    rewrite Rminus_def.
    apply ax_real_leq_true in H.
    rewrite ax_real_plus in H.
    rewrite ax_opp_is_opp in H.
    apply H.
Qed.

End RSOPMMiscLemmata.
