From Coq Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

Section RealSubsetsTypes.

(* Real Subset - Order, Addition and Multiplication *)
Record RealSubsetOAM := BuildRSOAM {
    T: Type;
    INJ_RSOAM: T -> R;
    RSOAM_zero: T;
    RSOAM_one: T;
    RSOAM_opp: T -> T;
    RSOAM_le: T -> T -> bool;
    RSOAM_plus: T -> T -> T;
    RSOAM_mult: T -> T -> T;
    ax_equality: forall x y,
        INJ_RSOAM x = INJ_RSOAM y -> x = y;
    ax_zero_is_zero:
        INJ_RSOAM RSOAM_zero = 0%R;
    ax_one_is_one:
        INJ_RSOAM RSOAM_one = 1%R;
    ax_opp_is_opp: forall x,
        INJ_RSOAM (RSOAM_opp x) = Ropp (INJ_RSOAM x); 
    ax_real_leq_true: forall x y,
        RSOAM_le x y = true <-> Rle (INJ_RSOAM x) (INJ_RSOAM y);
    ax_real_leq_false: forall x y,
        RSOAM_le x y = false <-> Rlt (INJ_RSOAM y) (INJ_RSOAM x);
    ax_real_plus: forall x y,
        INJ_RSOAM (RSOAM_plus x y) = Rplus (INJ_RSOAM x) (INJ_RSOAM y);
    ax_real_mult: forall x y,
        INJ_RSOAM (RSOAM_mult x y) = Rmult (INJ_RSOAM x) (INJ_RSOAM y) 
}.

End RealSubsetsTypes.

Section RealSubsetExtensions.

Context {RSOAM: RealSubsetOAM}.

Definition RSeq (x y: (T RSOAM)) :=
    match RSOAM_le RSOAM x y, RSOAM_le RSOAM y x with
    | true, true => true
    | _, _ => false
    end.

Definition RSlt (x y: (T RSOAM)) :=
    match RSOAM_le RSOAM x y, RSOAM_le RSOAM y x with
    | true, false => true
    | _, _ => false
    end.

Definition RSge (x y: (T RSOAM)) :=
    RSOAM_le RSOAM y x.

Definition RSgt (x y: (T RSOAM)) :=
    RSlt y x.
    
End RealSubsetExtensions.


Module RealSubsetNotations.
    
Declare Scope RSOAM_scope.
Delimit Scope RSOAM_scope with RS. 

Definition RS {RSOAM: RealSubsetOAM} := T RSOAM.

Definition RSzero {RSOAM: RealSubsetOAM} := RSOAM_zero RSOAM.
Notation "0" := RSzero: RSOAM_scope.

Definition RSone {RSOAM: RealSubsetOAM} := RSOAM_one RSOAM.
Notation "1" := RSone: RSOAM_scope.

Definition RSopp {RSOAM: RealSubsetOAM} := RSOAM_opp RSOAM.
Notation "- x" := (RSopp x) : RSOAM_scope.

Definition RSle {RSOAM: RealSubsetOAM} := RSOAM_le RSOAM.
Infix "<=" := RSle : RSOAM_scope.

Infix "<" := RSlt : RSOAM_scope.
Infix ">=" := RSge : RSOAM_scope.
Infix ">" := RSgt : RSOAM_scope.
Infix "==" := RSeq (at level 70, no associativity): RSOAM_scope.

Definition RSplus {RSOAM: RealSubsetOAM} := RSOAM_plus RSOAM.
Infix "+" := RSplus : RSOAM_scope.

Definition RSmult {RSOAM: RealSubsetOAM} := RSOAM_mult RSOAM.
Infix "*" := RSmult : RSOAM_scope.

End RealSubsetNotations.

Import RealSubsetNotations.
Open Scope RSOAM_scope.

Ltac RSOAM_realize :=
    repeat (
        rewrite ax_zero_is_zero ||
        rewrite ax_one_is_one ||
        rewrite ax_real_plus ||
        rewrite ax_opp_is_opp ||
        rewrite ax_real_mult
    ).

Ltac RSOAM_realize_eq :=
    repeat intro;
    apply ax_equality;
    RSOAM_realize.

Ltac RSOAM_solve :=
    RSOAM_realize_eq; lra.

Section SubsetsLemmas.

Context {RSOAM: RealSubsetOAM}.

Lemma RSOAM_plus_comm:
    forall (x y: T RSOAM),
        x + y = y + x.
Proof.
    intros x y. apply ax_equality.
    RSOAM_realize; apply Rplus_comm.
Qed.

Lemma RSOAM_plus_assoc:
    forall (x y z: T RSOAM),
        x + (y + z) = (x + y) + z.
Proof.
    intros x y z. apply ax_equality.
    RSOAM_realize; symmetry; apply Rplus_assoc.
Qed.

Lemma RSOAM_plus_0_r:
    forall (x : T RSOAM),
        x + 0 = x.
Proof.
    intros x. apply ax_equality.
    RSOAM_realize; apply Rplus_0_r.
Qed.

Lemma RSOAM_plus_opp:
    forall (x: T RSOAM),
        x + - x = 0.
Proof.
    intros x. apply ax_equality.
    RSOAM_realize.
    apply Rplus_opp_r.
Qed.

Lemma RSOAM_mult_assoc:
    forall (x y z: T RSOAM),
        x * (y * z) = (x * y) * z.
Proof.
    intros x y z. apply ax_equality.
    RSOAM_realize.
    symmetry.
    apply Rmult_assoc.
Qed.

Lemma RSOAM_mult_one_r:
    forall (x: T RSOAM),
        x * 1 = x.
Proof.
    intros x. apply ax_equality.
    RSOAM_realize.
    apply Rmult_1_r.
Qed.

Lemma RSOAM_mult_one_l:
    forall (x: T RSOAM),
        1 * x = x.
Proof.
    intros x. apply ax_equality.
    RSOAM_realize.
    apply Rmult_1_l.
Qed.

Lemma RSOAM_mult_plus_distr_r:
    forall (x y z: T RSOAM),
        (x + y) * z = (x * z) + (y * z).
Proof.
    intros x y z. apply ax_equality.
    RSOAM_realize.
    apply Rmult_plus_distr_r.
Qed.

Lemma RSOAM_mult_plus_distr_l:
    forall (x y z: T RSOAM),
        x * (y + z) = (x * y) + (x * z).
Proof.
    intros x y z. apply ax_equality.
    RSOAM_realize.
    apply Rmult_plus_distr_l.
Qed.

End SubsetsLemmas.

Section SubsetsInHierarchy.

(* RSOAM is always an abelian monoid *)

Definition RSOAM_AbelianMonoid_Mixin (RSOAM: RealSubsetOAM)
    : AbelianMonoid.class_of (T RSOAM) :=
    AbelianMonoid.Mixin (T RSOAM) (RSOAM_plus RSOAM) 
        (RSOAM_zero RSOAM) (RSOAM_plus_comm)
        (RSOAM_plus_assoc) (RSOAM_plus_0_r).

Definition RSOAM_AbelianMonoid (RSOAM: RealSubsetOAM): AbelianMonoid :=
    AbelianMonoid.Pack (T RSOAM) (RSOAM_AbelianMonoid_Mixin RSOAM) (T RSOAM).

(* RSOAM is always an abelian group *)

Definition RSOAM_AbelianGroup_Mixin (RSOAM: RealSubsetOAM)
    : AbelianGroup.mixin_of (RSOAM_AbelianMonoid RSOAM) :=
    AbelianGroup.Mixin (RSOAM_AbelianMonoid RSOAM) (RSOAM_opp RSOAM) RSOAM_plus_opp.

Definition RSOAM_AbelianGroup_Class (RSOAM: RealSubsetOAM)
    : AbelianGroup.class_of (T RSOAM) 
    :=
    AbelianGroup.Class (T RSOAM) (RSOAM_AbelianMonoid_Mixin RSOAM) 
        (RSOAM_AbelianGroup_Mixin RSOAM).

Definition RSOAM_AbelianGroup (RSOAM: RealSubsetOAM): AbelianGroup :=
    AbelianGroup.Pack (T RSOAM) (RSOAM_AbelianGroup_Class RSOAM) (T RSOAM).

(* RSOAM is always a ring *)

Definition RSOAM_Ring_Mixin (RSOAM: RealSubsetOAM) 
    : Ring.mixin_of (RSOAM_AbelianGroup RSOAM) 
    :=
    Ring.Mixin (RSOAM_AbelianGroup RSOAM) (RSOAM_mult RSOAM) (RSOAM_one RSOAM)
        RSOAM_mult_assoc RSOAM_mult_one_r RSOAM_mult_one_l
        RSOAM_mult_plus_distr_r RSOAM_mult_plus_distr_l.

Definition RSOAM_Ring_Class (RSOAM: RealSubsetOAM) : Ring.class_of (T RSOAM) :=
    Ring.Class (T RSOAM) (RSOAM_AbelianGroup_Class RSOAM) (RSOAM_Ring_Mixin RSOAM).

Definition RSOAM_Ring (RSOAM: RealSubsetOAM): Ring :=
    Ring.Pack (T RSOAM) (RSOAM_Ring_Class RSOAM) (T RSOAM).

Coercion RSOAM_Ring : RealSubsetOAM >-> Ring.

End SubsetsInHierarchy.

Section RSOAMMiscLemmata.

Context {RSOAM: RealSubsetOAM}.

Lemma RSOAM_le_plus_opp_r:
    forall (x y z: T RSOAM),
      (x + y <= z) = true ->
      x <= z + (- y) = true.
Proof.
    intros x y z H.
    apply ax_real_leq_true.
    RSOAM_realize.
    rewrite <- Rminus_def.
    rewrite Rle_minus_r.
    apply ax_real_leq_true in H.
    rewrite <- ax_real_plus.
    apply H.
Qed.

Lemma RSOAM_le_opp_plus_r:
    forall (x y z: T RSOAM),
        x <= z + (- y) = true ->
        (x + y <= z) = true.
Proof.
    intros x y z H.
    apply ax_real_leq_true.
    RSOAM_realize.
    rewrite <- Rle_minus_r.
    rewrite Rminus_def.
    apply ax_real_leq_true in H.
    rewrite ax_real_plus in H.
    rewrite ax_opp_is_opp in H.
    apply H.
Qed.

End RSOAMMiscLemmata.
