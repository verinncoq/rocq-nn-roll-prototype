From Coq Require Import Reals Lia Lra QArith.
From Verinncoq Require Import real_subsets.

Open Scope R_scope.

Section IntegersRSOPM.

Lemma Z_ax_zero_is_zero:
    IZR 0%Z = 0.
Proof.
    reflexivity.
Qed.

Lemma Z_ax_one_is_one:
    IZR 1%Z = 1.
Proof.
    reflexivity.
Qed.

Lemma Z_ax_real_leq_true: 
    forall x y,
        Z.leb x y = true <-> Rle (IZR x) (IZR y).
Proof.
    intros x y.
    split; intros H.
    * apply Zle_bool_imp_le in H.
      apply IZR_le; exact H.
    * apply Zle_imp_le_bool.
      apply le_IZR; exact H.
Qed.  

Lemma Z_ax_real_equals_false: 
    forall x y,
        Z.leb x y = false <-> Rlt (IZR y) (IZR x).
Proof.
    intros x y.
    split; intros H.
    * apply IZR_lt.
      apply Z.leb_gt; exact H.
    * apply Z.leb_gt.
      apply lt_IZR; exact H.
Qed.
    
Canonical Z_RSOPM : RealSubsetOPM := BuildRSOPM 
    Z IZR 0%Z 1%Z Z.opp Z.leb Z.add Z.mul eq_IZR 
    Z_ax_zero_is_zero 
    Z_ax_one_is_one
    opp_IZR
    Z_ax_real_leq_true
    Z_ax_real_equals_false
    plus_IZR
    mult_IZR.

End IntegersRSOPM.

Section RationalRSOPM.

(* 
    QDEP - dependent Q
        Like Q, but always reduced. Enables syntactic equality and 
        relies on excluded middle axiom.
*)
Definition QDEP := { q : Q | Qred q = q}.

Definition QDEP2Q (qdep: QDEP) := proj1_sig qdep.
Coercion QDEP2Q : QDEP >-> Q.

Lemma QDEP_Q_syntactic_equality:
    forall (qd1 qd2: QDEP),
        qd1 == qd2 -> QDEP2Q qd1 = QDEP2Q qd2.
Proof.
    intros qd1 qd2 H.
    destruct qd1 as [[n1 d1] P1].
    destruct qd2 as [[n2 d2] P2].
    simpl; simpl in H.
    rewrite <- P1.
    rewrite <- P2.
    apply Qred_eq_iff.
    apply H.
Qed.

(* Here we use proof irrelevance, which relies on excluded middle axiom P \/ ~P
   TODO: eliminate the excluded middle *)
Theorem QDEP_syntactic_equality: 
    forall (qd1 qd2: QDEP),
        qd1 == qd2 -> qd1 = qd2.
Proof.
    intros qd1 qd2 H.
    pose proof (QDEP_Q_syntactic_equality qd1 qd2 H) as Hqeq.
    destruct qd1 as [q1 P1].
    destruct qd2 as [q2 P2].
    simpl in Hqeq; simpl in H.
    generalize P1; generalize P2.
    rewrite Hqeq.
    intros P11 P22. 
    rewrite (Classical_Prop.proof_irrelevance _ P11 P22). (*!!!*)
    reflexivity.
Qed.

Definition toQDEP_impl (q: Q) : Q :=
    Qred q.

Lemma toQDEP_reduced:
    forall q, Qred (toQDEP_impl q) = (toQDEP_impl q).
Proof.
    intro q.
    unfold toQDEP_impl.
    apply Qred_eq_iff.
    apply Qred_correct.
Qed.

Definition toQDEP (q : Q) : QDEP :=
    exist _ (toQDEP_impl q) (toQDEP_reduced q).

(* Zero *)

Definition QDEP_zero_impl : Q := 0 # 1.

Lemma QDEP_zero_reduced:
    Qred QDEP_zero_impl = QDEP_zero_impl.
Proof.
    compute; reflexivity.
Qed.

Definition QDEP_zero: QDEP 
    := exist _ QDEP_zero_impl QDEP_zero_reduced.

(* One *)

Definition QDEP_one_impl: Q := 1 # 1.

Lemma QDEP_one_reduced:
    Qred QDEP_one_impl = QDEP_one_impl.
Proof.
    compute; reflexivity.
Qed.

Definition QDEP_one: QDEP := 
    exist _ QDEP_one_impl QDEP_one_reduced.

(* Opposite *)

Definition QDEP_opp (q: QDEP): QDEP := 
    toQDEP (Qopp q).

(* Less than or equal *)

Definition QDEP_le (q1 q2: QDEP): bool :=
    Qle_bool q1 q2.

(* Plus *)

Definition QDEP_plus (q1 q2: QDEP): QDEP :=
    toQDEP (Qplus q1 q2).

(* Multiplication *)

Definition QDEP_mult (q1 q2: QDEP): QDEP :=
    toQDEP (Qmult q1 q2).

(* Axioms *)

Lemma QDEP_ax_equality: 
    forall (x y: QDEP),
        Q2R x = Q2R y -> x = y.
Proof.
    intros x y H.
    destruct x as [x Px].
    destruct y as [y Py].
    apply Qreals.eqR_Qeq in H; simpl in H.
    apply QDEP_syntactic_equality; simpl.
    rewrite <- Px; rewrite <- Py.
    apply Qred_comp; apply H.
Qed.

Lemma QDEP_ax_zero_is_zero:
    Q2R QDEP_zero = 0%R.
Proof.
    compute; lra.
Qed.

Lemma QDEP_ax_one_is_one:
    Q2R QDEP_one = 1%R.
Proof.
    compute; lra.
Qed.

Lemma QDEP_ax_opp_is_opp: 
    forall x,
        Q2R (QDEP_opp x) = Ropp (Q2R x).
Proof.
    intros x.
    destruct x as [x Px].
    unfold QDEP_opp, toQDEP, toQDEP_impl, QDEP2Q, proj1_sig.
    rewrite Qred_opp.
    rewrite Px.
    apply Qreals.Q2R_opp.
Qed.

Lemma QDEP_ax_real_leq_true: 
    forall x y,
        QDEP_le x y = true <-> Rle (Q2R x) (Q2R y).
Proof.
    intros x y.
    destruct x as [x Px].
    destruct y as [y Py].
    unfold QDEP_le, QDEP2Q, proj1_sig.
    split; intro H.
    - apply Qle_bool_imp_le in H.
      apply Qreals.Qle_Rle.
      apply H.
    - apply Qle_bool_iff.
      apply Qreals.Rle_Qle.
      apply H.
Qed.

Lemma QDEP_ax_real_leq_false: 
    forall x y,
        QDEP_le x y = false <-> Rlt (Q2R y) (Q2R x).
Proof.
    intros x y.
    destruct x as [x Px].
    destruct y as [y Py].
    unfold QDEP_le, QDEP2Q, proj1_sig.
    split; intro H.
    - destruct (Rlt_dec (Q2R y) (Q2R x)) as [Hlt|Hge].
      * apply Hlt. 
      * apply not_Rlt in Hge.
        apply Rge_le in Hge.
        apply Qreals.Rle_Qle in Hge.
        apply Qle_bool_iff in Hge.
        rewrite H in Hge.
        inversion Hge.
    - destruct (Qle_bool x y) eqn:Hle.
      * rewrite Qle_bool_iff in Hle.
        apply Qreals.Rlt_Qlt in H.
        Lqa.lra.
      * reflexivity.
Qed.

Lemma QDEP_ax_real_plus: 
    forall x y,
        Q2R (QDEP_plus x y) = Rplus (Q2R x) (Q2R y).
Proof.
    intros x y.
    rewrite <- Qreals.Q2R_plus.
    destruct x as [x Px].
    destruct y as [y Py].
    unfold QDEP_plus, toQDEP, toQDEP_impl, QDEP2Q, proj1_sig.
    rewrite (Qreals.Qeq_eqR (Qred (x + y)) (x + y)); first reflexivity.
    rewrite Qred_correct.
    apply Qeq_refl.
Qed.

Lemma QDEP_ax_real_mult: 
    forall x y,
        Q2R (QDEP_mult x y) = Rmult (Q2R x) (Q2R y).
Proof.
    intros x y.
    rewrite <- Qreals.Q2R_mult.
    destruct x as [x Px].
    destruct y as [y Py].
    unfold QDEP_mult, toQDEP, toQDEP_impl, QDEP2Q, proj1_sig.
    rewrite (Qreals.Qeq_eqR (Qred (x * y)) (x * y)); first reflexivity.
    rewrite Qred_correct.
    apply Qeq_refl.
Qed. 
    
Definition QDEP_RSOPM : RealSubsetOPM := BuildRSOPM
    QDEP Q2R QDEP_zero QDEP_one QDEP_opp QDEP_le QDEP_plus QDEP_mult
    QDEP_ax_equality QDEP_ax_zero_is_zero QDEP_ax_one_is_one
    QDEP_ax_opp_is_opp QDEP_ax_real_leq_true QDEP_ax_real_leq_false
    QDEP_ax_real_plus QDEP_ax_real_mult.

End RationalRSOPM.
