From Coq Require Import List Reals Lra Lia.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import real_subsets matrix_extensions piecewise_affine pwaf_operations.

Import ListNotations.
Import MatrixNotations.

Open Scope list_scope.
Open Scope scalar_scope.

Section LinearPiecewise.

Context { RSOPM : RealSubsetOPM }.

Definition full_R_polyhedron (n: nat) := Polyhedron (RSOPM:=RSOPM) n nil.

Definition linear_body {n m: nat} (M: matrix (T:=RSOPM) m n) (b: colvec (RSOPM:=RSOPM) m): list _ :=
    cons (Segment _ _ (full_R_polyhedron n) (Affine _ _ M b)) nil.

Lemma linear_univalence {n m: nat} (M: matrix m n) (b: colvec m):
    pwaf_univalence (linear_body M b).
Proof.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b0 Ha Hb0 x Hintersect.
    destruct Ha. destruct Hb0.
    rewrite <- H. rewrite <- H0.
    reflexivity.
    contradiction H0. contradiction H.
Qed.

Definition LinearPWAF {in_dim out_dim: nat} (M: matrix out_dim in_dim) (b: colvec out_dim) := 
    mkPLF in_dim out_dim (linear_body M b) (linear_univalence M b).

Lemma linear_is_total {n m: nat} (M: matrix m n) (b: colvec m):
    is_total (LinearPWAF M b).
Proof.
    unfold is_total.
    intros x.
    unfold in_pwaf_domain.
    exists (Segment _ _ (full_R_polyhedron n) (Affine _ _ M b)).
    split.
    - simpl. left. reflexivity.
    - unfold full_R_polyhedron.
      simpl. contradiction.
Qed.

Definition LinearTPWAF {in_dim out_dim: nat} (M: matrix out_dim in_dim) (b: colvec out_dim): TPWAF := 
    exist _ (LinearPWAF M b) (linear_is_total M b).

End LinearPiecewise.

Section OutputPiecewise.

Context { RSOPM : RealSubsetOPM }.

Definition OutputTPWAF {in_dim out_dim: nat} : TPWAF :=
    LinearTPWAF (RSOPM:=RSOPM) (mk_matrix out_dim in_dim Mone_seq) (null_vector out_dim).

End OutputPiecewise.

Section ZeroDimFunc.

(* Helper PWAF of zeroth dimension *)

Context { RSOPM : RealSubsetOPM }.

Definition ZeroDim_polyhedron
    := Polyhedron (RSOPM:=RSOPM) 0 nil.

Theorem ZeroDim_polyhedron_full: 
    forall (x : colvec 0), in_convex_polyhedron x ZeroDim_polyhedron.
Proof.
   intros x.
   unfold in_convex_polyhedron.
   unfold ZeroDim_polyhedron.
   intros constraint HIn.
   contradiction HIn.
Qed.

Definition ZeroDim_body := 
    [Segment 0 0 ZeroDim_polyhedron (Affine 0 0 (Mone (T:=RSOPM) (n:=0)) (null_vector 0))].

Theorem ZeroDim_univalence: 
    pwaf_univalence ZeroDim_body.
Proof.
   unfold pwaf_univalence.
   unfold ZeroDim_body.
   unfold ForallPairs.
   intros a b HaIn HbIn x HInboth.
   destruct HaIn; try contradiction.
   destruct HbIn; try contradiction.
   rewrite <- H. rewrite <- H0.
   simpl. reflexivity.
Qed.

Definition ZeroDimPWAF := mkPLF 0 0 ZeroDim_body ZeroDim_univalence.

Lemma ZeroDimPWAF_total:
    is_total ZeroDimPWAF.
Proof.
    unfold is_total.
    intro x.
    unfold in_pwaf_domain.
    eexists.
    split.
    * unfold ZeroDimPWAF; simpl.
      left. reflexivity.
    * unfold in_affine_segment_domain.
      apply ZeroDim_polyhedron_full.
Qed.

Definition ZeroDimTPWAF := exist _ ZeroDimPWAF ZeroDimPWAF_total.

End ZeroDimFunc.

Section ReLUPiecewise.

Context { RSOPM : RealSubsetOPM }.
Import RealSubsetNotations.
Local Open Scope RSOPM_scope.

Definition ReLU1d_polyhedra_left 
    := Polyhedron 1 [Constraint 1 (Mone (T:=RSOPM)) 0].
Definition ReLU1d_polyhedra_right 
    := Polyhedron 1 [Constraint 1 ((RSopp 1) * (Mone (T:=RSOPM)))%scalar 0].

Lemma RelU1d_polyhedra_intersect:
    forall x, 
        in_convex_polyhedron x ReLU1d_polyhedra_left /\ 
        in_convex_polyhedron x ReLU1d_polyhedra_right ->
        dot (Mone (T:=RSOPM)) x = 0.
Proof.
    intros x Hintersect.
    unfold in_convex_polyhedron in Hintersect.
    destruct Hintersect.
    specialize (H (Constraint 1 (Mone (T:=RSOPM)) 0)). simpl in H. 
    specialize (H0 (Constraint 1 (scalar_mult (RSopp 1) (Mone (T:=RSOPM))) 0)). simpl in H0.
    apply ax_equality.
    apply Rle_antisym.
    - rewrite <- ax_real_leq_true. apply H. auto.
    - rewrite <- Ropp_involutive.
      rewrite ax_zero_is_zero.
      rewrite <- Ropp_0.
      apply Ropp_ge_le_contravar.
      apply Rle_ge.
      rewrite ax_real_leq_true in H0. 
      apply Ropp_le_ge_contravar in H0. 
      rewrite dot_scalar_mult in H0.
      rewrite ax_real_mult in H0.
      rewrite ax_opp_is_opp in H0.
      rewrite ax_one_is_one in H0.
      rewrite ax_zero_is_zero in H0.
      lra. 
      left. reflexivity.
Qed.  

Lemma x_is_0:
    forall (x: colvec (RSOPM:=RSOPM) 1),
        dot (Mone (T:=RSOPM)) x = 0 -> x = null_vector 1.
Proof.
    intros x Hdot.
    unfold null_vector.
    unfold mk_colvec.
    rewrite <- (mk_matrix_bij 0 x).
    unfold dot in Hdot.
    apply mk_matrix_ext.
    intros i j Hi Hj.
    induction i. induction j.
    - rewrite <- Hdot at 2.
      unfold Mmult.
      rewrite coeff_mat_bij; try lia.
      compute. rewrite (RSOPM_mult_one_l (RSOPM:=RSOPM)). rewrite (RSOPM_plus_0_r (RSOPM:=RSOPM)).
      reflexivity.
    induction j.
    all: lia.
Qed.

Lemma RelU1d_polyhedra_intersect_0:
    forall x, 
        in_convex_polyhedron x ReLU1d_polyhedra_left /\ 
        in_convex_polyhedron x ReLU1d_polyhedra_right ->
        x = null_vector 1.
Proof.
    intros x Hintersect.
    apply x_is_0.
    apply RelU1d_polyhedra_intersect.
    apply Hintersect.
Qed.

Definition ReLU1d_body: list (AffineSegment 1 1) 
    := [Segment 1 1 ReLU1d_polyhedra_left (Affine 1 1 (Mzero (G:=RSOPM)) (null_vector 1));
        Segment 1 1 ReLU1d_polyhedra_right (Affine 1 1 (Mone (T:=RSOPM)) (null_vector 1))].

Definition ReLU1d_pwaf_univalence:
    pwaf_univalence ReLU1d_body.
Proof.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b HaIn HbIn x Hintersect.
    unfold In in HaIn. simpl in HaIn.
    unfold In in HbIn. simpl in HbIn.
    do 2 (try destruct HaIn as [HaIn|HaIn]); try contradiction;
    do 2 (try destruct HbIn as [HbIn|HbIn]); try contradiction.
    - all: try (rewrite <- HaIn; rewrite <- HbIn; reflexivity).
    - all:
        (
            rewrite <- HaIn; rewrite <- HbIn;
            rewrite <- HaIn in Hintersect; rewrite <- HbIn in Hintersect;
            pose proof (RelU1d_polyhedra_intersect_0 x) as Hxzero;
            (rewrite Hxzero; try (split; apply Hintersect)); simpl;
            do 2 (rewrite dot_comm; rewrite dot_null_vector);
            do 2 rewrite Mplus_null_vector;
            do 2 rewrite Mmult_null_vector;
            reflexivity
        ).
Qed.
      
Definition ReLU1dPWAF := mkPLF 1 1 ReLU1d_body ReLU1d_pwaf_univalence.

Lemma ReLU1d_full_R_split:
    forall x,
        in_convex_polyhedron x ReLU1d_polyhedra_left \/ 
        in_convex_polyhedron x ReLU1d_polyhedra_right.
Proof.
    intros x.
    unfold in_convex_polyhedron.
    unfold ReLU1d_polyhedra_left; unfold ReLU1d_polyhedra_right.
    remember (dot (Mone (T:=RSOPM)) x <= 0) as comp_result.
    destruct comp_result.
    * left.
      intros constraint Hconstraint.
      destruct Hconstraint as [H|H]; try contradiction.
      rewrite <- H.
      unfold satisfies_lc.
      symmetry; apply Heqcomp_result.
    * right.
      symmetry in Heqcomp_result.
      apply ax_real_leq_false in Heqcomp_result.
      intros constraint Hconstraint.
      destruct Hconstraint as [H|H]; try contradiction.
      rewrite <- H.
      unfold satisfies_lc.
      apply ax_real_leq_true.
      rewrite ax_zero_is_zero.
      rewrite dot_scalar_mult.
      rewrite ax_real_mult.
      rewrite ax_opp_is_opp.
      rewrite ax_one_is_one.
      rewrite ax_zero_is_zero in Heqcomp_result.
      lra.
Qed.

Theorem ReLU1dPWAF_total:
    is_total ReLU1dPWAF.
Proof.
    unfold is_total.
    unfold in_pwaf_domain.
    intros x.
    pose proof (ReLU1d_full_R_split x).
    destruct H.
    - eexists. split.
      * simpl. left. reflexivity.
      * simpl.
        intros constraint Hconstraint.
        destruct Hconstraint; try contradiction.
        rewrite <- H0. apply H.
        unfold In. left; reflexivity.
    - eexists. split.
      * simpl. right. left. reflexivity.
      * simpl.
        intros constraint Hconstraint.
        destruct Hconstraint; try contradiction.
        rewrite <- H0. apply H.
        unfold In. left; reflexivity.
Qed.

Definition ReLU1dTPWAF: TPWAF := 
    exist _ ReLU1dPWAF ReLU1dPWAF_total. 

Fixpoint ReLU_TPWAF_helper (in_dim: nat): TPWAF :=
    match in_dim with
    | 0 => ZeroDimTPWAF
    | S n => tpwaf_concat ReLU1dTPWAF (ReLU_TPWAF_helper n)
    end.

Definition ReLU_TPWAF {in_dim out_dim: nat}: TPWAF (out_dim:=out_dim) :=
    tpwaf_compose OutputTPWAF (ReLU_TPWAF_helper in_dim).

End ReLUPiecewise.
