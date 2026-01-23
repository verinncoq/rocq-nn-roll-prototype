From Coq Require Import List QArith Reals Lia Lqa Lra.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import matrix_extensions neuron_functions real_subsets 
                              real_subsets_instances piecewise_affine
                              NNDH neural_networks NNDH_to_fme fourier_motzkin fm_q_support.

Open Scope RSOAM_scope.
Import RealSubsetNotations.

Section Monotonicity1DHyperpropery.

Definition is_monotone_1d (nn: TPWANNSequential (RSOAM:=Q_RSOAMD)): Prop :=
    forall x1 x2,
        toRS x1 <= toRS x2 = true -> toRS (nn_eval nn x1) <= toRS (nn_eval nn x2) = true.

Definition W_monotonicity_1d: ConvexPolyhedron 2 :=
    Polyhedron (RSOAM:=Q_RSOAMD) 2 (cons (Constraint 2 [[1], [- (1)]] 0) nil).

Lemma W_monotonicity_1d_correct:
    forall x1 x2,
       toRS x1 <= toRS x2 = true <-> in_convex_polyhedron (colvec_concat x1 x2) W_monotonicity_1d.
Proof.
    intros x1 x2; split; intro H.
    * unfold in_convex_polyhedron, W_monotonicity_1d.
      intros constraint Hconstraint.
      unfold In in Hconstraint.
      destruct Hconstraint as [Hconstraint|Hconstraint]; try contradiction Hconstraint.
      rewrite <- Hconstraint.
      unfold satisfies_lc.
      unfold dot, Mmult; rewrite coeff_mat_bij; try lia.
      unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
      unfold transpose, colvec_concat, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec.
      repeat (rewrite coeff_mat_bij; try lia); simpl.
      unfold coeff_colvec, coeff_mat, coeff_Tn, fst; simpl.
      rewrite (mult_one_l (K:=Q_RSOAMD)), (plus_zero_l (G:=Q_RSOAMD)), (plus_zero_r (G:=Q_RSOAMD)).
      rewrite (plus_zero_r (G:=Q_RSOAMD)), <- (opp_mult_m1 (K:=Q_RSOAMD)).
      rewrite (ax_real_leq_true Q_RSOAMD) in H.
      apply Rle_minus in H; unfold Rminus in H.
      rewrite <- (ax_opp_is_opp Q_RSOAMD), <- (ax_real_plus Q_RSOAMD), <- (ax_zero_is_zero Q_RSOAMD) in H.
      rewrite <- (ax_real_leq_true Q_RSOAMD) in H.
      apply H.
    * unfold in_convex_polyhedron, W_monotonicity_1d in H.
      specialize (H (Constraint 2 [[1], [- (1)]] 0) (in_eq _ _)).
      unfold satisfies_lc in H.
      unfold dot, Mmult in H; rewrite coeff_mat_bij in H; try lia.
      unfold sum_n , sum_n_m, Iter.iter_nat in H; simpl in H.
      unfold transpose, colvec_concat, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec in H.
      repeat (rewrite coeff_mat_bij in H; try lia); simpl in H.
      unfold coeff_colvec, coeff_mat, coeff_Tn, fst in H; simpl in H.
      rewrite (mult_one_l (K:=Q_RSOAMD)), (plus_zero_l (G:=Q_RSOAMD)), (plus_zero_r (G:=Q_RSOAMD)) in H.
      rewrite (plus_zero_r (G:=Q_RSOAMD)), <- (opp_mult_m1 (K:=Q_RSOAMD)) in H.
      rewrite (ax_real_leq_true Q_RSOAMD).
      apply Rminus_le; unfold Rminus.
      rewrite <- (ax_opp_is_opp Q_RSOAMD), <- (ax_real_plus Q_RSOAMD), <- (ax_zero_is_zero Q_RSOAMD).
      rewrite <- (ax_real_leq_true Q_RSOAMD).
      apply H.
Qed.

Definition netSat_monotonicity_1d_M : matrix (T:=T Q_RSOAMD) 1 4 := [[0, 0, - (1), 1]].

Definition NNDH_monotonicity_1d: NNHyperproperty :=
    NNDH (nn_in_dim:=1) (nn_out_dim:=1)
        2 2 W_monotonicity_1d (LinearTPWAF Mone (null_vector 2)) 
        (LinearTPWAF netSat_monotonicity_1d_M (null_vector 1)).

Definition monotonicity_1d_postcondition_helper {RSOAM}:
    matrix (T:=T RSOAM) (2 + 2 * 1) 1 -> colvec (RSOAM:=RSOAM) 4.
Proof.
    intros H.
    unfold colvec; apply H.
Defined.

Lemma monotonicity_1d_postcondition:
    forall (x1: colvec 1) (x2: colvec 1) (x: colvec 2) (nn: TPWANNSequential (input_dim:=1) (output_dim:=1)),
        x1 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x i) ->
        x2 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x (i + 1)) ->
        x = colvec_concat x1 x2 ->
        (toRS (nn_eval nn x1) <= toRS (nn_eval nn x2)) =
        (0 <=
            toRS 
                (tpwaf_eval (LinearTPWAF netSat_monotonicity_1d_M (null_vector 1))
                    (monotonicity_1d_postcondition_helper
                    (colvec_concat (tpwaf_eval (LinearTPWAF Mone (null_vector 2)) x)
                    (eval_nn_multiple (r:=2) nn (tpwaf_eval (LinearTPWAF Mone (null_vector 2)) x)))))).
Proof.
    intros x1 x2 x nn Hx1 Hx2 Hx.
    unfold monotonicity_1d_postcondition_helper.
    unfold tpwaf_eval; simpl.
    unfold netSat_monotonicity_1d_M.
    rewrite Mplus_null_vector.
    unfold Mmult, toRS.
    unfold coeff_colvec.
    rewrite (coeff_mat_bij _ _ 0 0); try lia.
    unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
    unfold coeff_mat at 1; simpl.
    rewrite (mult_zero_l (K:=Q_RSOAMD)).
    unfold coeff_mat at 1; simpl.
    rewrite (mult_zero_l (K:=Q_RSOAMD)).
    repeat rewrite (plus_zero_l (G:=Q_RSOAMD)).
    unfold coeff_mat at 1; simpl.
    unfold colvec_concat at 1.
    unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
    unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
    unfold extend_colvec_on_top at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
    unfold colvec_concat at 1, coeff_colvec at 1.
    unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
    unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
    unfold extend_colvec_on_top at 1; unfold mk_colvec at 2; rewrite coeff_mat_bij; try lia; simpl.
    rewrite (plus_zero_l (G:=Q_RSOAMD)).
    rewrite (plus_zero_r (G:=Q_RSOAMD)).
    assert (Hhelp: forall v, v = x1 -> nn_eval nn v = nn_eval nn x1). intros v Hv; rewrite Hv; reflexivity.
    rewrite (Hhelp (mk_colvec 1 _)); clear Hhelp.
    * unfold coeff_mat at 1; simpl.
        rewrite (mult_one_l (K:=Q_RSOAMD)).
        unfold colvec_concat at 1.
        unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
        unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        unfold extend_colvec_on_top at 1; unfold mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        rewrite (plus_zero_l (G:=Q_RSOAMD)).
        rewrite (plus_zero_r (G:=Q_RSOAMD)).
        unfold coeff_colvec at 2, colvec_concat at 1.
        unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
        unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        unfold extend_colvec_on_top at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        rewrite (plus_zero_l (G:=Q_RSOAMD)).
        unfold coeff_colvec at 2, colvec_concat at 1.
        unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
        unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        unfold extend_colvec_on_top at 1, mk_colvec at 3; rewrite coeff_mat_bij; try lia; simpl.
        rewrite (plus_zero_r (G:=Q_RSOAMD)).
        assert (Hhelp: forall v, v = x2 -> nn_eval nn v = nn_eval nn x2). intros v Hv; rewrite Hv; reflexivity.
        rewrite (Hhelp (mk_colvec 1 _)); clear Hhelp.
        - unfold mult, plus; simpl.
          unfold coeff_colvec, coeff_mat, coeff_Tn.
          remember (QDEP_le _ _) as comp_res.
          destruct comp_res.
          * symmetry in Heqcomp_res; symmetry.
            apply (ax_real_leq_true Q_RSOAMD); apply (ax_real_leq_true Q_RSOAMD) in Heqcomp_res.
            RSOAM_realize; simpl; simpl in Heqcomp_res.
            lra.
          * symmetry in Heqcomp_res; symmetry.
            apply (ax_real_leq_false Q_RSOAMD); apply (ax_real_leq_false Q_RSOAMD) in Heqcomp_res.
            RSOAM_realize; simpl; simpl in Heqcomp_res.
            lra.
        - rewrite Hx2.
          unfold mk_colvec.
          apply mk_matrix_ext; intros i j Hi Hj.
          destruct i; destruct j; try lia.
          unfold coeff_colvec.
          unfold Mplus; repeat (rewrite coeff_mat_bij; try lia).
          do 2 rewrite (plus_zero_r (G:=Q_RSOAMD)).
          unfold Mone; repeat (rewrite coeff_mat_bij; try lia); simpl.
          rewrite (mult_one_l (K:=Q_RSOAMD)).
          rewrite (mult_zero_l (K:=Q_RSOAMD)).
          rewrite (plus_zero_l (G:=Q_RSOAMD)).
          reflexivity.        
    * rewrite Hx1.
      unfold mk_colvec.
      apply mk_matrix_ext; intros i j Hi Hj.
      destruct i; destruct j; try lia.
      unfold coeff_colvec.
      unfold Mplus; repeat (rewrite coeff_mat_bij; try lia).
      do 2 rewrite (plus_zero_r (G:=Q_RSOAMD)).
      unfold Mone; repeat (rewrite coeff_mat_bij; try lia); simpl.
      rewrite (mult_one_l (K:=Q_RSOAMD)).
      rewrite (mult_zero_l (K:=Q_RSOAMD)).
      rewrite (plus_zero_r (G:=Q_RSOAMD)).
      reflexivity. 
Qed.

Lemma monotonicity_1d_correct:
    forall (nn: TPWANNSequential (RSOAM:=Q_RSOAMD)),
        is_monotone_1d nn <-> nn_satisfies_nndh nn NNDH_monotonicity_1d.
Proof.
    intros nn.
    split; intros H.
    * unfold is_monotone_1d in H.
      unfold nn_satisfies_nndh.
      unfold NNDH_monotonicity_1d.
      intros x HxW.
      pose proof (colvec_split 1 1 x) as Hsplit.
      destruct Hsplit as [x1 [x2 [Hx1 [Hx2 Hxconcat]]]].
      specialize (H x1 x2).
      pose proof monotonicity_1d_postcondition as Hpostcondition.
      specialize (Hpostcondition x1 x2 x nn Hx1 Hx2 Hxconcat).
      unfold monotonicity_1d_postcondition_helper in Hpostcondition.
      rewrite Hpostcondition in H.
      apply H.
      apply W_monotonicity_1d_correct.
      rewrite Hxconcat in HxW.
      apply HxW.
    * unfold is_monotone_1d.
      intros x1 x2 Hpre.
      unfold nn_satisfies_nndh, NNDH_monotonicity_1d in H.
      apply W_monotonicity_1d_correct in Hpre.
      specialize (H (colvec_concat x1 x2) Hpre).
      rewrite (monotonicity_1d_postcondition _ _ (colvec_concat x1 x2)); last reflexivity.
      - unfold monotonicity_1d_postcondition_helper.
        apply H.
      - rewrite <- (mk_matrix_bij 0 x1).
        apply mk_matrix_ext.
        intros i j Hi Hj.
        induction i; induction j; try lia.
        unfold colvec_concat, coeff_colvec, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec, coeff_colvec.
        repeat (rewrite coeff_mat_bij; try lia); simpl.
        rewrite (plus_zero_r (G:=Q_RSOAMD)); reflexivity.
      - rewrite <- (mk_matrix_bij 0 x2).
        apply mk_matrix_ext.
        intros i j Hi Hj.
        induction i; induction j; try lia.
        unfold colvec_concat, coeff_colvec, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec, coeff_colvec.
        repeat (rewrite coeff_mat_bij; try lia); simpl.
        rewrite (plus_zero_l (G:=Q_RSOAMD)); reflexivity.
Qed.

Lemma is_monotone_1d_verification:
  forall nn,
    verify_hyperporperty nn NNDH_monotonicity_1d = true <-> is_monotone_1d nn.
Proof.
  intro nn.
  rewrite monotonicity_1d_correct.
  rewrite verify_hyperporperty_correct.
  apply iff_refl.
Qed.

End Monotonicity1DHyperpropery.

Section SatisfactionExample.
 
Definition example1_weights1: matrix (T:=Q_RSOAMD) 2 1 :=
    [[toQDEP 1%Q], [toQDEP 2%Q]].

Definition example1_biases1: matrix 2 1 :=
    [[toQDEP 0.5%Q], [toQDEP 0.3%Q]].

Definition example1_weights2: matrix (T:=Q_RSOAMD) 1 2 :=
    [[toQDEP 1%Q, toQDEP 2%Q]].

Definition example1_biases2: matrix 1 1 :=
    [[toQDEP 0.3%Q]].

Definition example_nn1 := 
    (NNLinear example1_weights1 example1_biases1 
    (NNReLU
    (NNLinear example1_weights2 example1_biases2
    (NNReLU
    (NNOutput (output_dim:=1)))))).

Theorem example1: 
  is_monotone_1d example_nn1.
Proof.
  apply is_monotone_1d_verification.
  vm_compute; reflexivity.
Qed.

(* Extended proof for the paper *)
Theorem example1_monotone: 
  is_monotone_1d example_nn1.
Proof.
  rewrite monotonicity_1d_correct.
  rewrite <- verify_hyperporperty_correct.
  vm_compute; reflexivity.
Qed.

End SatisfactionExample.

Section ViolationExample.

Definition example2_weights1: matrix (T:=Q_RSOAMD) 3 1 :=
    [[toQDEP (-1)%Q], [toQDEP 1%Q], [toQDEP 0.7%Q]].

Definition example2_biases1: matrix 3 1 :=
    [[toQDEP 0.1%Q], [toQDEP 0.25%Q], [toQDEP 0%Q]].

Definition example2_weights2: matrix (T:=Q_RSOAMD) 1 3 :=
    [[toQDEP 0.66%Q, toQDEP (-0.3)%Q, toQDEP 0.99%Q]].

Definition example2_biases2: matrix 1 1 :=
    [[toQDEP 0.1%Q]].

Definition example_nn2 := 
    (NNLinear example2_weights1 example2_biases1 
    (NNReLU
    (NNLinear example2_weights2 example2_biases2
    (NNReLU
    (NNOutput (output_dim:=1)))))).

Theorem example2_not_monotone :
  ~ is_monotone_1d example_nn2.
Proof.
  intro Hcontra.
  apply is_monotone_1d_verification in Hcontra.
  vm_compute in Hcontra.
  discriminate.
Qed.
  
End ViolationExample.

