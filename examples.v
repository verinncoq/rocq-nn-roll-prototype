From Coq Require Import List QArith Lia Lqa.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import matrix_extensions neuron_functions real_subsets 
                              real_subsets_instances piecewise_affine
                              NNDH neural_networks NNDH_to_fme fourier_motzkin fm_q_support.

Open Scope RSOPM_scope.
Import RealSubsetNotations.

Section Monotonicity1DHyperpropery.

Definition monotonicity (nn: TPWANNSequential (RSOPM:=Q_RSOPMD)): Prop :=
    forall x1 x2,
        toRS x1 <= (toRS x2) = true -> toRS (nn_eval nn x1) <= toRS (nn_eval nn x2) = true.

Definition W_monotonicity: ConvexPolyhedron 2 :=
    Polyhedron (RSOPM:=Q_RSOPMD) 2 (cons (Constraint 2 [[1], [- (1)]] 0) nil).

Definition netSat_monotonicity_M : matrix (T:=T Q_RSOPMD) 1 4 := [[0, 0, - (1), 1]].

Definition NNDH_monotonicity: NNHyperproperty :=
    NNDH (nn_in_dim:=1) (nn_out_dim:=1)
        2 2 W_monotonicity (LinearTPWAF Mone (null_vector 2)) 
        (LinearTPWAF netSat_monotonicity_M (null_vector 1)).

Lemma monotonicity_correct:
    forall (nn: TPWANNSequential (RSOPM:=Q_RSOPMD)),
        monotonicity nn <-> nn_satisfies_nndh nn NNDH_monotonicity.
Proof.
    intros nn; split; intros H.
    * unfold monotonicity in H.
      unfold nn_satisfies_nndh.
      unfold NNDH_monotonicity.
      intros x HxW.
      pose proof (colvec_split 1 1 x) as Hsplit.
      destruct Hsplit as [x1 [x2 [Hx1 [Hx2 Hxconcat]]]].
      specialize (H x1 x2). simpl in H.
      unfold tpwaf_eval; simpl.
      unfold netSat_monotonicity_M.
      rewrite Mplus_null_vector.
      unfold Mmult, toRS.
      unfold coeff_colvec.
      rewrite (coeff_mat_bij _ _ 0 0); try lia.
      unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
      unfold coeff_mat at 1; simpl.
      rewrite (mult_zero_l (K:=Q_RSOPMD)).
      unfold coeff_mat at 1; simpl.
      rewrite (mult_zero_l (K:=Q_RSOPMD)).
      repeat rewrite (plus_zero_l (G:=Q_RSOPMD)).
      unfold coeff_mat at 1; simpl.
      unfold colvec_concat at 1.
      unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
      unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
      unfold extend_colvec_on_top at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
      unfold colvec_concat at 1, coeff_colvec at 1.
      unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
      unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
      unfold extend_colvec_on_top at 1; unfold mk_colvec at 2; rewrite coeff_mat_bij; try lia; simpl.
      rewrite (plus_zero_l (G:=Q_RSOPMD)).
      rewrite (plus_zero_r (G:=Q_RSOPMD)).
      assert (Hhelp: forall v, v = x1 -> nn_eval nn v = nn_eval nn x1). intros v Hv; rewrite Hv; reflexivity.
      rewrite Hhelp; clear Hhelp.
      - unfold coeff_mat at 1; simpl.
        rewrite (mult_one_l (K:=Q_RSOPMD)).
        unfold colvec_concat at 1.
        unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
        unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        unfold extend_colvec_on_top at 1; unfold mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        rewrite (plus_zero_l (G:=Q_RSOPMD)).
        rewrite (plus_zero_r (G:=Q_RSOPMD)).
        unfold coeff_colvec at 2, colvec_concat at 1.
        unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
        unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        unfold extend_colvec_on_top at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        rewrite (plus_zero_l (G:=Q_RSOPMD)).
        unfold coeff_colvec at 2, colvec_concat at 1.
        unfold Mplus at 1; rewrite coeff_mat_bij; try lia.
        unfold extend_colvec_at_bottom at 1, mk_colvec at 1; rewrite coeff_mat_bij; try lia; simpl.
        unfold extend_colvec_on_top at 1, mk_colvec at 3; rewrite coeff_mat_bij; try lia; simpl.
        rewrite (plus_zero_r (G:=Q_RSOPMD)).
        assert (Hhelp: forall v, v = x2 -> nn_eval nn v = nn_eval nn x2). intros v Hv; rewrite Hv; reflexivity.
        rewrite (Hhelp (mk_colvec 1 _)); clear Hhelp.
        * unfold mult, plus; simpl.
          assert (Halgebra: forall x11 x12 x21 x22,
                                x11 = x12 ->
                                x21 = x22 ->
                                QDEP_le x11 x21 = true ->
                                QDEP_le QDEP_zero (QDEP_plus (QDEP_mult (QDEP_opp QDEP_one) x12) x22) = true). {
                                    intros x11 x12 x21 x22 Hx11 Hx21.
                                    rewrite Hx11, Hx21.
                                    unfold QDEP_le.
                                    admit.
                                }
          apply (Halgebra (toRS (nn_eval nn x1)) _ (toRS (nn_eval nn x2)) _).
          - unfold toRS; reflexivity.
          - unfold toRS; reflexivity.
          - apply H.  
            rewrite Hxconcat in HxW.
            unfold in_convex_polyhedron, W_monotonicity in HxW.
            specialize (HxW (Constraint 2 [[1], [- (1)]] 0) (in_eq _ _)).
            unfold satisfies_lc in HxW.
            admit.
        * rewrite Hx2.
          unfold mk_colvec.
          apply mk_matrix_ext; intros i j Hi Hj.
          destruct i; destruct j; try lia.
          unfold coeff_colvec.
          unfold Mplus; repeat (rewrite coeff_mat_bij; try lia).
          do 2 rewrite (plus_zero_r (G:=Q_RSOPMD)).
          unfold Mone; repeat (rewrite coeff_mat_bij; try lia); simpl.
          rewrite (mult_one_l (K:=Q_RSOPMD)).
          rewrite (mult_zero_l (K:=Q_RSOPMD)).
          rewrite (plus_zero_l (G:=Q_RSOPMD)).
          reflexivity.        
      - rewrite Hx1.
        unfold mk_colvec.
        apply mk_matrix_ext; intros i j Hi Hj.
        destruct i; destruct j; try lia.
        unfold coeff_colvec.
        unfold Mplus; repeat (rewrite coeff_mat_bij; try lia).
        do 2 rewrite (plus_zero_r (G:=Q_RSOPMD)).
        unfold Mone; repeat (rewrite coeff_mat_bij; try lia); simpl.
        rewrite (mult_one_l (K:=Q_RSOPMD)).
        rewrite (mult_zero_l (K:=Q_RSOPMD)).
        rewrite (plus_zero_r (G:=Q_RSOPMD)).
        reflexivity.      
    *
Admitted.

End Monotonicity1DHyperpropery.

Section ExampleVerification1.

From Coq Require Import QArith.
    
Definition example_weights1: matrix (T:=Q_RSOPMD) 1 1 :=
    [[toQDEP 1%Q]].

Definition example_biases1: matrix 1 1 :=
    [[toQDEP 0.1%Q]].

Definition example_nn1 := 
    (NNLinear example_weights1 example_biases1 
    (NNReLU
    (NNOutput (output_dim:=1)))).

Compute verify_hyperporperty example_nn1 NNDH_monotonicity.

End ExampleVerification1.
