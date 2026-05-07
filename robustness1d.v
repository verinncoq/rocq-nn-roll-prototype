From Coq Require Import List QArith Reals Lia Lqa Lra.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import matrix_extensions neuron_functions real_subsets 
                              real_subsets_instances piecewise_affine
                              NNDH neural_networks NNDH_to_fme fourier_motzkin fm_q_support.

Open Scope RSOAM_scope.
Import RealSubsetNotations.

Definition RSOAM_abs_Q (x: Q_RSOAMD) : Q_RSOAMD :=
    if RSOAM_le Q_RSOAMD x 0 then - x else x.

Definition is_robust_1d (nn: TPWANNSequential (RSOAM:=Q_RSOAMD)) (epsilon delta: Q_RSOAMD) 
  (Hepsilon : 0 <= epsilon)
  (Hdelta : 0 <= delta): Prop :=
    forall x1 x2,
        RSOAM_abs_Q (toRS x1 - toRS x2) <= delta = true -> 
          RSOAM_abs_Q (toRS (nn_eval nn x1) - toRS (nn_eval nn x2)) <= epsilon = true.

Definition W_robustness_1d (delta :Q_RSOAMD) (Hdelta : 0 <= delta): ConvexPolyhedron 2 :=
    Polyhedron (RSOAM:=Q_RSOAMD) 2 
       ((Constraint 2 ([[1], [- (1)]])%RS delta) ::
       (Constraint 2 [[- (1)], [1]] delta) :: nil).

Lemma RSOAM_le_transitive {RSOAM: RealSubsetOAM}:
    forall (x y z: T RSOAM),
        x <= y = true ->
        y <= z = true ->
        x <= z = true.
Proof.
    intros x y z H1 H2.
    apply ax_real_leq_true.
    apply ax_real_leq_true in H1.
    apply ax_real_leq_true in H2.
    apply Rle_trans with (r2 := INJ_RSOAM RSOAM y).
    apply H1.
    apply H2.
Qed.

Lemma RSOAM_opp_bracket {RSOAM: RealSubsetOAM}:
    forall (x y: T RSOAM),
        - (x + - y) = - x + y.
Proof.
    intros x y.
    RSOAM_realize_eq; lra.
Qed.

Lemma W_robustness_1d_correct (delta :Q_RSOAMD) (Hdelta: 0 <= delta):
    forall x1 x2,
       RSOAM_abs_Q (toRS x1 + -toRS x2) <= delta = true <-> 
       in_convex_polyhedron (colvec_concat x1 x2) (W_robustness_1d delta Hdelta).
Proof.
  intros x1 x2.
  split.
  - intro Habs.
    unfold in_convex_polyhedron, W_robustness_1d.
    intros constraint HIn.
    unfold In in HIn. 
    destruct HIn as [HIn | [HIn | HIn]]; [| | contradiction].
    + (* constraint [1; -1] <= epsilon: need to show d <= epsilon *)
      subst constraint.
      unfold satisfies_lc.
      unfold dot, Mmult; rewrite coeff_mat_bij; try lia.
      unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
      unfold transpose, colvec_concat, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec.
      repeat (rewrite coeff_mat_bij; try lia); simpl.
      unfold coeff_colvec, coeff_mat, coeff_Tn, fst; simpl.
      rewrite (mult_one_l (K:=Q_RSOAMD)).
      rewrite (plus_zero_l (G:=Q_RSOAMD)), (plus_zero_r (G:=Q_RSOAMD)).
      rewrite (plus_zero_r (G:=Q_RSOAMD)).
      rewrite <- (opp_mult_m1 (K:=Q_RSOAMD)).
      (* goal is d <= epsilon = true *)
      apply (ax_real_leq_true Q_RSOAMD).
      unfold RSOAM_abs_Q in Habs.
      destruct (RSOAM_le Q_RSOAMD (toRS x1 + - toRS x2) 0) eqn:Hsgn.
      * apply ax_real_leq_true.
        apply RSOAM_le_transitive with (y := 0).
        - exact Hsgn.
        - change (0 <= delta = true).
          apply ax_real_leq_true.
          apply Is_true_eq_true in Hdelta.
          apply ax_real_leq_true in Hdelta.
          exact Hdelta.
      * (* goal follows from Habs *)
        apply ax_real_leq_true in Habs.
        apply Habs.
    + (* constraint [-1; 1] <= epsilon: need to show -d <= epsilon *)
      subst constraint.
      unfold satisfies_lc.
      unfold dot, Mmult; rewrite coeff_mat_bij; try lia.
      unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
      unfold transpose, colvec_concat, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec.
      repeat (rewrite coeff_mat_bij; try lia); simpl.
      rewrite <- (opp_mult_m1 (K:=Q_RSOAMD)).
      rewrite (mult_one_l (K:=Q_RSOAMD)).
      rewrite (plus_zero_l (G:=Q_RSOAMD)), (plus_zero_r (G:=Q_RSOAMD)).
      rewrite (plus_zero_r (G:=Q_RSOAMD)).
      apply (ax_real_leq_true Q_RSOAMD).
      unfold RSOAM_abs_Q in Habs.
      destruct (RSOAM_le Q_RSOAMD (toRS x1 + - toRS x2) 0) eqn:Hsgn.
      * apply ax_real_leq_true in Habs.
        rewrite RSOAM_opp_bracket in Habs.
        apply Habs.
      * (* since x1-x2 >0, and x1-x2 <= delta -->  -x1+x2 <= delta*)
        unfold toRS in Habs, Hsgn.
        apply ax_real_leq_true in Habs.
        apply ax_real_leq_false in Hsgn. 
        rewrite ax_zero_is_zero, ax_real_plus, ax_opp_is_opp in Hsgn.
        rewrite ax_real_plus, ax_opp_is_opp in Habs.
        unfold plus, AbelianMonoid.plus, AbelianMonoid.class, Ring.AbelianMonoid, RSOAM_Ring, RSOAM_Ring_Class,
          RSOAM_AbelianGroup_Class, RSOAM_AbelianGroup_Mixin, AbelianGroup.base, Ring.base, Ring.class,
          RSOAM_AbelianMonoid_Mixin.
        unfold opp, AbelianGroup.opp, RSOAM_Ring_Mixin, AbelianGroup.class, AbelianGroup.mixin,
          Ring.AbelianGroup, Ring.base, Ring.class.
        RSOAM_realize.
        assert (H: RSOAM_zero Q_RSOAMD = QDEP_zero). reflexivity.
        rewrite <- H; unfold RSzero in Hsgn, Habs.
        remember (INJ_RSOAM Q_RSOAMD (coeff_colvec (RSOAM_zero Q_RSOAMD) x1 0)) as x1_R.
        remember (INJ_RSOAM Q_RSOAMD (coeff_colvec (RSOAM_zero Q_RSOAMD) x2 0)) as x2_R.
        apply (eq_rect x2_R (fun r => 
                (- INJ_RSOAM Q_RSOAMD (coeff_colvec (RSOAM_zero Q_RSOAMD) x1 0) 
                + r <= INJ_RSOAM Q_RSOAMD delta)%R)).
        apply (eq_rect x1_R (fun r => 
                - r + x2_R <= INJ_RSOAM Q_RSOAMD delta)%R).
        - lra. 
        - rewrite Heqx1_R; reflexivity.
        - rewrite Heqx2_R; reflexivity.
  - (* Backward direction: both constraints => |d| <= epsilon *)
    intro Hpoly.
    unfold in_convex_polyhedron, W_robustness_1d in Hpoly.
    assert (Hc1: satisfies_lc (colvec_concat x1 x2) (Constraint 2 [[1], [-(1)]] delta)).
    { apply Hpoly. apply in_eq. }
    assert (Hc2: satisfies_lc (colvec_concat x1 x2) (Constraint 2 [[-(1)], [1]] delta)).
    { apply Hpoly. apply in_cons. apply in_eq. }
    unfold satisfies_lc in Hc1.
    unfold dot, Mmult in Hc1; rewrite coeff_mat_bij in Hc1; try lia.
    unfold sum_n, sum_n_m, Iter.iter_nat in Hc1; simpl in Hc1.
    unfold transpose, colvec_concat, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec in Hc1.
    repeat (rewrite coeff_mat_bij in Hc1; try lia); simpl in Hc1.
    unfold coeff_colvec, coeff_mat, coeff_Tn, fst in Hc1; simpl in Hc1.
    rewrite (mult_one_l (K:=Q_RSOAMD)) in Hc1.
    rewrite (plus_zero_l (G:=Q_RSOAMD)), (plus_zero_r (G:=Q_RSOAMD)) in Hc1.
    rewrite (plus_zero_r (G:=Q_RSOAMD)) in Hc1.
    rewrite <- (opp_mult_m1 (K:=Q_RSOAMD)) in Hc1.
    unfold satisfies_lc in Hc2.
    unfold dot, Mmult in Hc2; rewrite coeff_mat_bij in Hc2; try lia.
    unfold sum_n, sum_n_m, Iter.iter_nat in Hc2; simpl in Hc2.
    unfold transpose, colvec_concat, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec in Hc2.
    repeat (rewrite coeff_mat_bij in Hc2; try lia); simpl in Hc2.
    unfold coeff_colvec, coeff_mat, coeff_Tn, fst in Hc2; simpl in Hc2.
    rewrite <- (opp_mult_m1 (K:=Q_RSOAMD)) in Hc2.
    rewrite (mult_one_l (K:=Q_RSOAMD)) in Hc2.
    rewrite (plus_zero_l (G:=Q_RSOAMD)), (plus_zero_r (G:=Q_RSOAMD)) in Hc2.
    rewrite (plus_zero_r (G:=Q_RSOAMD)) in Hc2.
    unfold RSOAM_abs_Q.
    destruct (RSOAM_le Q_RSOAMD (toRS x1 + - toRS x2) 0) eqn:Hsgn.
    + rewrite RSOAM_opp_bracket.
      apply ax_real_leq_true.
      apply (ax_real_leq_true Q_RSOAMD) in Hc2.
      apply Hc2.
    + apply ax_real_leq_true.
      apply (ax_real_leq_true Q_RSOAMD) in Hc1.
      apply Hc1.
Qed.

Section NetSat.

Variable epsilon : Q_RSOAMD.
Variable Hepsilon : 0 <= epsilon.
(*NetSat as Piecewise affine function:

f(x,y) = epsilon-(x-y) if x-y >= 0
       = epsilon-(y-x) if x-y <= 0

*)

(* only depends on inputs 3 and 4*)
Definition c_x_minus_y : colvec (RSOAM:=Q_RSOAMD) 4 :=
  [[0], [0], [1], [-(1)]].

Definition c_y_minus_x : colvec (RSOAM:=Q_RSOAMD) 4 :=
  [[0], [0], [-(1)], [1]].

(* x-y >= 0 *)
Definition P_xy_eps_nonneg : ConvexPolyhedron (RSOAM:=Q_RSOAMD) 4 :=
  Polyhedron 4 (cons (Constraint 4 c_y_minus_x 0) nil).

(* x-y <= 0*)
Definition P_yx_eps_nonneg : ConvexPolyhedron (RSOAM:=Q_RSOAMD) 4 :=
  Polyhedron 4 (cons (Constraint 4 c_x_minus_y 0) nil).

(* first function: epsilon-(x-y) *)
Definition f_xy_eps : AffineFunction (RSOAM:=Q_RSOAMD) 4 1 :=
  Affine 4 1 [[0, 0, -(1), 1]] [[epsilon]].

(* second function: epsilon-(y-x)*)
Definition f_yx_eps : AffineFunction (RSOAM:=Q_RSOAMD) 4 1 :=
  Affine 4 1 [[0, 0, 1, -(1)]] [[epsilon]].

Definition seg_xy : AffineSegment (RSOAM:=Q_RSOAMD) 4 1 :=
  Segment 4 1 P_xy_eps_nonneg f_xy_eps.

Definition seg_yx : AffineSegment (RSOAM:=Q_RSOAMD) 4 1 :=
  Segment 4 1 P_yx_eps_nonneg f_yx_eps.

Definition body_4_to_1 : list (AffineSegment (RSOAM:=Q_RSOAMD) 4 1) :=
  cons seg_xy (cons seg_yx nil).

Lemma body_4_to_1_univalence :
  pwaf_univalence (RSOAM:=Q_RSOAMD) body_4_to_1.
Proof. 
  unfold pwaf_univalence, body_4_to_1.
  intros S1 S2 HS1 HS2 x Hintersect.
  simpl in HS1, HS2.
  destruct HS1 as [HS1 | [HS1 | []]];
  destruct HS2 as [HS2 | [HS2 | []]].
  - subst S1 S2. reflexivity.
  - subst S1 S2.
    destruct Hintersect as [H1 H2].
    unfold in_affine_segment_domain in H1, H2.
    unfold seg_xy, seg_yx, P_xy_eps_nonneg, P_yx_eps_nonneg in H1, H2.
    unfold in_convex_polyhedron in H1, H2.
    assert (Hc1 : satisfies_lc x (Constraint 4 c_y_minus_x 0)). {
      apply H1. simpl. left. reflexivity.
    }
    assert (Hc2 : satisfies_lc x (Constraint 4 c_x_minus_y 0)). {
      apply H2. simpl. left. reflexivity.
    }
    unfold satisfies_lc in Hc1, Hc2.
    simpl in Hc1, Hc2.
    unfold affine_segment_eval, seg_xy, seg_yx.
    unfold polyhedron_eval, P_xy_eps_nonneg, P_yx_eps_nonneg.
    apply Qle_bool_imp_le in Hc1.
    apply Qle_bool_imp_le in Hc2. 
    unfold affine_f_eval, f_xy_eps, f_yx_eps.
    rewrite Mplus_comm.
    (* to show: dot c_x_minus_y x = 0 *)
    assert (Heq_dot: dot c_x_minus_y x = QDEP_zero).
    {
      apply ax_equality.
      rewrite ax_zero_is_zero.
      apply Rle_antisym.
      - (* dot c_x_minus_y x <= 0 *)
        apply Qreals.Qle_Rle in Hc2. 
        (*somehow Hc2? 
        apply Hc2.*) 
        admit.
      - 
        apply Qreals.Qle_Rle in Hc1.
        assert (Hsc: c_y_minus_x = scalar_mult (-(1)) c_x_minus_y).
        { unfold c_y_minus_x, c_x_minus_y, scalar_mult. 

          admit.
        }
        rewrite Hsc in Hc1.
        admit.
    }
    unfold affine_segment_eval.
    admit.
  - (* S1 = seg_yx, S2 = seg_xy: symmetric *)
    subst S1 S2.
    destruct Hintersect as [H1 H2].
    (* symmetric to above case *)
    unfold in_affine_segment_domain in H1, H2.
    unfold seg_xy, seg_yx, P_xy_eps_nonneg, P_yx_eps_nonneg in H1, H2.
    unfold in_convex_polyhedron in H1, H2.
    assert (Hc1' : satisfies_lc x (Constraint 4 c_x_minus_y 0)). {
      apply H1. simpl. left. reflexivity.
    }
    assert (Hc2' : satisfies_lc x (Constraint 4 c_y_minus_x 0)). {
      apply H2. simpl. left. reflexivity.
    }
    unfold satisfies_lc in Hc1', Hc2'. simpl in Hc1', Hc2'.
    apply Qle_bool_imp_le in Hc1'.
    apply Qle_bool_imp_le in Hc2'.
    assert (Heq_dot': dot c_y_minus_x x = QDEP_zero).
    {
      apply ax_equality.
      rewrite ax_zero_is_zero.
      apply Rle_antisym.
      - apply Qreals.Qle_Rle in Hc1'.
        admit.
      - apply Qreals.Qle_Rle in Hc2'.
        assert (Hsc': c_x_minus_y = scalar_mult (-(1)) c_y_minus_x).
        { unfold c_x_minus_y, c_y_minus_x, scalar_mult; simpl. admit. }
        admit.
    }
    unfold affine_segment_eval.
    admit.
  - subst S1 S2. reflexivity.
Admitted.


Definition pwaf_4_to_1 : PWAF (RSOAM:=Q_RSOAMD) (in_dim:=4) (out_dim:=1) :=
  mkPLF 4 1 body_4_to_1 body_4_to_1_univalence.

Lemma pwaf_4_to_1_total :
  is_total (RSOAM:=Q_RSOAMD) pwaf_4_to_1.
Proof.
  unfold is_total, pwaf_4_to_1, body_4_to_1.
  intros v.
  unfold in_pwaf_domain.
  (*FAllunterscheidung: ist v[3] <= v[4] or not*)
Admitted.

Definition tpwaf_4_to_1 : TPWAF (RSOAM:=Q_RSOAMD) (in_dim:=4) (out_dim:=1) :=
  exist _ pwaf_4_to_1 pwaf_4_to_1_total.

End NetSat.




Definition NNDH_robustness_1d (epsilon delta: Q_RSOAMD) (Hepsilon : 0<= epsilon)
  (Hdelta : 0<= delta): NNHyperproperty :=
    NNDH (nn_in_dim:=1) (nn_out_dim:=1)
        2 2 (W_robustness_1d delta Hdelta) (LinearTPWAF Mone (null_vector 2)) 
        (tpwaf_4_to_1 epsilon Hepsilon).


Definition monotonicity_1d_postcondition_helper {RSOAM}:
    matrix (T:=T RSOAM) (2 + 2 * 1) 1 -> colvec (RSOAM:=RSOAM) 4.
Proof.
    intros H.
    unfold colvec; apply H.
Defined.        
(**)
Lemma robustness_1d_postcondition (epsilon: Q_RSOAMD) (Hepsilon : 0<= epsilon):
    forall (x1: colvec 1) (x2: colvec 1) (x: colvec 2) (nn: TPWANNSequential (input_dim:=1) (output_dim:=1)),
        x1 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x i) ->
        x2 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x (i + 1)) ->
        x = colvec_concat x1 x2 ->
         RSOAM_abs_Q (toRS (nn_eval nn x1) + -toRS (nn_eval nn x2)) <= epsilon =
        (0 <=
            toRS 
                (tpwaf_eval (tpwaf_4_to_1 epsilon Hepsilon) 
                    (monotonicity_1d_postcondition_helper
                    (colvec_concat (tpwaf_eval (LinearTPWAF Mone (null_vector 2)) x)
                    (eval_nn_multiple (r:=2) nn (tpwaf_eval (LinearTPWAF Mone (null_vector 2)) x)))))).
Proof.
  intros x1 x2 x nn Hx1 Hx2 Hx.
  unfold monotonicity_1d_postcondition_helper.
  unfold tpwaf_eval. 
  unfold tpwaf_4_to_1, body_4_to_1, seg_xy, seg_yx, P_xy_eps_nonneg, P_yx_eps_nonneg, c_x_minus_y, c_y_minus_x.
Admitted.



Lemma robustness_1d_correct:
    forall (nn: TPWANNSequential (RSOAM:=Q_RSOAMD)) (epsilon delta: Q_RSOAMD) (Hepsilon : 0<= epsilon) (Hdelta : 0<= delta),
        is_robust_1d nn epsilon delta Hepsilon Hdelta <-> nn_satisfies_nndh nn (NNDH_robustness_1d epsilon delta Hepsilon Hdelta).
Proof.
Admitted.

Lemma is_robust_1d_verification (epsilon delta: Q_RSOAMD) 
  (Hepsilon : 0<= epsilon)
  (Hdelta : 0<= delta):
  forall nn,
    verify_hyperporperty nn (NNDH_robustness_1d epsilon delta Hepsilon Hdelta)= true <-> is_robust_1d nn epsilon delta Hepsilon Hdelta.
Proof.
  intro nn.
  rewrite robustness_1d_correct.
  rewrite verify_hyperporperty_correct.
  apply iff_refl.
Qed.

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


(*if input has distance up to one, output
 distance is bigger then 0*)
Theorem example4_not_robust :
  ~ is_robust_1d example_nn2 0 1 
    (ltac:(vm_compute; reflexivity)) 
    (ltac:(vm_compute; reflexivity)).
Proof.
  intro Hcontra.
  apply is_robust_1d_verification in Hcontra.
  vm_compute in Hcontra.
  discriminate.
Qed.
(*if input distance is not bigger then one then also 
the output*)
Theorem example4_robust :
  is_robust_1d example_nn2 1 1 
    (ltac:(vm_compute; reflexivity)) 
    (ltac:(vm_compute; reflexivity)).
Proof.
  apply is_robust_1d_verification.
  vm_compute.
  reflexivity.
Qed.


Theorem example4_robust_test2 :
  is_robust_1d example_nn2 (toQDEP (0.096)%Q) (toQDEP (0.1)%Q) 
    (ltac:(vm_compute; reflexivity)) 
    (ltac:(vm_compute; reflexivity)).
Proof.
  apply is_robust_1d_verification.
  vm_compute.
  reflexivity.
Qed.

Theorem example4_robust_test1 :
  is_robust_1d example_nn2 (toQDEP (0.0959)%Q) (toQDEP (0.1)%Q) 
    (ltac:(vm_compute; reflexivity)) 
    (ltac:(vm_compute; reflexivity)).
Proof.
  intro Hcontra.
  admit.
  (* apply is_robust_1d_verification in Hcontra.
  vm_compute in Hcontra.
  discriminate.
Qed. *)
Admitted.
  
End ViolationExample.
