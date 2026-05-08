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
  scalar_mult (- (1)) c_x_minus_y.

(* x-y >= 0 *)
Definition P_xy_eps_nonneg : ConvexPolyhedron (RSOAM:=Q_RSOAMD) 4 :=
  Polyhedron 4 (cons (Constraint 4 c_y_minus_x 0) nil).

(* x-y <= 0*)
Definition P_yx_eps_nonneg : ConvexPolyhedron (RSOAM:=Q_RSOAMD) 4 :=
  Polyhedron 4 (cons (Constraint 4 c_x_minus_y 0) nil).

(* first function: epsilon-(x-y) *)
Definition f_xy_eps : AffineFunction (RSOAM:=Q_RSOAMD) 4 1 :=
  Affine 4 1 (transpose c_y_minus_x) [[epsilon]].

(* second function: epsilon-(y-x)*)
Definition f_yx_eps : AffineFunction (RSOAM:=Q_RSOAMD) 4 1 :=
  Affine 4 1 (transpose c_x_minus_y) [[epsilon]].

Definition seg_xy : AffineSegment (RSOAM:=Q_RSOAMD) 4 1 :=
  Segment 4 1 P_xy_eps_nonneg f_xy_eps.

Definition seg_yx : AffineSegment (RSOAM:=Q_RSOAMD) 4 1 :=
  Segment 4 1 P_yx_eps_nonneg f_yx_eps.

Definition body_4_to_1 : list (AffineSegment (RSOAM:=Q_RSOAMD) 4 1) :=
  cons seg_xy (cons seg_yx nil).

Lemma seg_xy_seg_yx_intersection:
    forall x, 
        in_convex_polyhedron x P_xy_eps_nonneg /\ in_convex_polyhedron x P_yx_eps_nonneg ->
        dot c_x_minus_y x = 0.
Proof.
    intros x. 
    unfold in_convex_polyhedron, P_xy_eps_nonneg, P_yx_eps_nonneg, satisfies_lc. 
    intros H. destruct H as [H H0].
    specialize (H (Constraint 4 c_y_minus_x 0)). specialize (H0 (Constraint 4 c_x_minus_y 0)).
    unfold lincon1 in H. unfold lincon2 in H0.
    assert (forall dim (c: LinearConstraint (RSOAM:=Q_RSOAMD) dim), 
                c = c \/ False). {
        intros dim c. left. reflexivity.
    }
    specialize (H1 4%nat (Constraint 4 c_y_minus_x 0)) as H11.
    specialize (H1 4%nat (Constraint 4 c_x_minus_y 0)) as H12.
    apply H in H11. apply H0 in H12.
    unfold c_y_minus_x in H11.
    rewrite dot_scalar_mult in H11.
    apply ax_real_leq_true in H11.
    rewrite ax_real_mult, ax_opp_is_opp, ax_one_is_one, ax_zero_is_zero in H11.
    apply ax_real_leq_true in H12.
    rewrite ax_zero_is_zero in H12.
    RSOAM_realize_eq; lra.
Qed. (*If Rocq takes too long here, replace with Admitted*)

Lemma transpose_scalar_mult {RSOAM: RealSubsetOAM}:
  forall n m c (v: matrix (T:=RSOAM) n m),
    transpose (scalar_mult c v) = scalar_mult c (transpose v).
Proof.
  intros n m c v.
  unfold transpose, scalar_mult.
  apply mk_matrix_ext.
  intros i j Hi Hj.
  repeat (rewrite coeff_mat_bij; try lia).
  reflexivity.
Qed.

Lemma Mmult_scalar_mult {RSOAM: RealSubsetOAM}:
  forall n m k c (M1: matrix (T:=RSOAM) n m) (M2: matrix (T:=RSOAM) m k),
    Mmult (T:=RSOAM) (scalar_mult c M1) M2 = scalar_mult c (Mmult M1 M2).
Proof.
  intros n m k c M1 M2.
  unfold Mmult, scalar_mult.
  apply mk_matrix_ext.
  intros i j Hi Hj.
  rewrite coeff_mat_bij; try lia.
  assert (Hhelp: RSmult = (mult (K:=RSOAM))). reflexivity.
  rewrite Hhelp.
  rewrite <- (sum_n_mult_l (K:=RSOAM) c).
  apply (sum_n_ext_loc (G:=RSOAM)).
  intros l Hl.
  destruct m.
  - rewrite coeff_mat_default; try lia.
    rewrite (coeff_mat_default _ _ _ _ M1); try lia.
    rewrite mult_zero_l.
    rewrite mult_zero_r.
    reflexivity.
  - assert (Hdim: (S m >= 1)%nat). lia.
    pose proof (nat_pred_le_lt l (S m) Hl Hdim) as Hlm.
    rewrite coeff_mat_bij; try lia.
    symmetry; apply RSOAM_mult_assoc.
Qed.


(*changed x0 to 0 since otherwise you get the counterexample:
n = 0, m = 0, i = 0, j = 0, x0 = 1, c = 0
coeff_mat 1 (scalar_mult 0 M) 0 0 = 1
0 * coeff_mat 1 M 0 0 = 0
*)

Lemma coeff_mat_scalar_mult {RSOAM: RealSubsetOAM}:
  forall n m c (M: matrix (T:=RSOAM) n m) i j,
    coeff_mat 0 (scalar_mult c M) i j = c * coeff_mat 0 M i j.
Proof.
  intros n m c M i j.
  destruct (Compare_dec.lt_dec i n) as [Hi|Hi];
  destruct (Compare_dec.lt_dec j m) as [Hj|Hj].
  - unfold scalar_mult.
    rewrite coeff_mat_bij; try lia.
    reflexivity.
  - rewrite coeff_mat_default; try lia.
    rewrite coeff_mat_default; try lia.
    admit.
Admitted.


Lemma seg_xy_equal_seg_yx:
  forall x,
    in_affine_segment_domain seg_xy x /\ in_affine_segment_domain seg_yx x ->
    affine_segment_eval seg_xy x = affine_segment_eval seg_yx x.
Proof.
  intros x Hintersect.
  unfold in_affine_segment_domain in Hintersect.
  unfold seg_xy, seg_yx in Hintersect.
  pose proof (seg_xy_seg_yx_intersection _ Hintersect) as Hdot.
  destruct Hintersect as [Hxy Hyx].
  unfold affine_segment_eval, seg_xy, seg_yx.
  apply polyhedron_eval_correct in Hxy.
  apply polyhedron_eval_correct in Hyx.
  rewrite Hxy, Hyx.
  unfold affine_f_eval, f_xy_eps, f_yx_eps.
  assert (Hmain: (Mmult (T:=Q_RSOAMD) (transpose c_y_minus_x) x) = (Mmult (T:=Q_RSOAMD) (transpose c_x_minus_y) x)). {
      unfold dot in Hdot.
      rewrite <- (mk_matrix_bij 0 (Mmult (T:=Q_RSOAMD) (transpose c_y_minus_x) x)).
      rewrite <- (mk_matrix_bij 0 (Mmult (T:=Q_RSOAMD) (transpose c_x_minus_y) x)).
      apply mk_matrix_ext.
      intros i j Hi Hj; destruct i; destruct j; try lia.
      rewrite Hdot.
      unfold c_y_minus_x.
      rewrite transpose_scalar_mult.
      rewrite Mmult_scalar_mult.
      rewrite coeff_mat_scalar_mult.
      rewrite Hdot.
      RSOAM_realize_eq; lra.
  }
  rewrite Hmain; reflexivity.
Qed.

Lemma body_4_to_1_univalence :
  pwaf_univalence (RSOAM:=Q_RSOAMD) body_4_to_1.
Proof. 
  unfold pwaf_univalence, body_4_to_1.
  intros S1 S2 HS1 HS2 x Hintersect.
  simpl in HS1, HS2.
  destruct HS1 as [HS1 | [HS1 | []]];
  destruct HS2 as [HS2 | [HS2 | []]]; subst S1 S2.
  1,4: reflexivity.
  - apply (seg_xy_equal_seg_yx _ Hintersect).
  - symmetry; apply seg_xy_equal_seg_yx; split; apply Hintersect.
Qed.

Definition pwaf_4_to_1 : PWAF (RSOAM:=Q_RSOAMD) (in_dim:=4) (out_dim:=1) :=
  mkPLF 4 1 body_4_to_1 body_4_to_1_univalence.

Lemma pwaf_4_to_1_full_split:
    forall x,
        in_convex_polyhedron x P_xy_eps_nonneg \/ in_convex_polyhedron x P_yx_eps_nonneg.
Proof.
    intros x.
    unfold in_convex_polyhedron, P_xy_eps_nonneg, P_yx_eps_nonneg, satisfies_lc.
    destruct (dot c_x_minus_y x <= 0) eqn:Hdot.
    * right; intros constraint HIn.
      destruct HIn as [HIn|]; try contradiction.
      rewrite <- HIn.
      apply Hdot.
    * left; intros constraint HIn.
      destruct HIn as [HIn|]; try contradiction.
      rewrite <- HIn.
      unfold c_y_minus_x.
      rewrite dot_scalar_mult.
      apply ax_real_leq_true; RSOAM_realize.
      apply ax_real_leq_false in Hdot.
      rewrite ax_zero_is_zero in Hdot.
      lra.
Qed.(*If Rocq takes too long here, replace with Admitted*)

Lemma pwaf_4_to_1_total :
  is_total (RSOAM:=Q_RSOAMD) pwaf_4_to_1.
Proof.
  unfold is_total, pwaf_4_to_1, body_4_to_1.
  intros x.
  unfold in_pwaf_domain.
  specialize (pwaf_4_to_1_full_split x) as Hsplit.
  destruct Hsplit as [Hsplit|Hsplit].
  * exists seg_xy; split.
    - apply in_eq.
    - unfold in_affine_segment_domain, seg_xy.
      apply Hsplit.
  * exists seg_yx; split.
    - apply in_cons, in_eq. 
    - unfold in_affine_segment_domain, seg_yx.
      apply Hsplit.
Qed.

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
