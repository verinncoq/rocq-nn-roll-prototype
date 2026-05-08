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
  all: rewrite coeff_mat_default; try lia.
  all: rewrite coeff_mat_default; try lia.
  all: unfold RSzero.
  all: RSOAM_realize_eq.
  all: rewrite (ax_zero_is_zero RSOAM); lra.
Qed.

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
      apply (mk_matrix_ext 1 1 _ _).
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
Qed. (*If Rocq takes too long here, replace with Admitted*)

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

Definition NNDH_robustness_1d (epsilon delta: Q_RSOAMD) (Hepsilon : 0 <= epsilon)
  (Hdelta : 0<= delta): NNHyperproperty :=
    NNDH (nn_in_dim:=1) (nn_out_dim:=1)
        2 2 (W_robustness_1d delta Hdelta) (LinearTPWAF Mone (null_vector 2)) 
        (tpwaf_4_to_1 epsilon).

Definition monotonicity_1d_postcondition_helper {RSOAM}:
    matrix (T:=T RSOAM) (2 + 2 * 1) 1 -> colvec (RSOAM:=RSOAM) 4.
Proof.
    intros H.
    unfold colvec; apply H.
Defined.        

Lemma dot_c_x_minus_y_netsat_helper {RSOAM: RealSubsetOAM}:
  matrix (T:=RSOAM) (2 * 1 + 2 * 1) 1 -> colvec (RSOAM:=RSOAM) 4.
Proof.
  simpl; unfold colvec.
  intro H; apply H.
Defined.

Lemma dot_c_x_minus_y_netsat {RSOAM: RealSubsetOAM}:
  forall (x: colvec (2 * 1)) x1 x2 (nn: TPWANNSequential (input_dim:=1) (output_dim:=1)),
    x1 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x i) ->
    x2 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x (i + 1)) ->
    x = colvec_concat x1 x2 ->
    dot 
      c_x_minus_y 
      (dot_c_x_minus_y_netsat_helper (colvec_concat x (eval_nn_multiple nn x)))
      = toRS (nn_eval nn x1) - toRS (nn_eval nn x2).
Proof.
  intros x x1 x2 nn Hx1 Hx2 Hx.
  rewrite Hx1, Hx2.
  unfold dot_c_x_minus_y_netsat_helper, toRS,
         dot, eval_nn_multiple, colvec_concat,
         Mmult, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, null_vector,
         mk_colvec, coeff_colvec, transpose, c_x_minus_y, 
         sum_n, sum_n_m, Iter.iter_nat,
         mk_matrix, coeff_mat, plus, mult; simpl.
  repeat rewrite (mult_zero_l (K:=Q_RSOAMD)).
  repeat rewrite (plus_zero_l (G:=Q_RSOAMD)).
  repeat rewrite (mult_one_l (K:=Q_RSOAMD)).
  remember (@fst QDEP unit (@fst (QDEP * unit) unit (@nn_eval QDEP_RSOAM 1 1 nn [[@fst QDEP unit (@fst (QDEP * unit) (QDEP * unit * unit) x)]])))
              as nn1.
  remember (@fst QDEP unit (@fst (QDEP * unit) unit
                 (@nn_eval QDEP_RSOAM 1 1 nn [[@fst QDEP unit (@fst (QDEP * unit) unit (@snd (QDEP * unit) (QDEP * unit * unit) x))]])))
              as nn2.
  repeat rewrite (plus_zero_r (G:=Q_RSOAMD)). 
  reflexivity.
Qed.

Lemma some_removal:
  forall (T: Type) (a b: T), Some a = Some b -> a = b.
Proof.
  intros; inversion H; reflexivity.
Qed.

Lemma robustness_1d_postcondition (epsilon: Q_RSOAMD) (Hepsilon : 0 <= epsilon):
    forall (x1: colvec 1) (x2: colvec 1) (x: colvec 2) (nn: TPWANNSequential (input_dim:=1) (output_dim:=1)),
        x1 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x i) ->
        x2 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x (i + 1)) ->
        x = colvec_concat x1 x2 ->
         RSOAM_abs_Q (toRS (nn_eval nn x1) - toRS (nn_eval nn x2)) <= epsilon =
        (0 <=
            toRS 
                (tpwaf_eval (tpwaf_4_to_1 epsilon) 
                    (monotonicity_1d_postcondition_helper
                    (colvec_concat (tpwaf_eval (LinearTPWAF Mone (null_vector 2)) x)
                    (eval_nn_multiple (r:=2) nn (tpwaf_eval (LinearTPWAF Mone (null_vector 2)) x)))))).
Proof.
  intros x1 x2 x nn Hx1 Hx2 Hx.
  unfold monotonicity_1d_postcondition_helper.
  unfold tpwaf_eval at 2 3, pwaf_eval, pwaf_eval_helper, LinearTPWAF, 
          LinearPWAF, body, TPWAF2PWAF, proj1_sig, linear_body,
          affine_segment_eval, full_R_polyhedron, polyhedron_eval,
          polyhedron_eval_helper, affine_f_eval.
  rewrite Mplus_null_vector.
  rewrite Mmult_one_l.
  remember (tpwaf_eval _ _) as eval_res.
  symmetry in Heqeval_res; apply tpwaf_eval_is_value in Heqeval_res.
  apply pwaf_eval_correct in Heqeval_res.
  unfold tpwaf_4_to_1, pwaf_eval, pwaf_4_to_1, body,
         pwaf_eval_helper, body_4_to_1, TPWAF2PWAF, proj1_sig,
         affine_segment_eval, seg_xy, seg_yx in Heqeval_res.
  destruct (pwaf_4_to_1_full_split (colvec_concat x (eval_nn_multiple (r:=2) nn x))) as [Hsplit|Hsplit].
  * apply polyhedron_eval_correct in Hsplit.
    rewrite Hsplit in Heqeval_res.
    apply some_removal in Heqeval_res.
    rewrite <- Heqeval_res.
    unfold RSOAM_abs_Q.
    unfold polyhedron_eval, P_xy_eps_nonneg, polyhedron_eval_helper, lc_eval in Hsplit.
    unfold c_y_minus_x in Hsplit.
    rewrite andb_true_r in Hsplit.
    rewrite dot_scalar_mult in Hsplit.
    pose proof (dot_c_x_minus_y_netsat (RSOAM:=Q_RSOAMD) x x1 x2 nn Hx1 Hx2 Hx) as Hhelp.
    unfold dot_c_x_minus_y_netsat_helper in Hhelp.
    rewrite <- Hhelp.
    destruct (RSOAM_le Q_RSOAMD (dot (RSOAM:=Q_RSOAMD) _ _) 0) eqn:Hcmp.
    - apply ax_real_leq_true in Hsplit.
      apply ax_real_leq_true in Hcmp.
      rewrite ax_zero_is_zero in Hsplit, Hcmp.
      rewrite ax_real_mult, ax_opp_is_opp, ax_one_is_one in Hsplit.
      assert (Hdep: dot (RSOAM:=Q_RSOAMD) c_x_minus_y (colvec_concat x (eval_nn_multiple (r:=2) nn x)) =
                      @dot Q_RSOAMD 4 c_x_minus_y
                            (@colvec_concat Q_RSOAMD (2 * 1) (2 * 1) x
                                  (@eval_nn_multiple Q_RSOAMD 2 1 1 nn x))). reflexivity.
      assert (Hzero: dot (RSOAM:=Q_RSOAMD) c_x_minus_y (colvec_concat x (eval_nn_multiple (r:=2) nn x)) = 0). {
        rewrite Hdep in Hsplit.
        rewrite Hdep.
        remember (@dot Q_RSOAMD 4 c_x_minus_y
                            (@colvec_concat Q_RSOAMD (2 * 1) (2 * 1) x
                                  (@eval_nn_multiple Q_RSOAMD 2 1 1 nn x))) as dot_res.
        RSOAM_realize_eq.
        lra.
      }
      assert (Hzero2: @dot Q_RSOAMD 4 c_x_minus_y
                          (@colvec_concat Q_RSOAMD (2 * 1) (2 * 1) x
                                (@eval_nn_multiple Q_RSOAMD 2 1 1 nn x)) = 0). {
          rewrite <- Hzero.
          reflexivity.
      }
      rewrite Hzero2.
      unfold affine_f_eval, f_xy_eps.
      unfold c_y_minus_x.
      rewrite transpose_scalar_mult.
      rewrite Mmult_scalar_mult.
      unfold dot in Hzero2.
      unfold scalar_mult, mk_matrix, mk_Tn.
      unfold dot in Hzero.
      rewrite Hzero.
      unfold Mplus, toRS, coeff_colvec.
      repeat (rewrite coeff_mat_bij; try lia).
      remember (- 0 <= epsilon) as cmp_res.
      destruct cmp_res.
      * symmetry.
        apply ax_real_leq_true.
        unfold coeff_mat, coeff_Tn, fst.
        assert (Hweird: (plus (G:=Q_RSOAMD)) = (RSplus (RSOAM:=Q_RSOAMD))). reflexivity.
        rewrite Hweird.
        RSOAM_realize.
        unfold RSzero.
        rewrite (ax_zero_is_zero Q_RSOAMD).
        symmetry in Heqcmp_res.
        apply ax_real_leq_true in Heqcmp_res.
        rewrite ax_opp_is_opp in Heqcmp_res.
        rewrite ax_zero_is_zero in Heqcmp_res.
        lra.
      * symmetry.
        apply ax_real_leq_false.
        unfold coeff_mat, coeff_Tn, fst.
        assert (Hweird: (plus (G:=Q_RSOAMD)) = (RSplus (RSOAM:=Q_RSOAMD))). reflexivity.
        rewrite Hweird.
        RSOAM_realize.
        symmetry in Heqcmp_res.
        apply ax_real_leq_false in Heqcmp_res.
        rewrite ax_opp_is_opp in Heqcmp_res.
        rewrite ax_zero_is_zero in Heqcmp_res.
        lra.
    - unfold affine_f_eval, f_xy_eps, c_y_minus_x, dot.
      unfold toRS, Mplus, coeff_colvec.
      repeat (rewrite coeff_mat_bij; try lia).
      unfold coeff_mat at 3, coeff_Tn, fst.
      rewrite transpose_scalar_mult.
      rewrite Mmult_scalar_mult.
      unfold dot in Hhelp.
      rewrite Hhelp.
      rewrite (coeff_mat_scalar_mult (RSOAM:=Q_RSOAMD)).
      remember (toRS (nn_eval nn x1) - toRS (nn_eval nn x2) <= epsilon) as b.
      destruct b.
      * symmetry in Heqb.
        apply ax_real_leq_true in Heqb.
        symmetry; apply ax_real_leq_true.
        assert (Hweird: (plus (G:=Q_RSOAMD)) = (RSplus (RSOAM:=Q_RSOAMD))). reflexivity.
        rewrite Hweird.
        RSOAM_realize.
        assert (Halg: (forall r1 r2, r1 <= r2 -> 0 <= - (1) * r1 + r2)%R). {
          intros r1 r2 H.
          rewrite Ropp_mult_distr_l_reverse.
          lra.
        }
        apply Halg.
        rewrite <- Hhelp in Heqb.
        apply Heqb.
      * symmetry in Heqb.
        apply ax_real_leq_false in Heqb.
        symmetry; apply ax_real_leq_false.
        assert (Hweird: (plus (G:=Q_RSOAMD)) = (RSplus (RSOAM:=Q_RSOAMD))). reflexivity.
        rewrite Hweird.
        RSOAM_realize.
        assert (Halg: (forall r1 r2, r2 < r1 -> - (1) * r1 + r2 < 0 )%R). {
          intros r1 r2 H.
          rewrite Ropp_mult_distr_l_reverse.
          lra.
        }
        apply Halg.
        rewrite <- Hhelp in Heqb.
        apply Heqb.      
  * destruct (polyhedron_eval (dim:=4) (colvec_concat x (eval_nn_multiple (r:=2) nn x)) P_xy_eps_nonneg) eqn:Hinxy.
    - apply polyhedron_eval_correct in Hinxy.
      pose proof (seg_xy_seg_yx_intersection 
                    (colvec_concat x (eval_nn_multiple (r:=2) nn x))
                    (conj Hinxy Hsplit)) as Hintersect.
      pose proof (dot_c_x_minus_y_netsat (RSOAM:=Q_RSOAMD) x x1 x2 nn Hx1 Hx2 Hx) as Hhelp.
      unfold dot_c_x_minus_y_netsat_helper in Hhelp.
      Set Printing Implicit.
      assert (Hdep: @dot Q_RSOAMD 4 c_x_minus_y (@colvec_concat Q_RSOAMD 2 (2 * 1) x (@eval_nn_multiple Q_RSOAMD 2 1 1 nn x)) =
                    @dot Q_RSOAMD 4 c_x_minus_y (@colvec_concat Q_RSOAMD (2 * 1) (2 * 1) x (@eval_nn_multiple Q_RSOAMD 2 1 1 nn x))).
      reflexivity.
      rewrite Hdep in Hintersect.
      rewrite Hhelp in Hintersect.
      rewrite Hintersect.
      unfold RSOAM_abs_Q.
      assert (Hle: RSOAM_le Q_RSOAMD 0 0 = true). reflexivity.
      rewrite Hle.
      apply some_removal in Heqeval_res.
      rewrite <- Heqeval_res.
      remember (- 0 <= epsilon) as cmp_res.
      destruct cmp_res.
      * symmetry.
        apply ax_real_leq_true.
        unfold affine_f_eval, f_xy_eps, c_y_minus_x.
        rewrite transpose_scalar_mult.
        rewrite Mmult_scalar_mult.
        rewrite <-Hhelp in Hintersect.
        rewrite <-Hdep in Hintersect.
        unfold dot in Hintersect.
        unfold toRS, Mplus, coeff_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite (coeff_mat_scalar_mult (RSOAM:=Q_RSOAMD)).
        rewrite Hintersect.
        unfold coeff_mat, coeff_Tn, fst.
        assert (Hweird: (plus (G:=Q_RSOAMD)) = (RSplus (RSOAM:=Q_RSOAMD))). reflexivity.
        rewrite Hweird.
        RSOAM_realize.
        unfold RSzero.
        rewrite (ax_zero_is_zero Q_RSOAMD).
        symmetry in Heqcmp_res.
        apply ax_real_leq_true in Heqcmp_res.
        rewrite ax_opp_is_opp in Heqcmp_res.
        rewrite ax_zero_is_zero in Heqcmp_res.
        lra.
      * symmetry.
        apply ax_real_leq_false.
        unfold affine_f_eval, f_xy_eps, c_y_minus_x.
        rewrite transpose_scalar_mult.
        rewrite Mmult_scalar_mult.
        rewrite <-Hhelp in Hintersect.
        rewrite <-Hdep in Hintersect.
        unfold dot in Hintersect.
        unfold toRS, Mplus, coeff_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite (coeff_mat_scalar_mult (RSOAM:=Q_RSOAMD)).
        rewrite Hintersect.
        unfold coeff_mat, coeff_Tn, fst.
        assert (Hweird: (plus (G:=Q_RSOAMD)) = (RSplus (RSOAM:=Q_RSOAMD))). reflexivity.
        rewrite Hweird.
        RSOAM_realize.
        unfold RSzero.
        symmetry in Heqcmp_res.
        apply ax_real_leq_false in Heqcmp_res.
        rewrite ax_opp_is_opp in Heqcmp_res.
        rewrite ax_zero_is_zero in Heqcmp_res.
        lra.
    - apply polyhedron_eval_correct in Hsplit.
      rewrite Hsplit in Heqeval_res.
      apply some_removal in Heqeval_res.
      rewrite <- Heqeval_res.
      unfold RSOAM_abs_Q.
      unfold P_yx_eps_nonneg, polyhedron_eval, polyhedron_eval_helper, lc_eval in Hsplit.
      rewrite andb_true_r in Hsplit.
      pose proof (dot_c_x_minus_y_netsat (RSOAM:=Q_RSOAMD) x x1 x2 nn Hx1 Hx2 Hx) as Hhelp.
      unfold dot_c_x_minus_y_netsat_helper in Hhelp.
      rewrite <- Hhelp.
      destruct (RSOAM_le Q_RSOAMD _ 0) eqn:Hcmp.
      * remember ((- @dot Q_RSOAMD 4 c_x_minus_y (@colvec_concat Q_RSOAMD (2 * 1) (2 * 1) x (@eval_nn_multiple Q_RSOAMD 2 1 1 nn x)) <= epsilon)) as cmp.
        destruct cmp.
        - unfold affine_f_eval, f_yx_eps. 
          symmetry; apply ax_real_leq_true.
          rewrite ax_zero_is_zero.
          unfold toRS, Mplus, coeff_colvec.
          repeat (rewrite coeff_mat_bij; try lia).
          assert (Hweird: (plus (G:=Q_RSOAMD)) = (RSplus (RSOAM:=Q_RSOAMD))). reflexivity.
          rewrite Hweird.
          rewrite ax_real_plus.
          symmetry in Heqcmp; apply ax_real_leq_true in Heqcmp.
          unfold dot in Heqcmp.
          rewrite ax_opp_is_opp in Heqcmp.
          assert (Hweird2: (zero (G:=Q_RSOAMD)) = 0). reflexivity.
          rewrite Hweird2 at 1.
          unfold coeff_mat at 2, coeff_Tn, fst.
          assert (Halg: (forall r1 r2, - r1 <= r2 -> 0 <= r1 + r2)%R). {
            intros r1 r2 H.
            nra.
          } 
          apply Halg.
          apply Heqcmp.
        - unfold affine_f_eval, f_yx_eps. 
          symmetry; apply ax_real_leq_false.
          rewrite ax_zero_is_zero.
          unfold toRS, Mplus, coeff_colvec.
          repeat (rewrite coeff_mat_bij; try lia).
          assert (Hweird: (plus (G:=Q_RSOAMD)) = (RSplus (RSOAM:=Q_RSOAMD))). reflexivity.
          rewrite Hweird.
          rewrite ax_real_plus.
          symmetry in Heqcmp; apply ax_real_leq_false in Heqcmp.
          unfold dot in Heqcmp.
          rewrite ax_opp_is_opp in Heqcmp.
          assert (Hweird2: (zero (G:=Q_RSOAMD)) = 0). reflexivity.
          rewrite Hweird2 at 1.
          unfold coeff_mat at 2, coeff_Tn, fst.
          assert (Halg: (forall r1 r2, r2 < - r1 -> r1 + r2 < 0)%R). {
            intros r1 r2 H.
            nra.
          } 
          apply Halg.
          apply Heqcmp.
      * unfold RSle in Hsplit.
        exfalso.
        assert (Hcontra: true = false -> False). discriminate.
        apply Hcontra.
        rewrite <- Hsplit.
        rewrite <- Hcmp.
        reflexivity.
Qed. (*If Rocq takes too long here, replace with Admitted*)

Lemma robustness_1d_correct:
  forall (nn: TPWANNSequential (RSOAM:=Q_RSOAMD)) (epsilon delta: Q_RSOAMD) 
          (Hepsilon : 0 <= epsilon) (Hdelta : 0 <= delta),
      is_robust_1d nn epsilon delta Hepsilon Hdelta <-> 
      nn_satisfies_nndh nn (NNDH_robustness_1d epsilon delta Hepsilon Hdelta).
Proof.
  intros nn epsilon delta Hepsilon Hdelta.
  split; intro H.
  * unfold nn_satisfies_nndh.
    unfold NNDH_robustness_1d.
    intros x HxW.
    pose proof (colvec_split 1 1 x) as Hsplit.
    destruct Hsplit as [x1 [x2 [Hx1 [Hx2 Hxconcat]]]].
    specialize (H x1 x2).
    pose proof robustness_1d_postcondition as Hpostcondition.
    specialize (Hpostcondition epsilon Hepsilon x1 x2 x nn Hx1 Hx2 Hxconcat).
    unfold monotonicity_1d_postcondition_helper in Hpostcondition.
    rewrite Hpostcondition in H.
    apply H.
    rewrite (W_robustness_1d_correct delta Hdelta x1 x2).
    rewrite Hxconcat in HxW.
    apply HxW.
  * unfold is_robust_1d.
    intros x1 x2 Hpre.
    unfold nn_satisfies_nndh, NNDH_robustness_1d in H.
    apply (W_robustness_1d_correct delta Hdelta) in Hpre.
    specialize (H (colvec_concat x1 x2) Hpre).
    rewrite (robustness_1d_postcondition epsilon Hepsilon _ _ (colvec_concat x1 x2)); last reflexivity.
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

Lemma is_robust_1d_verification (epsilon delta: Q_RSOAMD) 
  (Hepsilon : 0 <= epsilon)
  (Hdelta : 0 <= delta):
  forall nn,
    verify_hyperporperty nn (NNDH_robustness_1d epsilon delta Hepsilon Hdelta)= true <-> is_robust_1d nn epsilon delta Hepsilon Hdelta.
Proof.
  intro nn.
  rewrite robustness_1d_correct.
  rewrite verify_hyperporperty_correct.
  apply iff_refl.
Qed.

Section RobustnessExample.

Definition example_weights1: matrix (T:=Q_RSOAMD) 3 1 :=
    [[toQDEP (-1)%Q], [toQDEP 1%Q], [toQDEP 0.7%Q]].

Definition example_biases1: matrix 3 1 :=
    [[toQDEP 0.1%Q], [toQDEP 0.25%Q], [toQDEP 0%Q]].

Definition example_weights2: matrix (T:=Q_RSOAMD) 1 3 :=
    [[toQDEP 0.66%Q, toQDEP (-0.3)%Q, toQDEP 0.99%Q]].

Definition example_biases2: matrix 1 1 :=
    [[toQDEP 0.1%Q]].

Definition example_nn := 
    (NNLinear example_weights1 example_biases1 
    (NNReLU
    (NNLinear example_weights2 example_biases2
    (NNReLU
    (NNOutput (output_dim:=1)))))).

(*if input has distance up to one, output
 distance is bigger then 0*)
Theorem example_not_robust (H1: 0 <= 0) (H2: 0 <= 1):
  ~ is_robust_1d example_nn 0 1 H1 H2. 
Proof.
  intro Hcontra.
  apply is_robust_1d_verification in Hcontra.
  vm_compute in Hcontra.
  discriminate.
Qed.
(*if input distance is not bigger then one then also 
the output*)
Theorem example_robust (H1: 0 <= 1) (H2: 0 <= 1):
  is_robust_1d example_nn 1 1 H1 H2.
Proof.
  apply is_robust_1d_verification.
  vm_compute.
  reflexivity.
Qed.

Theorem example_robust2 
  (H1: RSOAM_le Q_RSOAMD 0 (toQDEP (0.096)%Q))
  (H2: RSOAM_le Q_RSOAMD 0 (toQDEP (0.1)%Q)):
  is_robust_1d example_nn (toQDEP (0.096)%Q) (toQDEP (0.1)%Q) H1 H2.
Proof.
  apply is_robust_1d_verification.
  vm_compute.
  reflexivity.
Qed.

Theorem example_not_robust2
  (H1: RSOAM_le Q_RSOAMD 0 (toQDEP (0.0959)%Q))
  (H2: RSOAM_le Q_RSOAMD 0 (toQDEP (0.1)%Q)):
  ~ is_robust_1d example_nn (toQDEP (0.0959)%Q) (toQDEP (0.1)%Q) H1 H2.
Proof.
  intro Hcontra.
  apply is_robust_1d_verification in Hcontra.
  vm_compute in Hcontra.
  discriminate.
Qed. 
  
End RobustnessExample.
