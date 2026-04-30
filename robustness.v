From Coq Require Import List QArith Reals Lia Lqa Lra.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import matrix_extensions neuron_functions real_subsets 
                              real_subsets_instances piecewise_affine
                              NNDH neural_networks NNDH_to_fme fourier_motzkin fm_q_support.

Open Scope RSOPM_scope.
Import RealSubsetNotations.

Section L_infty_metric.

Context {RSOPM : RealSubsetOPM}.
Import RealSubsetNotations.
Open Scope RSOPM_scope.


(* FOllowing https://kops.uni-konstanz.de/server/api/core/bitstreams/8cc59f27-b0ae-4273-9328-a9a009b08710/content*)


Definition colvec_entry_sum {n: nat} (v1 v2: colvec n) (i:nat) : RS :=
    coeff_colvec (RSOPM:= RSOPM)RSzero v1 i + coeff_colvec (RSOPM:= RSOPM)RSzero v2 i.

Definition colvec_entry_sub {n: nat} (v1 v2: colvec n) (i:nat) : RS :=
    coeff_colvec (RSOPM:= RSOPM)RSzero v1 i + - coeff_colvec (RSOPM:= RSOPM)RSzero v2 i.

Definition colvec_sub {n: nat} (v1 v2: colvec n) : colvec n :=
  mk_colvec (RSOPM:=RSOPM) n (fun i => colvec_entry_sub v1 v2 i).

Fixpoint colvec_max {n: nat} (v: colvec n) : RS :=
  match n as n0 return colvec n0 -> RS with
  | O => fun _ => RSzero
  | S n' => fun v =>
    let head := coeff_colvec (RSOPM:=RSOPM) RSzero v O in
    let tail := mk_colvec (RSOPM:=RSOPM) n'
      (fun i => coeff_colvec (RSOPM:=RSOPM) RSzero v (S i)) in
    let tail_max := colvec_max tail in
    if RSOPM_le RSOPM head tail_max then tail_max else head
  end v.

Definition RSOPM_abs (x: T RSOPM) : T RSOPM :=
    if RSOPM_le RSOPM x 0 then - x else x.

Definition L_infty_metric {n: nat} (v1 v2: colvec n) : RS :=
  colvec_max (mk_colvec (RSOPM:=RSOPM) n
    (fun i => RSOPM_abs (colvec_entry_sub v1 v2 i))).

End L_infty_metric.

Definition RSOPM_abs_Q (x: Q_RSOPMD) : Q_RSOPMD :=
    if RSOPM_le Q_RSOPMD x 0 then - x else x.


Definition is_robust_1d (nn: TPWANNSequential (RSOPM:=Q_RSOPMD)) (epsilon delta: Q_RSOPMD) 
  (Hepsilon : 0<= epsilon)
  (Hdelta : 0<= delta): Prop :=
    forall x1 x2,
        RSOPM_abs_Q (toRS x1 + -toRS x2) <= delta = true -> RSOPM_abs_Q (toRS (nn_eval nn x1) + -toRS (nn_eval nn x2)) <= epsilon= true.

Definition W_robustness_1d (delta :Q_RSOPMD)
  (Hdelta : 0<= delta): ConvexPolyhedron 2 :=
    Polyhedron (RSOPM:=Q_RSOPMD) 2 (cons (Constraint 2 [[1], [- (1)]] delta) 
                                   (cons (Constraint 2 [[- (1)], [1]] delta) nil)).

Lemma W_robustness_1d_correct (delta :Q_RSOPMD) (Hdelta: 0 <= delta ):
    forall x1 x2,
       RSOPM_abs_Q (toRS x1 + -toRS x2) <= delta = true <-> in_convex_polyhedron (colvec_concat x1 x2) (W_robustness_1d delta Hdelta).
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
      rewrite (mult_one_l (K:=Q_RSOPMD)).
      rewrite (plus_zero_l (G:=Q_RSOPMD)), (plus_zero_r (G:=Q_RSOPMD)).
      rewrite (plus_zero_r (G:=Q_RSOPMD)).
      rewrite <- (opp_mult_m1 (K:=Q_RSOPMD)).
      (* goal is d <= epsilon = true *)
      apply (ax_real_leq_true Q_RSOPMD).
      unfold RSOPM_abs_Q in Habs.
      destruct (RSOPM_le Q_RSOPMD (toRS x1 + - toRS x2) 0) eqn:Hsgn.
      * (*by transiticvity with Hdelta and Hsgn the goal follows*)
        admit.
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
      unfold coeff_colvec, coeff_mat, coeff_Tn, fst; simpl.
      rewrite <- (opp_mult_m1 (K:=Q_RSOPMD)).
      rewrite (mult_one_l (K:=Q_RSOPMD)).
      rewrite (plus_zero_l (G:=Q_RSOPMD)), (plus_zero_r (G:=Q_RSOPMD)).
      rewrite (plus_zero_r (G:=Q_RSOPMD)).
      apply (ax_real_leq_true Q_RSOPMD).
      unfold RSOPM_abs_Q in Habs.
      destruct (RSOPM_le Q_RSOPMD (toRS x1 + - toRS x2) 0) eqn:Hsgn.
      * (* *)
        apply ax_real_leq_true in Habs.
        (*some lemma that opp of bracket is the same as opp of each summand 
        to rewrite Habs
        + apply Habs*)
        admit.
      * (* since Hsgn the term in the goal is smaller then 0, 
        so also smaller then delta by transitivity*)
        apply ax_real_leq_true in Habs.
        apply ax_real_leq_false in Hsgn.
        admit.
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
    rewrite (mult_one_l (K:=Q_RSOPMD)) in Hc1.
    rewrite (plus_zero_l (G:=Q_RSOPMD)), (plus_zero_r (G:=Q_RSOPMD)) in Hc1.
    rewrite (plus_zero_r (G:=Q_RSOPMD)) in Hc1.
    rewrite <- (opp_mult_m1 (K:=Q_RSOPMD)) in Hc1.
    unfold satisfies_lc in Hc2.
    unfold dot, Mmult in Hc2; rewrite coeff_mat_bij in Hc2; try lia.
    unfold sum_n, sum_n_m, Iter.iter_nat in Hc2; simpl in Hc2.
    unfold transpose, colvec_concat, Mplus, extend_colvec_at_bottom, extend_colvec_on_top, mk_colvec in Hc2.
    repeat (rewrite coeff_mat_bij in Hc2; try lia); simpl in Hc2.
    unfold coeff_colvec, coeff_mat, coeff_Tn, fst in Hc2; simpl in Hc2.
    rewrite <- (opp_mult_m1 (K:=Q_RSOPMD)) in Hc2.
    rewrite (mult_one_l (K:=Q_RSOPMD)) in Hc2.
    rewrite (plus_zero_l (G:=Q_RSOPMD)), (plus_zero_r (G:=Q_RSOPMD)) in Hc2.
    rewrite (plus_zero_r (G:=Q_RSOPMD)) in Hc2.
    unfold RSOPM_abs_Q.
    destruct (RSOPM_le Q_RSOPMD (toRS x1 + - toRS x2) 0) eqn:Hsgn.
    + apply ax_real_leq_true.
      apply (ax_real_leq_true Q_RSOPMD) in Hc2.
      RSOPM_realize.
      (*lemma for opp and brackts to rewrite goal then apply Hc2*)
      admit.
    + apply ax_real_leq_true.
      apply (ax_real_leq_true Q_RSOPMD) in Hc1.
      apply Hc1.
Admitted.  

Section NetSat.

Variable epsilon : Q_RSOPMD.
Variable Hepsilon : 0 <= epsilon.
(*NetSat as Piecewise affine function:

f(x,y) = epsilon-(x-y) if x-y >= 0
       = epsilon-(y-x) if x-y <= 0

*)

(* only depends on inputs 3 and 4*)
Definition c_x_minus_y : colvec (RSOPM:=Q_RSOPMD) 4 :=
  [[0], [0], [1], [-(1)]].

Definition c_y_minus_x : colvec (RSOPM:=Q_RSOPMD) 4 :=
  [[0], [0], [-(1)], [1]].

(* x-y >= 0 *)
Definition P_xy_eps_nonneg : ConvexPolyhedron (RSOPM:=Q_RSOPMD) 4 :=
  Polyhedron 4 (cons (Constraint 4 c_y_minus_x 0) nil).

(* x-y <= 0*)
Definition P_yx_eps_nonneg : ConvexPolyhedron (RSOPM:=Q_RSOPMD) 4 :=
  Polyhedron 4 (cons (Constraint 4 c_x_minus_y 0) nil).

(* first function: epsilon-(x-y) *)
Definition f_xy_eps : AffineFunction (RSOPM:=Q_RSOPMD) 4 1 :=
  Affine 4 1 [[0, 0, -(1), 1]] [[epsilon]].

(* second function: epsilon-(y-x)*)
Definition f_yx_eps : AffineFunction (RSOPM:=Q_RSOPMD) 4 1 :=
  Affine 4 1 [[0, 0, 1, -(1)]] [[epsilon]].

Definition seg_xy : AffineSegment (RSOPM:=Q_RSOPMD) 4 1 :=
  Segment 4 1 P_xy_eps_nonneg f_xy_eps.

Definition seg_yx : AffineSegment (RSOPM:=Q_RSOPMD) 4 1 :=
  Segment 4 1 P_yx_eps_nonneg f_yx_eps.

Definition body_4_to_1 : list (AffineSegment (RSOPM:=Q_RSOPMD) 4 1) :=
  cons seg_xy (cons seg_yx nil).

Lemma body_4_to_1_univalence :
  pwaf_univalence (RSOPM:=Q_RSOPMD) body_4_to_1.
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


Definition pwaf_4_to_1 : PWAF (RSOPM:=Q_RSOPMD) (in_dim:=4) (out_dim:=1) :=
  mkPLF 4 1 body_4_to_1 body_4_to_1_univalence.

Lemma pwaf_4_to_1_total :
  is_total (RSOPM:=Q_RSOPMD) pwaf_4_to_1.
Proof.
  unfold is_total, pwaf_4_to_1, body_4_to_1.
  intros v.
  unfold in_pwaf_domain.
  (*FAllunterscheidung: ist v[3] <= v[4] or not*)
Admitted.

Definition tpwaf_4_to_1 : TPWAF (RSOPM:=Q_RSOPMD) (in_dim:=4) (out_dim:=1) :=
  exist _ pwaf_4_to_1 pwaf_4_to_1_total.

End NetSat.




Definition NNDH_robustness_1d (epsilon delta: Q_RSOPMD) (Hepsilon : 0<= epsilon)
  (Hdelta : 0<= delta): NNHyperproperty :=
    NNDH (nn_in_dim:=1) (nn_out_dim:=1)
        2 2 (W_robustness_1d delta Hdelta) (LinearTPWAF Mone (null_vector 2)) 
        (tpwaf_4_to_1 epsilon Hepsilon).


Definition monotonicity_1d_postcondition_helper {RSOPM}:
    matrix (T:=T RSOPM) (2 + 2 * 1) 1 -> colvec (RSOPM:=RSOPM) 4.
Proof.
    intros H.
    unfold colvec; apply H.
Defined.        
(**)
Lemma robustness_1d_postcondition (epsilon: Q_RSOPMD) (Hepsilon : 0<= epsilon):
    forall (x1: colvec 1) (x2: colvec 1) (x: colvec 2) (nn: TPWANNSequential (input_dim:=1) (output_dim:=1)),
        x1 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x i) ->
        x2 = mk_colvec 1 (fun i : nat => coeff_colvec 0 x (i + 1)) ->
        x = colvec_concat x1 x2 ->
         RSOPM_abs_Q (toRS (nn_eval nn x1) + -toRS (nn_eval nn x2)) <= epsilon =
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

Lemma monotonicity_1d_correct:
    forall (nn: TPWANNSequential (RSOPM:=Q_RSOPMD)) (epsilon delta: Q_RSOPMD) (Hepsilon : 0<= epsilon) (Hdelta : 0<= delta),
        is_robust_1d nn epsilon delta Hepsilon Hdelta <-> nn_satisfies_nndh nn (NNDH_robustness_1d epsilon delta Hepsilon Hdelta).
Proof.
Admitted.

(*multi-dimensional variant? *)
Definition is_robust {in_dim out_dim : nat}
  (nn : TPWANNSequential (RSOPM:=Q_RSOPMD)
         (input_dim:=in_dim) (output_dim:=out_dim))
  (epsilon delta : Q_RSOPMD) : Prop :=
  forall (x1 x2 : colvec in_dim),
    L_infty_metric (RSOPM:=Q_RSOPMD) x1 x2 <= delta = true ->
    L_infty_metric (RSOPM:=Q_RSOPMD)
      (nn_eval (RSOPM:=Q_RSOPMD) (in_dim:=in_dim) (out_dim:=out_dim) nn x1)
      (nn_eval (RSOPM:=Q_RSOPMD) (in_dim:=in_dim) (out_dim:=out_dim) nn x2)
      <= epsilon = true.
