From Coq Require Import Nat Reals List Arith Lia Lra.
Require Import Coquelicot.Coquelicot.

From Verinncoq Require Import real_subsets.
From Verinncoq Require Import matrix_extensions.
From Verinncoq Require Import piecewise_affine.
From Verinncoq Require Import pwaf_operations.
From Verinncoq Require Import neuron_functions.
From Verinncoq Require Import neural_networks.
From Verinncoq Require Import NNDH.
From Verinncoq Require Import fourier_motzkin.

Import RealSubsetNotations.
Import MatrixNotations.

Open Scope colvec_scope.
Open Scope matrix_scope.

Section NNDHAffineSegmentToFME.

Context {RSOPMD : RSOPMWithDiv}.
Open Scope RSOPM_scope.

Definition linsys_solution_to_colvec {d}
  (sol: LinearSystemSolution (RSOPM:=RSOPMD) d)
  : colvec d :=
  mk_colvec d (fun i => sol (S i)).

Definition colvec_to_linsys_solution {d}
  (v: colvec (RSOPM:=RSOPMD) d)
  : LinearSystemSolution d :=
  (fun i => match i with 0 => 0 | S p => coeff_colvec 0 v p end).

Lemma linsys_solution_colvec_inverse:
  forall n (x: colvec n),
    linsys_solution_to_colvec (colvec_to_linsys_solution x) = x.
Proof.
  intros n x.
  unfold linsys_solution_to_colvec.
  unfold colvec_to_linsys_solution.
  rewrite <- (mk_matrix_bij 0 x).
  apply mk_matrix_ext.
  intros i j Hi Hj; simpl.
  unfold coeff_colvec.
  rewrite coeff_mat_bij; try lia.
  induction j; last lia.
  reflexivity.
Qed.

Definition W_to_linsys {d}
  (W: ConvexPolyhedron d)
  : LinearSystem (RSOPM:=RSOPMD) d :=
  match W with
  | Polyhedron lincons => map (fun lincon => 
    match lincon with
    | Constraint c b =>
        Inclusive _ (fun i => if i =? 0 then (- b) else coeff_colvec 0 c (i - 1))
    end
    ) lincons
  end.

Lemma interpret_inequality_sum_n:
  forall d (sol: LinearSystemSolution d) b f,
    interpret_inequality_helper d (fun i => if i =? 0 then (- b) else f i) sol =
    sum_n (G:=RSOPMD) (fun i => if i =? 0 then (- b) else f i * sol i) d.
Proof.
  intros d.
  induction d; intros sol b f.
  * unfold interpret_inequality_helper.
    rewrite Nat.eqb_refl.
    simpl; unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
    rewrite plus_zero_r.
    reflexivity.
  * unfold interpret_inequality_helper.
    fold (interpret_inequality_helper (RSOPM:=RSOPMD) d); simpl.
    rewrite sum_Sn.
    rewrite IHd; try lia.
    unfold plus; simpl.
    RSOPM_realize_eq.
    lra.
Qed.

Lemma sum_n_case_Sn:
  forall n r f,
    sum_n (G:=RSOPMD) (fun i => if i =? 0 then r else (f i)) (S n) =
    plus (sum_n (fun i => f (S i)%nat) n) r.
Proof.
  induction n; intros r f.
  * unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
    rewrite plus_zero_r.
    rewrite plus_comm.
    unfold plus; simpl; reflexivity.
  * repeat rewrite sum_Sn.
    rewrite (plus_comm (sum_n _ n) (f (S (S n)))).
    rewrite <- (plus_assoc (f (S (S n)))).
    rewrite <- IHn; simpl.
    rewrite sum_Sn; simpl.
    unfold plus; simpl.
    RSOPM_realize_eq; lra.
Qed.

Lemma interpret_inequality_helper_W_to_linsys_eq:
  forall d (sol: LinearSystemSolution d) c b,
    interpret_inequality_helper d (fun i => if i =? 0 then (- b) else coeff_colvec 0 c (i - 1)) sol =
    (c * linsys_solution_to_colvec sol)%v + (- b).
Proof.
  intros d sol c b.
  unfold dot, Mmult.
  rewrite coeff_mat_bij; try lia.
  rewrite interpret_inequality_sum_n; try lia.
  destruct d.
  * unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
    do 2 (rewrite coeff_mat_default; try lia).
    rewrite mult_zero_l.
    rewrite plus_zero_r.
    rewrite plus_zero_l.
    RSOPM_realize_eq.
    lra.
  * simpl.
    rewrite sum_n_case_Sn.
    unfold plus; simpl.
    RSOPM_realize_eq.
    apply (Rplus_eq_compat_r (- INJ_RSOPM RSOPMD b)).
    f_equal.
    apply sum_n_ext_loc.
    intros i H.
    unfold linsys_solution_to_colvec.
    unfold mk_colvec, transpose.
    repeat (rewrite coeff_mat_bij; try lia).
    simpl; rewrite Nat.sub_0_r.
    unfold mult; simpl.
    reflexivity.
Qed.

Lemma interpret_inequality_W_to_linsys_solution:
  forall d (sol: LinearSystemSolution d) c b,
    interpret_inequality (Inclusive _ (fun i => if i =? 0 then (- b) else coeff_colvec 0 c (i - 1))) sol ->
    (c * linsys_solution_to_colvec sol)%v <= b = true.
Proof.
  unfold interpret_inequality.
  intros d sol c b H.
  rewrite interpret_inequality_helper_W_to_linsys_eq in H.
  apply ax_real_leq_true in H.
  apply ax_real_leq_true.
  rewrite ax_real_plus in H.
  rewrite ax_opp_is_opp in H.
  rewrite ax_zero_is_zero in H.
  lra.
Qed.

Lemma W_to_linsys_solution:
  forall d (sol: LinearSystemSolution (RSOPM:=RSOPMD) d) W,
    is_linear_system_solution (W_to_linsys W) sol ->
    in_convex_polyhedron (linsys_solution_to_colvec sol) W.
Proof.
  intros d sol W Hsol.
  unfold in_convex_polyhedron.
  destruct W as [lcs]; intros constraint Hconstraint.
  induction lcs; first contradiction Hconstraint.
  unfold W_to_linsys in Hsol.
  rewrite map_cons in Hsol.
  rewrite <- is_linear_system_solution_cons in Hsol.
  destruct Hsol as [Ha Hsol].
  apply in_inv in Hconstraint.
  destruct Hconstraint as [Hconstraint|Hconstraint].
  * rewrite Hconstraint in Ha.
    unfold satisfies_lc.
    destruct constraint as [c b].
    unfold is_linear_system_solution,interpret_inequalities in Ha.
    destruct Ha as [Ha Hclear]; clear Hclear.
    apply interpret_inequality_W_to_linsys_solution.
    apply Ha.
  * apply IHlcs.
    - unfold W_to_linsys.
      apply Hsol.
    - apply Hconstraint.
Qed.

Lemma solution_W_to_linsys:
  forall d (x: colvec (RSOPM:=RSOPMD) d) W,
    in_convex_polyhedron x W ->
    is_linear_system_solution (W_to_linsys W) (colvec_to_linsys_solution x).
Proof.
  intros d x W H.
  unfold in_convex_polyhedron in H.
  destruct W as [lcs].
  induction lcs; first (exact I).
  unfold W_to_linsys.
  unfold W_to_linsys in IHlcs.
  rewrite map_cons.
  rewrite <- is_linear_system_solution_cons; split.
  * specialize (H a (in_eq a lcs)).
    destruct a as [c b].
    unfold is_linear_system_solution, interpret_inequalities, interpret_inequality; split; last exact I.
    unfold satisfies_lc in H.
    rewrite interpret_inequality_helper_W_to_linsys_eq.
    rewrite linsys_solution_colvec_inverse.
    apply ax_real_leq_true.
    apply ax_real_leq_true in H.
    RSOPM_realize; lra.
  * apply IHlcs.
    intros constraint HIn.
    apply H, in_cons, HIn.
Qed.

Definition p_to_linsys {d}
  (p: ConvexPolyhedron (d + d))
  : LinearSystem (RSOPM:=RSOPMD) d :=
  match p with
  | Polyhedron lincons => map (fun lincon => 
    match lincon with
    | Constraint c b =>
        Inclusive _ (fun i => if i =? 0 then (- b) 
                  else (coeff_colvec 0 c (i - 1)) + (coeff_colvec 0 c (i - 1 + d)))
    end
    ) lincons
  end.

Lemma interpret_inequality_helper_p_to_linsys_eq:
  forall d (sol: LinearSystemSolution d) c b,
    interpret_inequality_helper _ (fun i => if i =? 0 then (- b) 
                                  else (coeff_colvec 0 c (i - 1)) + (coeff_colvec 0 c (i - 1 + d))
                                ) sol =
    (c * colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol))%v + (- b).
Proof.
  intros d sol c b.
  pose proof (colvec_split _ _ c) as Hsplit.
  destruct Hsplit as [c1 [c2 [Hc1 [Hc2 Hc]]]].
  rewrite Hc.
  rewrite dot_concat.
  unfold dot, Mmult.
  rewrite coeff_mat_bij; try lia.
  rewrite interpret_inequality_sum_n; try lia.
  destruct d.
  * unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
    do 2 (rewrite coeff_mat_default; try lia).
    rewrite coeff_mat_bij; try lia.
    do 2 (rewrite coeff_mat_default; try lia).
    unfold plus, mult, zero; simpl.
    RSOPM_realize_eq.
    lra.
  * rewrite coeff_mat_bij; try lia.
    rewrite sum_n_case_Sn.
    unfold plus; simpl.
    RSOPM_realize_eq.
    apply (Rplus_eq_compat_r (- INJ_RSOPM RSOPMD b)).
    rewrite <- ax_real_plus.
    f_equal.
    pose proof (sum_n_plus (G:=RSOPMD)) as Hhelp.
    unfold plus in Hhelp; simpl in Hhelp.
    rewrite <- Hhelp; clear Hhelp.
    apply sum_n_ext_loc.
    intros i H.
    unfold linsys_solution_to_colvec, mk_colvec.
    repeat (rewrite coeff_mat_bij; try lia).
    rewrite <- Hc.
    rewrite Hc1, Hc2.
    unfold transpose, mk_colvec.
    repeat rewrite coeff_mat_bij; try lia.
    rewrite Nat.sub_0_r.
    unfold mult; simpl.
    RSOPM_realize_eq.
    lra.
Qed.

Lemma interpret_inequality_p_to_linsys_solution:
  forall d (sol: LinearSystemSolution d) c b,
    interpret_inequality (Inclusive _ (fun i => if i =? 0 then (- b) 
                                  else (coeff_colvec 0 c (i - 1)) + (coeff_colvec 0 c (i - 1 + d))
                          )) sol ->
    ((c * colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol))%v <= b) = true.
Proof.
  unfold interpret_inequality.
  intros d sol c b H.
  rewrite interpret_inequality_helper_p_to_linsys_eq in H.
  apply ax_real_leq_true in H.
  apply ax_real_leq_true.
  rewrite ax_real_plus in H.
  rewrite ax_opp_is_opp in H.
  rewrite ax_zero_is_zero in H.
  lra.
Qed.

Lemma p_to_linsys_solution:
  forall d (sol: LinearSystemSolution (RSOPM:=RSOPMD) d) p,
    is_linear_system_solution (p_to_linsys p) sol ->
    in_convex_polyhedron (colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol)) p.
Proof.
  intros d sol p Hsol.
  unfold in_convex_polyhedron.
  destruct p as [lcs]; intros constraint Hconstraint.
  induction lcs; first contradiction Hconstraint.
  unfold p_to_linsys in Hsol.
  rewrite map_cons in Hsol.
  rewrite <- is_linear_system_solution_cons in Hsol.
  destruct Hsol as [Ha Hsol].
  apply in_inv in Hconstraint.
  destruct Hconstraint as [Hconstraint|Hconstraint].
  * rewrite Hconstraint in Ha.
    unfold satisfies_lc.
    destruct constraint as [c b].
    unfold is_linear_system_solution,interpret_inequalities in Ha.
    destruct Ha as [Ha Hclear]; clear Hclear.
    apply interpret_inequality_p_to_linsys_solution.
    apply Ha.
  * apply IHlcs.
    - unfold W_to_linsys.
      apply Hsol.
    - apply Hconstraint.  
Qed.

Lemma solution_p_to_linsys:
  forall d (x: colvec (RSOPM:=RSOPMD) d) p,
    in_convex_polyhedron (colvec_concat x x) p ->
    is_linear_system_solution (p_to_linsys p) (colvec_to_linsys_solution x).
Proof.
  intros d x W H.
  unfold in_convex_polyhedron in H.
  destruct W as [lcs].
  induction lcs; first (exact I).
  unfold p_to_linsys.
  unfold p_to_linsys in IHlcs.
  rewrite map_cons.
  rewrite <- is_linear_system_solution_cons; split.
  * specialize (H a (in_eq a lcs)).
    destruct a as [c b].
    unfold is_linear_system_solution, interpret_inequalities, interpret_inequality; split; last exact I.
    unfold satisfies_lc in H.
    rewrite interpret_inequality_helper_p_to_linsys_eq.
    rewrite linsys_solution_colvec_inverse.
    apply ax_real_leq_true.
    apply ax_real_leq_true in H.
    RSOPM_realize; lra.
  * apply IHlcs.
    intros constraint HIn.
    apply H, in_cons, HIn.  
Qed.  

Definition af_to_linsys {d : nat} 
  (af: AffineFunction (RSOPM:=RSOPMD) (d + d) 1) 
  : LinearSystem (RSOPM:=RSOPMD) d :=
      match af with
      | Affine C b =>
        cons (Strict _ (fun i =>
          if i =? 0 then coeff_colvec 0 b 0
            else (coeff_mat 0 C 0 (i - 1)) + (coeff_mat 0 C 0 (i - 1 + d)))) nil
      end.

Lemma interpret_inequality_helper_af_to_linsys_eq:
  forall d (sol: LinearSystemSolution d) (M_af: matrix (T:=RSOPMD) 1 (d + d)) (b_af: matrix (T:=RSOPMD) 1 1),
    interpret_inequality_helper _
     (fun i : nat => if i =? 0 then 
                        coeff_mat 0 b_af 0 0 
                     else 
                        coeff_mat 0 M_af 0 (i - 1) + coeff_mat 0 M_af 0 (i - 1 + d)) sol =
    plus
      (coeff_mat zero (M_af * colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol))%M 0 0)
      (coeff_mat zero b_af 0 0).
Proof.
  intros d sol M_af b_af.
  assert (Hhelp: 
          coeff_mat zero (M_af * colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol))%M 0 0 =
          dot (transpose M_af) (colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol))).
          unfold dot. rewrite transpose_transpose. reflexivity.
  rewrite Hhelp; clear Hhelp.
  assert (Hhelp: forall (r:T RSOPMD), r = - - r). intros r; RSOPM_realize_eq; lra.
  rewrite (Hhelp (coeff_mat zero b_af 0 0)).
  unfold plus; simpl; fold (RSplus (RSOPM:=RSOPMD)).
  rewrite <- interpret_inequality_helper_p_to_linsys_eq.
  rewrite <- Hhelp.
  unfold zero, coeff_colvec; simpl.
  unfold transpose.
  fold (RSzero (RSOPM:=RSOPMD)).
  f_equal. apply FunctionalExtensionality.functional_extensionality_dep; intro x.
  destruct (Nat.lt_ge_cases (x - 1 + d) (d + d)); destruct (Nat.lt_ge_cases (x - 1) (d + d)).
  * repeat (rewrite coeff_mat_bij; try lia).
    reflexivity.
  * rewrite coeff_mat_bij; try lia.
  * rewrite coeff_mat_bij; try lia.
    rewrite (coeff_mat_default _ _ _ _ (mk_matrix (d + d) 1 _)); try lia.
    rewrite (coeff_mat_default _ _ _ _ M_af 0 (x - 1 + d)); try lia.
    reflexivity.
  * repeat (rewrite (coeff_mat_default _ _ _ _ (mk_matrix (d + d) 1 _)); try lia).
    repeat rewrite (coeff_mat_default _ _ _ _ M_af); try lia.
    reflexivity.
Qed.

Lemma af_to_linsys_solution:
  forall d (sol: LinearSystemSolution (RSOPM:=RSOPMD) d) af,
    is_linear_system_solution (af_to_linsys af) sol ->
    forall val,
      is_affine_f_value af (colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol)) val ->
      (0 <= toRS val) = false.
Proof.
  intros d sol af Haf_sol val Hval.
  unfold is_affine_f_value in Hval.
  destruct af as [M_af b_af].
  rewrite <- Hval.
  unfold Mplus, toRS, coeff_colvec.
  repeat (rewrite coeff_mat_bij; try lia).
  unfold af_to_linsys,is_linear_system_solution, interpret_inequalities, interpret_inequality in Haf_sol.
  destruct Haf_sol as [Haf_sol Hclear]; clear Hclear.
  unfold coeff_colvec in Haf_sol.
  rewrite interpret_inequality_helper_af_to_linsys_eq in Haf_sol.
  apply Haf_sol.
Qed.

Lemma solution_af_to_linsys:
  forall d (x: colvec (RSOPM:=RSOPMD) d) af val,
    is_affine_f_value af (colvec_concat x x) val ->
    (0 <= toRS val) = false ->
    is_linear_system_solution (af_to_linsys af) (colvec_to_linsys_solution x).
Proof.
  intros d x af val Hval Haf.
  unfold is_affine_f_value in Hval.
  destruct af as [M_af b_af].
  rewrite <- Hval in Haf.
  unfold Mplus, toRS, coeff_colvec in Haf.
  repeat (rewrite coeff_mat_bij in Haf; try lia).
  unfold af_to_linsys,is_linear_system_solution, interpret_inequalities, interpret_inequality; split; last (exact I).
  unfold coeff_colvec.
  rewrite interpret_inequality_helper_af_to_linsys_eq.
  rewrite linsys_solution_colvec_inverse.
  apply Haf.
Qed.

Definition satisfaction_as_linear_system {d: nat}
    (affine_el: AffineSegment (RSOPM:=RSOPMD) (d + d) 1)
    (W: ConvexPolyhedron (RSOPM:=RSOPMD) d)
    : LinearSystem (RSOPM:=RSOPMD) d := (*Maybe not d*)
      match affine_el with
        | Segment p af => (W_to_linsys W) ++ (p_to_linsys p) ++ (af_to_linsys af)
      end.

Theorem satisfaction_as_linear_system_correct {d: nat}:
    forall affine_el (W: ConvexPolyhedron (RSOPM:=RSOPMD) d),
        satisfaction_over_segment affine_el W <-> 
        fme_solve (satisfaction_as_linear_system affine_el W) = None.
Proof.
  intros el W; destruct el as [seg_p seg_af].
  pose proof (fme_correct _ (satisfaction_as_linear_system (Segment _ _ seg_p seg_af) W)) as Hfme.
  split; intro H.
  * destruct (fme_solve (satisfaction_as_linear_system (Segment _ _ seg_p seg_af) W)) as [sol|]; last reflexivity.
    unfold satisfaction_as_linear_system in Hfme.
    do 2 rewrite <- is_linear_system_solution_app in Hfme.
    destruct Hfme as [HW_sys [Hp_sys Haf_sys]].
    unfold satisfaction_over_segment in H.
    specialize (H (linsys_solution_to_colvec sol)).
    apply W_to_linsys_solution in HW_sys.
    specialize (H HW_sys).
    remember (affine_segment_eval (Segment _ _ seg_p seg_af) _) as eval_res.
    destruct eval_res as [eval_res|].
    - symmetry in Heqeval_res.
      apply affine_segment_eval_correct in Heqeval_res.
      unfold is_affine_segment_value in Heqeval_res.
      destruct Heqeval_res as [Hdel Hf]; clear Hdel.
      pose proof (af_to_linsys_solution _ _ _ Haf_sys eval_res Hf) as Haf_sol.
      rewrite Haf_sol in H.
      discriminate H.
    - unfold affine_segment_eval in Heqeval_res.
      apply p_to_linsys_solution in Hp_sys.
      apply polyhedron_eval_correct in Hp_sys.
      rewrite Hp_sys in Heqeval_res.
      discriminate Heqeval_res. 
  * rewrite H in Hfme.
    unfold satisfaction_as_linear_system in Hfme.
    unfold satisfaction_over_segment; intros x HxW.
    remember (affine_segment_eval (Segment _ _ seg_p seg_af) _) as eval_res.
    destruct eval_res as [eval_res|]; last (exact I).
    symmetry in Heqeval_res; apply affine_segment_eval_correct in Heqeval_res.
    unfold is_affine_segment_value in Heqeval_res.
    destruct Heqeval_res as [Hseg_dom Hseg_val].
    remember (0 <= toRS eval_res )%RS as cmp_res.
    destruct cmp_res; first reflexivity.
    exfalso; apply Hfme.
    exists (colvec_to_linsys_solution x).
    do 2 rewrite <- is_linear_system_solution_app.
    split; try split.
    - apply solution_W_to_linsys.
      apply HxW. 
    - apply solution_p_to_linsys.
      unfold in_affine_segment_domain in Hseg_dom.
      apply Hseg_dom.
    - apply (solution_af_to_linsys _ _ _ eval_res).
      * apply Hseg_val.
      * symmetry in Heqcmp_res.
        apply Heqcmp_res.
Qed.

End NNDHAffineSegmentToFME.

Section NNHyperpropertyVerification.

Context {RSOPMD : RSOPMWithDiv}.
Open Scope RSOPM_scope.

(* Automated verification of neural network hyperproperties *)

Fixpoint verify_hyperporperty_helper {d: nat}
    (W: ConvexPolyhedron (RSOPM:=RSOPMD) d)
    (body: list (AffineSegment (d + d) 1)) :=
    match body with
    | nil => None
    | body_el :: tail => 
        match fme_solve (satisfaction_as_linear_system body_el W) with
        | Some counterexample => Some counterexample
        | None => verify_hyperporperty_helper W tail
        end
    end.

Definition verify_hyperporperty_witness {in_dim out_dim}
    (nn: TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim))
    (nndh: NNHyperproperty) 
    : option _
    :=
    let nn_asd := asd nn in
    match nndh with
    | NNDH r w W netIn netSat =>
        let full_pwaf := 
                pwaf_compose netSat
                (pwaf_concat netIn
                    (pwaf_compose (repeat_concat r nn_asd) netIn)) in     
        verify_hyperporperty_helper W (body full_pwaf)
    end.

Definition verify_hyperporperty {in_dim out_dim}
    (nn: TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim))
    (nndh: NNHyperproperty) 
    : bool 
    :=
    match verify_hyperporperty_witness nn nndh with
    | Some _ => false
    | None => true
    end.

Theorem verify_hyperporperty_correct {in_dim out_dim}:
    forall
      (nn: TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim))
      (nndh: NNHyperproperty),
        verify_hyperporperty nn nndh = true <-> nn_satisfies_nndh nn nndh.
Proof.
    intros nn nndh.
    unfold verify_hyperporperty, verify_hyperporperty_witness.
    remember (asd nn) as nn_asd.
    split; intro H.
    * apply (asd_preserves_satisfiability _ _ nn_asd); first apply Heqnn_asd.
      apply pwaf_satisfiability_segments_split.
      unfold nndh_pwaf_segment_split.
      destruct nndh as [r w W netIn netSat].
      induction (body _); intro body_el.
      - unfold In; contradiction.
      - intro HIn.
        apply in_inv in HIn.
        unfold verify_hyperporperty_helper in H.
        remember (fme_solve _) as fme_sol.
        destruct fme_sol; first inversion H.
        fold (verify_hyperporperty_helper W l) in H.
        destruct HIn as [HIn|HIn].
        * symmetry in Heqfme_sol.
          apply satisfaction_as_linear_system_correct.
          rewrite HIn in Heqfme_sol.
          apply Heqfme_sol.
        * apply IHl.
          apply H.
          apply HIn.
    * apply (asd_preserves_satisfiability _ _ nn_asd) in H; last apply Heqnn_asd.
      apply pwaf_satisfiability_segments_split in H.
      unfold nndh_pwaf_segment_split in H.   
      destruct nndh as [r w W netIn netSat].
      induction (body _).
      - unfold verify_hyperporperty_helper; reflexivity.
      - unfold verify_hyperporperty_helper.
        remember (fme_solve _) as fme_sol.
        destruct fme_sol.
        * specialize (H a).
          pose proof (in_eq a l) as HIn_el.
          specialize (H HIn_el).
          apply satisfaction_as_linear_system_correct in H.
          rewrite H in Heqfme_sol.
          inversion Heqfme_sol.
        * fold (verify_hyperporperty_helper W l).
          apply IHl.
          intros body_el Hel.
          apply H.
          right; apply Hel.
Qed.

End NNHyperpropertyVerification.
