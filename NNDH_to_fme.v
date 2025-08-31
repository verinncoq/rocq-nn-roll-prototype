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

Section NNDHAffineElementToFME.

Context {RSOPMD : RSOPMWithDiv}.
Open Scope RSOPM_scope.

Definition linsys_solution_to_colvec {d}
  (sol: LinearSystemSolution (RSOPM:=RSOPMD) d)
  : colvec d :=
  mk_colvec d (fun i => sol (S i)).

Definition colvec_to_linsys_solution {d}
  (v: colvec (RSOPM:=RSOPMD) d)
  : LinearSystemSolution d :=
  (fun i => if i =? 0 then 0 else coeff_colvec 0 v i).

Definition W_to_linsys {d}
  (W: ConvexPolyhedron d)
  : LinearSystem (RSOPM:=RSOPMD) d :=
  match W with
  | Polyhedron lincons => map (fun lincon => 
    match lincon with
    | Constraint c b =>
        (fun i => if i =? 0 then (- b) else coeff_colvec 0 c (i - 1))
    end
    ) lincons
  end.

Lemma interpret_inequality_sum_n:
  forall d1 d2 (sol: LinearSystemSolution d1) (c: colvec d2) b,
    (d1 <= d2)%nat ->
    interpret_inequality_helper (fun i => if i =? 0 then (- b) else coeff_colvec 0 c (i - 1)) sol =
    sum_n (G:=RSOPMD) (fun i => if i =? 0 then (- b) else coeff_colvec 0 c (i - 1) * sol i) d1.
Proof.
  intros d1.
  induction d1; intros d2 sol c b Hleq.
  * unfold interpret_inequality_helper.
    rewrite Nat.eqb_refl.
    simpl; unfold sum_n, sum_n_m, Iter.iter_nat; simpl.
    rewrite plus_zero_r.
    reflexivity.
  * unfold interpret_inequality_helper.
    fold (interpret_inequality_helper (RSOPM:=RSOPMD) (n:=d1)).
    rewrite sum_Sn.
    rewrite IHd1; try lia.
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
    interpret_inequality_helper (fun i => if i =? 0 then (- b) else coeff_colvec 0 c (i - 1)) sol =
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
    interpret_inequality (fun i => if i =? 0 then (- b) else coeff_colvec 0 c (i - 1)) sol ->
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
  unfold W_to_linsys.
Admitted.

Definition p_to_linsys {d}
  (p: ConvexPolyhedron (d + d))
  : LinearSystem (RSOPM:=RSOPMD) d :=
  match p with
  | Polyhedron lincons => map (fun lincon => 
    match lincon with
    | Constraint c b =>
        (fun i => if i =? 0 then (- b) 
                  else (coeff_colvec 0 c (i - 1)) + (coeff_colvec 0 c (i - 1 + d)))
    end
    ) lincons
  end.

Lemma p_to_linsys_solution:
  forall d (sol: LinearSystemSolution (RSOPM:=RSOPMD) d) p,
    is_linear_system_solution (p_to_linsys p) sol ->
    in_convex_polyhedron (colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol)) p.
Proof.
Admitted.

Lemma solution_p_to_linsys:
  forall d (x: colvec (RSOPM:=RSOPMD) d) p,
    in_convex_polyhedron (colvec_concat x x) p ->
    is_linear_system_solution (p_to_linsys p) (colvec_to_linsys_solution x).
Proof.
Admitted.  

Definition af_to_linsys {d : nat} 
  (af: AffineFunction (RSOPM:=RSOPMD) (d + d) 1) 
  : LinearSystem (RSOPM:=RSOPMD) d :=
      match af with
      | Affine C b =>
          map (fun i =>
                  fun j =>
                    if j=? 0 then (- coeff_colvec 0 b i) 
                    else (coeff_mat 0 C i (j - 1)) + (coeff_mat 0 C i (j - 1 + d))) 
              (seq 0 (d + d)) 
      end.

Lemma af_to_linsys_solution:
  forall d (sol: LinearSystemSolution (RSOPM:=RSOPMD) d) af,
    is_linear_system_solution (af_to_linsys af) sol ->
    forall val,
      is_affine_f_value af (colvec_concat (linsys_solution_to_colvec sol) (linsys_solution_to_colvec sol)) val ->
      (toRS val <= 0) = true.
Proof.
Admitted.

Lemma solution_af_to_linsys:
  forall d (x: colvec (RSOPM:=RSOPMD) d) af val,
    is_affine_f_value af (colvec_concat x x) val ->
    (toRS val <= 0) = true ->
    is_linear_system_solution (af_to_linsys af) (colvec_to_linsys_solution x).
Proof.
Admitted.

Definition satisfaction_as_linear_system {d: nat}
    (affine_el: AffineElement (RSOPM:=RSOPMD) (d + d) 1)
    (W: ConvexPolyhedron (RSOPM:=RSOPMD) d)
    : LinearSystem (RSOPM:=RSOPMD) d := (*Maybe not d*)
      match affine_el with
        | Element p af => (W_to_linsys W) ++ (p_to_linsys p) ++ (af_to_linsys af)
      end.

Theorem satisfaction_as_linear_system_correct {d: nat}:
    forall affine_el (W: ConvexPolyhedron (RSOPM:=RSOPMD) d),
        satisfaction_over_element affine_el W <-> 
        fme_solve (satisfaction_as_linear_system affine_el W) = None.
Proof.
  intros el W; destruct el as [el_p el_af].
  pose proof (fme_correct _ (satisfaction_as_linear_system (Element _ _ el_p el_af) W)) as Hfme.
  split; intro H.
  * destruct (fme_solve (satisfaction_as_linear_system (Element _ _ el_p el_af) W)) as [sol|]; last reflexivity.
    unfold satisfaction_as_linear_system in Hfme.
    do 2 rewrite <- is_linear_system_solution_app in Hfme.
    destruct Hfme as [HW_sys [Hp_sys Haf_sys]].
    unfold satisfaction_over_element in H.
    specialize (H (linsys_solution_to_colvec sol)).
    apply W_to_linsys_solution in HW_sys.
    specialize (H HW_sys).
    remember (affine_element_eval (Element _ _ el_p el_af) _) as eval_res.
    destruct eval_res as [eval_res|].
    - symmetry in Heqeval_res.
      apply affine_element_eval_correct in Heqeval_res.
      unfold is_affine_element_value in Heqeval_res.
      destruct Heqeval_res as [Hdel Hf]; clear Hdel.
      pose proof (af_to_linsys_solution _ _ _ Haf_sys eval_res Hf) as Haf_sol.
      rewrite Haf_sol in H.
      discriminate H.
    - unfold affine_element_eval in Heqeval_res.
      apply p_to_linsys_solution in Hp_sys.
      apply polyhedron_eval_correct in Hp_sys.
      rewrite Hp_sys in Heqeval_res.
      discriminate Heqeval_res. 
  * rewrite H in Hfme.
    unfold satisfaction_as_linear_system in Hfme.
    unfold satisfaction_over_element; intros x HxW.
    remember (affine_element_eval (Element _ _ el_p el_af) _) as eval_res.
    destruct eval_res as [eval_res|]; last (exact I).
    symmetry in Heqeval_res; apply affine_element_eval_correct in Heqeval_res.
    unfold is_affine_element_value in Heqeval_res.
    destruct Heqeval_res as [Hel_dom Hel_val].
    remember (toRS eval_res <= 0)%RS as cmp_res.
    destruct cmp_res; last reflexivity.
    exfalso; apply Hfme.
    exists (colvec_to_linsys_solution x).
    do 2 rewrite <- is_linear_system_solution_app.
    split; try split.
    - apply solution_W_to_linsys.
      apply HxW. 
    - apply solution_p_to_linsys.
      unfold in_affine_element_domain in Hel_dom.
      apply Hel_dom.
    - apply (solution_af_to_linsys _ _ _ eval_res).
      * apply Hel_val.
      * symmetry in Heqcmp_res.
        apply Heqcmp_res.
Qed.

End NNDHAffineElementToFME.

Section NNHyperpropertyVerification.

Context {RSOPMD : RSOPMWithDiv}.
Open Scope RSOPM_scope.

(* Automated verification of neural network hyperproperties *)

Fixpoint verify_hyperporperty_helper {d: nat}
    (W: ConvexPolyhedron (RSOPM:=RSOPMD) d)
    (body: list (AffineElement (d + d) 1)) :=
    match body with
    | nil => true
    | body_el :: tail => 
        match fme_solve (satisfaction_as_linear_system body_el W) with
        | Some counterexample => false
        | None => verify_hyperporperty_helper W tail
        end
    end.

Definition verify_hyperporperty {in_dim out_dim}
    (nn: TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim))
    (nndh: NNHyperproperty)
    : bool 
    :=
    let nn_aed := aed nn in
    match nndh with
    | NNDH r w W netIn netSat =>
        let full_pwaf := 
                pwaf_compose netSat
                (pwaf_concat netIn
                    (pwaf_compose (repeat_concat r nn_aed) netIn)) in     
        verify_hyperporperty_helper W (body full_pwaf)
    end.

Theorem verify_hyperporperty_correct {in_dim out_dim}:
    forall
      (nn: TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim))
      (nndh: NNHyperproperty),
        verify_hyperporperty nn nndh = true <-> nn_satisfies_nndh nn nndh.
Proof.
    intros nn nndh.
    unfold verify_hyperporperty.
    remember (aed nn) as nn_aed.
    split; intro H.
    * apply (aed_preserves_satisfiability _ _ nn_aed); first apply Heqnn_aed.
      apply pwaf_satisfiability_elements_split.
      unfold nndh_pwaf_element_split.
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
    * apply (aed_preserves_satisfiability _ _ nn_aed) in H; last apply Heqnn_aed.
      apply pwaf_satisfiability_elements_split in H.
      unfold nndh_pwaf_element_split in H.   
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

Print Assumptions verify_hyperporperty_correct.

End NNHyperpropertyVerification.
