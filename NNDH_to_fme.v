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

(*TODO!!!*)

Definition convert_to_fme {d: nat}
    (affine_el: AffineElement (RSOPM:=RSOPMD) (d + d) 1)
    (W: ConvexPolyhedron (RSOPM:=RSOPMD) d)
    : LinearSystem (RSOPM:=RSOPMD) d. (*Maybe not d*)
Admitted.

Theorem convert_to_fme_correct {d: nat}:
    forall affine_el (W: ConvexPolyhedron (RSOPM:=RSOPMD) d),
        satisfaction_over_element affine_el W <-> 
        fme_solve (convert_to_fme affine_el W) = None.
Admitted.

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
        match fme_solve (convert_to_fme body_el W) with
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
          apply convert_to_fme_correct.
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
          apply convert_to_fme_correct in H.
          rewrite H in Heqfme_sol.
          inversion Heqfme_sol.
        * fold (verify_hyperporperty_helper W l).
          apply IHl.
          intros body_el Hel.
          apply H.
          right; apply Hel.
Qed.

End NNHyperpropertyVerification.
