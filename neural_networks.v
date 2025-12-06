From Coq Require Import QArith Reals Lia Lra.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import real_subsets real_subsets_instances matrix_extensions piecewise_affine pwaf_operations neuron_functions.

Section NeuralNetworks.

Context { RSOPM : RealSubsetOPM }.

Inductive TPWANNSequential {input_dim output_dim: nat} :=
| NNOutput : TPWANNSequential
| NNTPWALayer {hidden_dim: nat}:
    TPWAF (RSOPM:=RSOPM) (in_dim:=input_dim) (out_dim:=hidden_dim) 
    -> TPWANNSequential (input_dim:=hidden_dim) (output_dim:=output_dim)
    -> TPWANNSequential.

Definition NNLinear 
    {input_dim hidden_dim output_dim: nat} 
    (W: matrix hidden_dim input_dim) 
    (b: colvec hidden_dim) 
    (NNnext: TPWANNSequential (input_dim:=hidden_dim) (output_dim:=output_dim)) :=
    NNTPWALayer (LinearTPWAF W b) NNnext.

Definition NNReLU
    {input_dim output_dim: nat} 
    (NNnext: TPWANNSequential (input_dim:=input_dim) (output_dim:=output_dim)) :=
    NNTPWALayer (input_dim:=input_dim) ReLU_TPWAF NNnext.
    
End NeuralNetworks.

(*-----------------------------------------------------------------------------------------*)

Section SequentialNeuralNetworkExample.

Definition example_weights1: matrix 2 2 :=
    [[2%Z, 0%Z],
     [1%Z, 0%Z]].

Definition example_biases1: colvec 2 :=
    [[1%Z ], 
     [2%Z ]].

Definition example1 := 
    (NNLinear example_weights1 example_biases1 
    (NNReLU
    (NNOutput (output_dim:=2)))).
    
End SequentialNeuralNetworkExample.

(*-----------------------------------------------------------------------------------------*)

Section SequentialNeuralNetworkExample2.

Definition example_weights2: matrix (T:=QDEP_RSOPM) 2 2 :=
    [[toQDEP 1, toQDEP 1],
     [toQDEP 1, toQDEP 1]].

Definition example_biases2: colvec (RSOPM:=QDEP_RSOPM) 2 :=
    [[toQDEP 1], 
     [toQDEP 0.25]].

Definition example2: TPWANNSequential := 
    (NNLinear (input_dim:=2) example_weights2 example_biases2
    (NNReLU
    (NNLinear example_weights2 example_biases2 
    (NNOutput (output_dim:=2))))).
    
End SequentialNeuralNetworkExample2.

(*-----------------------------------------------------------------------------------------*)

Section SequentialNetworkEvaluation.

Context { RSOPM : RealSubsetOPM }.

Definition flex_dim_copy {input_dim output_dim: nat} 
    (x: colvec input_dim): colvec output_dim 
    :=
    Mmult (T:=RSOPM) (mk_matrix output_dim input_dim Mone_seq) x.

Fixpoint nn_eval {in_dim out_dim: nat} 
    (nn: TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim)) 
    (input: colvec in_dim)
    : colvec out_dim
    := 
    match nn with
        | NNOutput => flex_dim_copy input
        | NNTPWALayer _ pwaf next_layer => 
            nn_eval next_layer (tpwaf_eval pwaf input)
    end.

End SequentialNetworkEvaluation.

Section AffineSegmentDecomposition.

Context { RSOPM : RealSubsetOPM }.

Fixpoint aed {in_dim out_dim: nat}
    (nn: TPWANNSequential (input_dim := in_dim) (output_dim := out_dim)) 
    : TPWAF (RSOPM:=RSOPM) (in_dim := in_dim) (out_dim := out_dim)
    :=
    match nn with
        | NNOutput => OutputTPWAF
        | NNTPWALayer _ pwaf next => 
            tpwaf_compose (aed next) pwaf
    end.
    
Theorem aed_correct:
    forall in_dim out_dim (x: colvec in_dim) (f_x: colvec out_dim) nn nn_tpwaf,
        nn_tpwaf = aed nn ->
        is_pwaf_value nn_tpwaf x f_x <-> nn_eval nn x = f_x.
Proof.
    intros in_dim out_dim x f_x nn nn_tpwaf Hrepr.
    induction nn; unfold aed in Hrepr.
    * unfold nn_eval.
      unfold flex_dim_copy.
      unfold is_pwaf_value.
      split; intros H.
      - destruct H as [body_el [HelIn Helval]].
        rewrite Hrepr in HelIn; simpl in HelIn.
        destruct HelIn as [Hbody_el|HelIn]; try contradiction HelIn.
        rewrite <- Hbody_el in Helval.
        unfold is_affine_segment_value in Helval.
        destruct Helval as [Hdomain Hvalue].
        unfold is_affine_f_value in Hvalue.
        rewrite Mplus_null_vector in Hvalue.
        apply Hvalue.
      - exists (Segment _ _ (full_R_polyhedron input_dim) 
                    (Affine _ _ (mk_matrix (T:=RSOPM) output_dim input_dim Mone_seq) (null_vector output_dim))).
        split.
        * rewrite Hrepr; simpl.
          left; reflexivity.
        * unfold is_affine_segment_value.
          unfold in_affine_segment_domain.
          split.
          - unfold in_convex_polyhedron.
            unfold full_R_polyhedron.
            easy.
          - unfold is_affine_f_value.
            rewrite Mplus_null_vector.
            easy.
    * fold (aed (in_dim:=hidden_dim) (out_dim:=output_dim)) in Hrepr.
      unfold nn_eval; fold (nn_eval (RSOPM:=RSOPM) (in_dim:=hidden_dim) (out_dim:=output_dim)).
      rewrite Hrepr.  
      specialize (IHnn (tpwaf_eval t x) f_x (aed nn) eq_refl).
      split; intros H.
      - apply tpwaf_compose_reverse_value in H.
        destruct H as [Ht Hnn].
        apply IHnn; easy.
      - apply tpwaf_compose_correct.
        apply IHnn.
        apply H.
Qed.

End AffineSegmentDecomposition.
