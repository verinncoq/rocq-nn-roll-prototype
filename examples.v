From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import matrix_extensions neuron_functions real_subsets 
                              real_subsets_instances piecewise_affine
                              NNDH neural_networks NNDH_to_fme fourier_motzkin fm_q_support.

Open Scope RSOPM_scope.
Import RealSubsetNotations.

Section Monotonicity1DHyperpropery.

Definition monotonicity (nn: TPWANNSequential (RSOPM:=Q_RSOPMD)): Prop :=
    forall x1 x2,
        toRS x1 <= (toRS x2) = true -> toRS (nn_eval nn x2) <= toRS (nn_eval nn x1) = false.

Definition W_monotonicity: ConvexPolyhedron 2 :=
    Polyhedron (RSOPM:=Q_RSOPMD) 2 (cons (Constraint 2 [[1], [- (1)]] 0) nil).

Definition netSat_monotonicity_M : matrix (T:=T Q_RSOPMD) 1 4 := [[0, 0, - (1), 1]].

Definition NNDH_monotonicity: NNHyperproperty :=
    NNDH (nn_in_dim:=1) (nn_out_dim:=1)
        2 2 W_monotonicity (LinearTPWAF Mone (null_vector 2)) 
        (LinearTPWAF netSat_monotonicity_M (null_vector 1)).

Lemma monotonicity_validation:
    forall (nn: TPWANNSequential (RSOPM:=Q_RSOPMD)),
        monotonicity nn <-> nn_satisfies_nndh nn NNDH_monotonicity.
Proof.
    intros nn; split; intros H.
    * unfold monotonicity in H.
      unfold nn_satisfies_nndh.
      unfold NNDH_monotonicity.
      intros x HxW.
      unfold tpwaf_eval at 2 3.
      unfold pwaf_eval, pwaf_eval_helper.
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

Compute match verify_hyperporperty example_nn1 NNDH_monotonicity with None => 0%Q | Some w => QDEP2Q (w 5%nat) end.

Compute QDEP2Q (toRS (nn_eval example_nn1 [[toQDEP (-0.1)%Q]])).
    

End ExampleVerification1.
