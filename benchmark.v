From Coq Require Import List 
                        QArith.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import real_subsets 
                              real_subsets_instances 
                              fourier_motzkin 
                              fm_q_support 
                              neural_networks
                              NNDH_to_fme
                              monotonicity1d.

Open Scope RSOPM_scope.
Import RealSubsetNotations.

Section OneActivation.
    
Definition example1_weights1: matrix (T:=Q_RSOPMD) 1 1 :=
    [[toQDEP 1.106%Q]].

Definition example1_biases1: matrix 1 1 :=
    [[toQDEP 0.677%Q]].

Definition example_nn1 := 
    (NNLinear example1_weights1 example1_biases1 
    (NNReLU
    (NNOutput (output_dim:=1)))).

(* Time Compute (verify_hyperporperty example_nn1 NNDH_monotonicity_1d). *)

End OneActivation. 

(* -------------------------------------------------------------------------------- *)

Section TwoActivations.

Definition example2_weights1: matrix (T:=Q_RSOPMD) 1 1 :=
    [[toQDEP 1.463%Q]].

Definition example2_biases1: matrix 1 1 :=
    [[toQDEP 0.828%Q]].

Definition example2_weights2: matrix (T:=Q_RSOPMD) 1 1 :=
    [[toQDEP 1.749%Q]].

Definition example2_biases2: matrix 1 1 :=
    [[toQDEP 0.637%Q]].

Definition example_nn2 := 
    (NNLinear example2_weights1 example2_biases1 
    (NNReLU
    (NNLinear example2_weights2 example2_biases2
    (NNReLU
    (NNOutput (output_dim:=1)))))).

(* Time Compute (verify_hyperporperty example_nn2 NNDH_monotonicity_1d). *)

End TwoActivations.

(* -------------------------------------------------------------------------------- *)

Section ThreeActivations.

Definition example3_weights1: matrix (T:=Q_RSOPMD) 1 1 :=
    [[toQDEP 1.978%Q]].

Definition example3_biases1: matrix 1 1 :=
    [[toQDEP 0.645%Q]].

Definition example3_weights2: matrix (T:=Q_RSOPMD) 1 1 :=
    [[toQDEP 1.160%Q]].

Definition example3_biases2: matrix 1 1 :=
    [[toQDEP 0.304%Q]].

Definition example3_weights3: matrix (T:=Q_RSOPMD) 1 1 :=
    [[toQDEP 1.817%Q]].

Definition example3_biases3: matrix 1 1 :=
    [[toQDEP 0.314%Q]].

Definition example_nn3 := 
    (NNLinear example3_weights1 example3_biases1 
    (NNReLU
    (NNLinear example3_weights2 example3_biases2
    (NNReLU
    (NNLinear example3_weights3 example3_biases3 
    (NNReLU
    (NNOutput (output_dim:=1)))))))).

(* Time Compute (verify_hyperporperty example_nn3 NNDH_monotonicity_1d). *)

End ThreeActivations.

(* -------------------------------------------------------------------------------- *)

Section FourActivations.

Definition example4_weights1: matrix (T:=Q_RSOPMD) 2 1 :=
    [[toQDEP 1.978%Q], [toQDEP 1.978%Q]].

Definition example4_biases1: matrix 2 1 :=
    [[toQDEP 0.645%Q], [toQDEP 0.645%Q]].

Definition example4_weights2: matrix (T:=Q_RSOPMD) 1 2 :=
    [[toQDEP 1.160%Q, toQDEP 1.160%Q]].

Definition example4_biases2: matrix 1 1 :=
    [[toQDEP 0.304%Q]].

Definition example4_weights3: matrix (T:=Q_RSOPMD) 1 1 :=
    [[toQDEP 1.817%Q]].

Definition example4_biases3: matrix 1 1 :=
    [[toQDEP 0.314%Q]].

Definition example_nn4 := 
    (NNLinear example4_weights1 example4_biases1 
    (NNReLU
    (NNLinear example4_weights2 example4_biases2
    (NNReLU
    (NNLinear example4_weights3 example4_biases3 
    (NNReLU
    (NNOutput (output_dim:=1)))))))).

(* Time Compute (verify_hyperporperty example_nn4 NNDH_monotonicity_1d). *)

End FourActivations.

(* -------------------------------------------------------------------------------- *)

Section FiveActivations.

Definition example5_weights1: matrix (T:=Q_RSOPMD) 2 1 :=
    [[toQDEP 1.754%Q], [toQDEP 1.574%Q]].

Definition example5_biases1: matrix 2 1 :=
    [[toQDEP 0.920%Q], [toQDEP 0.838%Q]].

Definition example5_weights2: matrix (T:=Q_RSOPMD) 2 2 :=
    [[toQDEP 1.06%Q, toQDEP 1.215%Q],
     [toQDEP 1.435%Q, toQDEP 1.230%Q]].

Definition example5_biases2: matrix 2 1 :=
    [[toQDEP 0.601%Q], [toQDEP 0.072%Q]].

Definition example5_weights3: matrix (T:=Q_RSOPMD) 1 2 :=
    [[toQDEP 1.881%Q, toQDEP 1.929%Q]].

Definition example5_biases3: matrix 1 1 :=
    [[toQDEP 0.905%Q]].

Definition example_nn5 := 
    (NNLinear example5_weights1 example5_biases1 
    (NNReLU
    (NNLinear example5_weights2 example5_biases2
    (NNReLU
    (NNLinear example5_weights3 example5_biases3 
    (NNReLU
    (NNOutput (output_dim:=1)))))))).

(* Time Compute (verify_hyperporperty example_nn5 NNDH_monotonicity_1d). *)

End FiveActivations.

(* -------------------------------------------------------------------------------- *)

Section SixActivations.

Definition example6_weights1: matrix (T:=Q_RSOPMD) 3 1 :=
    [[toQDEP 1.065%Q], [toQDEP 1.185%Q], [toQDEP 1.693%Q]].

Definition example6_biases1: matrix 3 1 :=
    [[toQDEP 0.949%Q], [toQDEP 0.091%Q], [toQDEP 0.197%Q]].

Definition example6_weights2: matrix (T:=Q_RSOPMD) 2 3 :=
    [[toQDEP 1.148%Q, toQDEP 1.354%Q, toQDEP 1.690%Q],
     [toQDEP 1.702%Q, toQDEP 1.846%Q, toQDEP 1.108%Q]].

Definition example6_biases2: matrix 2 1 :=
    [[toQDEP 0.601%Q], [toQDEP 0.072%Q]].

Definition example6_weights3: matrix (T:=Q_RSOPMD) 1 2 :=
    [[toQDEP 1.224%Q, toQDEP 1.697%Q]].

Definition example6_biases3: matrix 1 1 :=
    [[toQDEP 0.031%Q]].

Definition example_nn6 := 
    (NNLinear example6_weights1 example6_biases1 
    (NNReLU
    (NNLinear example6_weights2 example6_biases2
    (NNReLU
    (NNLinear example6_weights3 example6_biases3 
    (NNReLU
    (NNOutput (output_dim:=1)))))))).

(* Time Compute (verify_hyperporperty example_nn6 NNDH_monotonicity_1d). *)

End SixActivations.

(* -------------------------------------------------------------------------------- *)

Section SevenActivations.

Definition example7_weights1: matrix (T:=Q_RSOPMD) 3 1 :=
    [[toQDEP 1.294%Q], [toQDEP 1.854%Q], [toQDEP 1.394%Q]].

Definition example7_biases1: matrix 3 1 :=
    [[toQDEP 0.087%Q], [toQDEP 0.703%Q], [toQDEP 0.327%Q]].

Definition example7_weights2: matrix (T:=Q_RSOPMD) 3 3 :=
    [[toQDEP 1.175%Q, toQDEP 1.195%Q, toQDEP 1.885%Q],
     [toQDEP 1.659%Q, toQDEP 1.213%Q, toQDEP 1.064%Q],
     [toQDEP 1.852%Q, toQDEP 1.970%Q, toQDEP 1.168%Q]].

Definition example7_biases2: matrix 3 1 :=
    [[toQDEP 0.333%Q], [toQDEP 0.579%Q], [toQDEP 0.780%Q]].

Definition example7_weights3: matrix (T:=Q_RSOPMD) 1 3 :=
    [[toQDEP 1.898%Q, toQDEP 1.033%Q, toQDEP 1.708%Q]].

Definition example7_biases3: matrix 1 1 :=
    [[toQDEP 0.731%Q]].

Definition example_nn7 := 
    (NNLinear example7_weights1 example7_biases1 
    (NNReLU
    (NNLinear example7_weights2 example7_biases2
    (NNReLU
    (NNLinear example7_weights3 example7_biases3 
    (NNReLU
    (NNOutput (output_dim:=1)))))))).

(* Time Compute (verify_hyperporperty example_nn7 NNDH_monotonicity_1d). *)

End SevenActivations.

(* -------------------------------------------------------------------------------- *)

Section EightActivations.

Definition example8_weights1: matrix (T:=Q_RSOPMD) 4 1 :=
    [[toQDEP 1.018%Q], [toQDEP 1.937%Q], [toQDEP 1.693%Q], [toQDEP 1.631%Q]].

Definition example8_biases1: matrix 4 1 :=
    [[toQDEP 0.551%Q], [toQDEP 0.096%Q], [toQDEP 0.278%Q], [toQDEP 0.916%Q]].

Definition example8_weights2: matrix (T:=Q_RSOPMD) 3 4 :=
    [[toQDEP 1.317%Q, toQDEP 1.840%Q, toQDEP 1.544%Q, toQDEP 1.693%Q],
     [toQDEP 1.043%Q, toQDEP 1.639%Q, toQDEP 1.772%Q, toQDEP 1.215%Q],
     [toQDEP 1.169%Q, toQDEP 1.842%Q, toQDEP 1.555%Q, toQDEP 1.901%Q]].

Definition example8_biases2: matrix 3 1 :=
    [[toQDEP 0.374%Q], [toQDEP 0.035%Q], [toQDEP 0.754%Q]].

Definition example8_weights3: matrix (T:=Q_RSOPMD) 1 3 :=
    [[toQDEP 1.570%Q, toQDEP 1.977%Q, toQDEP 1.265%Q]].

Definition example8_biases3: matrix 1 1 :=
    [[toQDEP 0.626%Q]].

Definition example_nn8 := 
    (NNLinear example8_weights1 example8_biases1 
    (NNReLU
    (NNLinear example8_weights2 example8_biases2
    (NNReLU
    (NNLinear example8_weights3 example8_biases3 
    (NNReLU
    (NNOutput (output_dim:=1)))))))).

(* Time Compute (verify_hyperporperty example_nn8 NNDH_monotonicity_1d).*) 

End EightActivations.

(* -------------------------------------------------------------------------------- *)

Section NineActivations.

Definition example9_weights1: matrix (T:=Q_RSOPMD) 4 1 :=
    [[toQDEP 1.461%Q], [toQDEP 1.154%Q], [toQDEP 1.369%Q], [toQDEP 1.702%Q]].

Definition example9_biases1: matrix 4 1 :=
    [[toQDEP 0.022%Q], [toQDEP 0.332%Q], [toQDEP 0.572%Q], [toQDEP 0.399%Q]].

Definition example9_weights2: matrix (T:=Q_RSOPMD) 4 4 :=
    [[toQDEP 1.678%Q, toQDEP 1.094%Q, toQDEP 1.425%Q, toQDEP 1.778%Q],
     [toQDEP 1.135%Q, toQDEP 1.586%Q, toQDEP 1.696%Q, toQDEP 1.285%Q],
     [toQDEP 1.216%Q, toQDEP 1.837%Q, toQDEP 1.447%Q, toQDEP 1.253%Q],
     [toQDEP 1.685%Q, toQDEP 1.247%Q, toQDEP 1.792%Q, toQDEP 1.248%Q]].

Definition example9_biases2: matrix 4 1 :=
    [[toQDEP 0.631%Q], [toQDEP 0.601%Q], [toQDEP 0.559%Q], [toQDEP 0.259%Q]].

Definition example9_weights3: matrix (T:=Q_RSOPMD) 1 4 :=
    [[toQDEP 1.93%Q, toQDEP 1.065%Q, toQDEP 1.155%Q, toQDEP 1.790%Q]].

Definition example9_biases3: matrix 1 1 :=
    [[toQDEP 0.371%Q]].

Definition example_nn9 := 
    (NNLinear example9_weights1 example9_biases1 
    (NNReLU
    (NNLinear example9_weights2 example9_biases2
    (NNReLU
    (NNLinear example9_weights3 example9_biases3 
    (NNReLU
    (NNOutput (output_dim:=1)))))))).

(* Time Compute (verify_hyperporperty example_nn9 NNDH_monotonicity_1d).*) 

End NineActivations.

(* -------------------------------------------------------------------------------- *)

Section TenActivations.

Definition example10_weights1: matrix (T:=Q_RSOPMD) 5 1 :=
    [[toQDEP 1.855%Q], [toQDEP 1.711%Q], [toQDEP 1.750%Q], [toQDEP 1.048%Q], [toQDEP 1.598%Q]].

Definition example10_biases1: matrix 5 1 :=
    [[toQDEP 0.782%Q], [toQDEP 0.02%Q], [toQDEP 0.996%Q], [toQDEP 0.001%Q], [toQDEP 0.479%Q]].

Definition example10_weights2: matrix (T:=Q_RSOPMD) 4 5 :=
    [[toQDEP 1.564%Q, toQDEP 1.928%Q, toQDEP 1.881%Q, toQDEP 1.258%Q, toQDEP 1.866%Q],
     [toQDEP 1.896%Q, toQDEP 1.173%Q, toQDEP 1.337%Q, toQDEP 1.183%Q, toQDEP 1.562%Q],
     [toQDEP 1.235%Q, toQDEP 1.918%Q, toQDEP 1.151%Q, toQDEP 1.421%Q, toQDEP 1.272%Q],
     [toQDEP 1.348%Q, toQDEP 1.551%Q, toQDEP 1.505%Q, toQDEP 1.349%Q, toQDEP 1.265%Q]].

Definition example10_biases2: matrix 4 1 :=
    [[toQDEP 0.776%Q], [toQDEP 0.236%Q], [toQDEP 0.645%Q], [toQDEP 0.612%Q]].

Definition example10_weights3: matrix (T:=Q_RSOPMD) 1 4 :=
    [[toQDEP 1.962%Q, toQDEP 1.955%Q, toQDEP 1.630%Q, toQDEP 1.377%Q]].

Definition example10_biases3: matrix 1 1 :=
    [[toQDEP 0.437%Q]].

Definition example_nn10 := 
    (NNLinear example10_weights1 example10_biases1 
    (NNReLU
    (NNLinear example10_weights2 example10_biases2
    (NNReLU
    (NNLinear example10_weights3 example10_biases3 
    (NNReLU
    (NNOutput (output_dim:=1)))))))).

Time Eval vm_compute in (verify_hyperporperty example_nn10 NNDH_monotonicity_1d).

End TenActivations.