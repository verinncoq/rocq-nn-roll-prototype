Require Import Coquelicot.Coquelicot.
From Verinncoq Require Import piecewise_affine.
From Verinncoq Require Import pwaf_operations.
From Verinncoq Require Import neuron_functions.
From Verinncoq Require Import neural_networks.
From Verinncoq Require Import matrix_extensions.
From Verinncoq Require Import real_subsets.
From Coq Require Import Nat Reals List Arith Lia Lra.
Require Import Coq.Lists.List.
Import ListNotations.
Import RealSubsetNotations.

Import MatrixNotations.

Open Scope colvec_scope.
Open Scope matrix_scope.

Section NeuralNetworkDefinedHyperproperties.

Context {RSOPM : RealSubsetOPM}.
Open Scope RSOPM_scope.

(** Neural network hyperproperty *)

Inductive NNHyperproperty {nn_in_dim nn_out_dim : nat} :=
  | NNDH 
      (r w : nat)
      (W : ConvexPolyhedron (RSOPM:=RSOPM) w)
      (netIn : TPWAF (RSOPM:=RSOPM) (in_dim:=w) (out_dim:=r * nn_in_dim))
      (netSat : TPWAF (RSOPM:=RSOPM) 
        (in_dim:=(r * nn_in_dim) + (r * nn_out_dim)) (out_dim:=1)).

(** Semantics over a neural network *)

Definition toRS (c: colvec 1): T RSOPM := coeff_colvec 0 c 0.

Fixpoint eval_nn_multiple {r} {nn_in_dim nn_out_dim: nat}
  (nn: TPWANNSequential (output_dim:=nn_out_dim))
  (inputs: colvec (r * nn_in_dim))
  : colvec (RSOPM:=RSOPM) (r * nn_out_dim) :=
  match r with
  | 0 => null_vector (0 * nn_out_dim)
  | S n => 
    let input := mk_colvec nn_in_dim (fun i => coeff_colvec RSzero inputs i) in
    let next  := mk_colvec (n * nn_in_dim) (fun i => coeff_colvec RSzero inputs (i + nn_in_dim)) in
      (colvec_concat (nn_eval nn input) (eval_nn_multiple nn next))
  end.

Definition nn_satisfies_nndh {nn_in_dim nn_out_dim: nat} 
  (nn: TPWANNSequential (input_dim:=nn_in_dim) (output_dim:=nn_out_dim)) 
  (nndh: NNHyperproperty) 
  : Prop 
  :=
  match nndh with 
  | NNDH r w W netIn netSat =>
    forall (x: colvec (RSOPM:=RSOPM) w), in_convex_polyhedron x W -> 
      let input_set := tpwaf_eval netIn x in 
      let output_set := eval_nn_multiple nn input_set in
        0 <= toRS (tpwaf_eval netSat (colvec_concat input_set output_set)) = true
  end.

(** Semantics over a PWAF *)

Lemma repeat_concat_helper {m n}:
    PWAF (RSOPM:=RSOPM) (in_dim:= 0) (out_dim:=0) -> 
    PWAF (RSOPM:=RSOPM) (in_dim := 0 * m) (out_dim:=0 * n).
Proof.
  intros H; apply H.
Defined.

Fixpoint repeat_concat {pwaf_in_dim pwaf_out_dim: nat}
  (times: nat) 
  (pwaf: PWAF (in_dim:=pwaf_in_dim) (out_dim:=pwaf_out_dim))
  : PWAF (in_dim:=times * pwaf_in_dim) (out_dim:=times * pwaf_out_dim) :=
  match times with
  | 0 => repeat_concat_helper ZeroDimPWAF
  | S n => (pwaf_concat pwaf (repeat_concat n pwaf))
  end.

Definition nndh_full_pwaf_helper {pwaf_in_dim pwaf_out_dim r w: nat}
  (netIn: PWAF (in_dim:=w)) 
  (netSat: PWAF (out_dim:=1))
  (pwaf: PWAF (RSOPM:=RSOPM) (in_dim:=pwaf_in_dim) (out_dim:=pwaf_out_dim))
  : PWAF
  :=
  pwaf_compose netSat (pwaf_concat netIn
    (pwaf_compose (repeat_concat r pwaf) netIn)).

Definition pwaf_satisfies_nndh {pwaf_in_dim pwaf_out_dim: nat}
  (pwaf: PWAF (in_dim:=pwaf_in_dim) (out_dim:=pwaf_out_dim))
  (nndh: NNHyperproperty)
  : Prop 
  :=
  match nndh with
  | NNDH r w W netIn netSat =>
    forall (x: colvec (RSOPM:=RSOPM) w), in_convex_polyhedron x W ->
      let full_pwaf := 
        pwaf_compose netSat
          (pwaf_concat netIn
            (pwaf_compose (repeat_concat r pwaf) netIn)) in
      match pwaf_eval full_pwaf (colvec_concat x x) with
      | Some r => 0 <= toRS r = true
      | None => True
      end
  end.

End NeuralNetworkDefinedHyperproperties.

Section NNHyperpropertySemanticsRelationships.

Context {RSOPM : RealSubsetOPM}.
Open Scope RSOPM_scope.

(** Relationship between hyperproperties on NNs and PWAFs *)

Lemma pwaf_tpwaf_compose {in_dim hidden_dim out_dim: nat}:
  forall
    (f: TPWAF (RSOPM:=RSOPM) (in_dim:=hidden_dim) (out_dim:=out_dim))
    (g: TPWAF (in_dim:=in_dim) (out_dim:=hidden_dim)),
      pwaf_compose f g = tpwaf_compose f g.
Proof.
  intros f g; unfold tpwaf_compose, TPWAF2PWAF; reflexivity.
Qed.

Lemma pwaf_tpwaf_concat {in_dim1 in_dim2 out_dim1 out_dim2: nat}:
  forall
    (f: TPWAF (RSOPM:=RSOPM) (in_dim:=in_dim1) (out_dim:=out_dim1))
    (g: TPWAF (in_dim:=in_dim2) (out_dim:=out_dim2)),
      pwaf_concat f g = tpwaf_concat f g.
Proof.
  intros f g; unfold tpwaf_concat, TPWAF2PWAF; reflexivity.
Qed.

Lemma repeat_concat_total_helper:
  forall m n, 
    TPWAF (RSOPM:=RSOPM) (in_dim:= 0) (out_dim:=0) -> 
    TPWAF (RSOPM:=RSOPM) (in_dim := 0 * m) (out_dim:=0 * n).
Proof.
  intros m n H. do 2 unfold Nat.mul. apply H.
Defined.

Fixpoint repeat_concat_total {pwaf_in_dim pwaf_out_dim: nat}
  (times: nat) 
  (pwaf: TPWAF (in_dim:=pwaf_in_dim) (out_dim:=pwaf_out_dim))
  : TPWAF (in_dim:=times * pwaf_in_dim) (out_dim:=times * pwaf_out_dim) :=
  match times with
  | 0 => repeat_concat_total_helper _ _ ZeroDimTPWAF
  | S n => (tpwaf_concat pwaf (repeat_concat_total n pwaf))
  end.

Lemma repeat_concat_total_correct {pwaf_in_dim pwaf_out_dim: nat}:
  forall times (tpwaf: TPWAF (in_dim:=pwaf_in_dim) (out_dim:=pwaf_out_dim)),
    repeat_concat times tpwaf = repeat_concat_total times tpwaf.
Proof.
  intros times tpwaf; induction times.
  * unfold repeat_concat, repeat_concat_total; reflexivity.
  * unfold repeat_concat, repeat_concat_total.
    fold (repeat_concat times tpwaf); fold (repeat_concat_total times tpwaf).
    rewrite IHtimes.
    unfold tpwaf_concat, TPWAF2PWAF; reflexivity.
Qed.

Lemma tpwaf_eval_is_value {in_dim out_dim}:
  forall (f: TPWAF (RSOPM:=RSOPM) (in_dim:=in_dim) (out_dim:=out_dim)) x fx, 
  is_pwaf_value f x fx <-> tpwaf_eval f x = fx.
Proof.
  intros f x fx.
  split; intro H.
  * pose proof (tpwaf_eval_correct _ _ f x) as Hc.
    apply pwaf_eval_correct in Hc.
    apply pwaf_eval_correct in H.
    rewrite H in Hc.
    symmetry in Hc.
    injection Hc; easy.
  * rewrite <- H.
    apply tpwaf_eval_correct.
Qed.

Lemma tpwaf_eval_concat {in_dim1 in_dim2 out_dim1 out_dim2}:
  forall 
    (tpwaf1: TPWAF (RSOPM:=RSOPM) (in_dim:=in_dim1) (out_dim:=out_dim1)) 
    (tpwaf2: TPWAF (in_dim:=in_dim2) (out_dim:=out_dim2)) x1 x2,
    tpwaf_eval (tpwaf_concat tpwaf1 tpwaf2) (colvec_concat x1 x2) =
      colvec_concat (tpwaf_eval tpwaf1 x1) (tpwaf_eval tpwaf2 x2).
Proof.
  intros tpwaf1 tpwaf2 x1 x2.
  apply tpwaf_eval_is_value.
  apply tpwaf_concat_correct; apply tpwaf_eval_correct.
Qed.

Lemma tpwaf_eval_compose {in_dim hid_dim out_dim}:
  forall 
    (x: colvec in_dim) 
    (f: TPWAF (in_dim:=hid_dim) (out_dim:=out_dim))
    (g: TPWAF (in_dim:=in_dim) (out_dim:=hid_dim)),
      tpwaf_eval (tpwaf_compose (RSOPM:=RSOPM) f g) x = 
      tpwaf_eval f (tpwaf_eval g x).
Proof.
  intros x f g.
  apply tpwaf_eval_is_value. 
  unfold tpwaf_compose.
  apply (pwaf_compose_correct _ _ _ _ _ (tpwaf_eval g x)). 
  apply tpwaf_eval_correct.
  apply tpwaf_eval_correct.
Qed.

Lemma repeat_concat_total_is_eval_multiple_nn {in_dim out_dim}:
  forall
    (nn: TPWANNSequential (RSOPM:=RSOPM) (input_dim:=in_dim) (output_dim:=out_dim))
    nn_asd r x,
    nn_asd = asd nn ->
    tpwaf_eval (repeat_concat_total r nn_asd) x = eval_nn_multiple nn x.
Proof.
  intros nn nn_asd r x Hasd.
  induction r.
  * unfold repeat_concat_total, repeat_concat_total_helper, eval_nn_multiple.
    unfold Nat.mul. 
    apply unique_colvec_0.
  * unfold repeat_concat_total; fold (repeat_concat_total r nn_asd).
    unfold eval_nn_multiple; fold (eval_nn_multiple nn (mk_colvec (r * in_dim) (fun i : nat => coeff_colvec 0 x (i + in_dim)))).
    rewrite <- tpwaf_eval_is_value.
    pose proof (colvec_split in_dim (r * in_dim) x) as Hsplit.
    destruct Hsplit as [x1 [x2 [Hx1 [Hx2 Hxdef]]]].
    rewrite Hxdef at 1.
    apply tpwaf_concat_correct.
    - rewrite Hx1.
      apply (asd_correct _ _ _ _ nn nn_asd); last reflexivity.
      apply Hasd.
    - specialize (IHr (mk_colvec (r * in_dim) (fun i : nat => coeff_colvec 0 x (i + in_dim)))).
      rewrite Hx2.
      apply tpwaf_eval_is_value in IHr.
      apply IHr.
Qed.

Theorem asd_preserves_satisfiability {in_dim out_dim: nat}:
  forall 
    (nn: TPWANNSequential (RSOPM:=RSOPM) (input_dim:=in_dim) (output_dim:=out_dim)) 
    nndh nn_asd,
    nn_asd = asd nn ->
    (nn_satisfies_nndh nn nndh <-> pwaf_satisfies_nndh nn_asd nndh).
Proof.
  intros nn nndh nn_asd Hasd.
  destruct nndh as [r w W netIn netSat].
  unfold pwaf_satisfies_nndh, nn_satisfies_nndh.
  rewrite repeat_concat_total_correct.
  rewrite pwaf_tpwaf_compose.
  rewrite pwaf_tpwaf_concat.
  rewrite pwaf_tpwaf_compose.
  split; intros H x HxIn; specialize (H x HxIn).
  * destruct (pwaf_eval _ _) eqn:Heval; try (exact I).
    rewrite <- H; do 2 f_equal.
    symmetry; apply is_pwaf_value_tpwaf_eval.
    apply pwaf_eval_correct in Heval.
    apply tpwaf_compose_reverse_value in Heval.
    destruct Heval as [Heval1 Heval2].
    rewrite tpwaf_eval_concat in Heval2.
    rewrite tpwaf_eval_compose in Heval2.
    rewrite (repeat_concat_total_is_eval_multiple_nn nn) in Heval2.
    apply Heval2. apply Hasd.
  * destruct (pwaf_eval _ _) eqn:Heval.
    - rewrite <- H; do 2 f_equal.
      apply is_pwaf_value_tpwaf_eval.
      apply pwaf_eval_correct in Heval.
      apply tpwaf_compose_reverse_value in Heval.
      destruct Heval as [Heval1 Heval2].
      rewrite tpwaf_eval_concat in Heval2.
      rewrite tpwaf_eval_compose in Heval2.
      rewrite (repeat_concat_total_is_eval_multiple_nn nn) in Heval2.
      apply Heval2. apply Hasd.
    - apply tpwaf_pwaf_eval_never_none in Heval; contradiction.
Qed.  

End NNHyperpropertySemanticsRelationships.

Section NNHyperpropertyComponentSplit.

Context {RSOPM : RealSubsetOPM}.
Open Scope RSOPM_scope.

(** Verification of a hypeproperty over individual affine segments *)

Definition satisfaction_over_segment {w: nat}
  (affine_seg: AffineSegment (RSOPM:=RSOPM) (w + w) 1)
  (W: ConvexPolyhedron w)
  : Prop
  := 
  forall x, in_convex_polyhedron x W ->
    match affine_segment_eval affine_seg (colvec_concat x x) with
    | Some r => 0 <= toRS r = true
    | None => True
    end.

Definition nndh_pwaf_segment_split {pwaf_in_dim pwaf_out_dim: nat}
  (pwaf: PWAF (in_dim:=pwaf_in_dim) (out_dim:=pwaf_out_dim))
  (nndh: NNHyperproperty)
  : Prop 
  :=
  match nndh with
  | NNDH r w W netIn netSat =>
      let full_pwaf := 
        pwaf_compose netSat
          (pwaf_concat netIn
            (pwaf_compose (repeat_concat r pwaf) netIn)) in
      forall body_seg, In body_seg (body full_pwaf) ->
        satisfaction_over_segment body_seg W
  end.

Theorem pwaf_satisfiability_segments_split {in_dim out_dim}:
  forall nndh (pwaf: PWAF (RSOPM:=RSOPM) (in_dim:=in_dim) (out_dim:=out_dim)),
    pwaf_satisfies_nndh pwaf nndh <-> nndh_pwaf_segment_split pwaf nndh.
Proof.
  intros nndh pwaf.
  destruct nndh as [r w W netIn netSat].
  unfold nndh_pwaf_segment_split, pwaf_satisfies_nndh.
  split; intro H.
  * intros body_el Hbody_el.
    unfold satisfaction_over_segment.
    intros x Hx.
    specialize (H x Hx).
    pose proof ((prop (pwaf_compose netSat
                  (pwaf_concat netIn
                    (pwaf_compose (repeat_concat r pwaf) netIn))))) as Huni.
    destruct (pwaf_eval _ _) eqn:Heval.
    - apply pwaf_eval_correct in Heval.
      unfold is_pwaf_value in Heval.
      destruct Heval as [eval_body_el [Heval_body_el Hseg_val]].
      unfold pwaf_univalence, ForallPairs in Huni.
      specialize (Huni body_el eval_body_el Hbody_el Heval_body_el
                  (colvec_concat x x)).
      remember (affine_segment_eval body_el _) as body_seg_val.
      destruct body_seg_val as [val|]; last (exact I).
      symmetry in Heqbody_seg_val. 
      apply affine_segment_eval_correct in Heqbody_seg_val.
      assert (Hdomains: 
                in_affine_segment_domain body_el (colvec_concat x x) /\
                in_affine_segment_domain eval_body_el (colvec_concat x x)). {
                  split.
                  * unfold is_affine_segment_value in Heqbody_seg_val.
                    destruct Heqbody_seg_val as [Hdom _].
                    apply Hdom.
                  * unfold is_affine_segment_value in Hseg_val.
                    destruct Hseg_val as [Hdom _].
                    apply Hdom.
                }
      specialize (Huni Hdomains).
      apply affine_segment_eval_correct in Hseg_val.
      rewrite Hseg_val in Huni.
      inversion Huni.
      apply H.
    - remember (affine_segment_eval body_el _) as body_seg_val.
      destruct body_seg_val as [val|]; last (exact I).
      assert (Hcontra: is_pwaf_value 
                        (pwaf_compose netSat 
                          (pwaf_concat netIn 
                            (pwaf_compose (repeat_concat r pwaf) netIn)))
                        (colvec_concat x x) val). {
                          unfold is_pwaf_value.
                          exists body_el.
                          split.
                          * apply Hbody_el.
                          * apply affine_segment_eval_correct.
                            rewrite Heqbody_seg_val; reflexivity.
                        }
      apply pwaf_eval_correct in Hcontra.
      rewrite Hcontra in Heval.
      inversion Heval.
  * intros x Hx.
    destruct (pwaf_eval _ _) eqn:Heval; last (exact I).
    apply pwaf_eval_correct in Heval.
    unfold is_pwaf_value in Heval.
    destruct Heval as [body_el [Hbody_el Hval]].
    specialize (H body_el Hbody_el).
    unfold satisfaction_over_segment in H.
    specialize (H x Hx).
    apply affine_segment_eval_correct in Hval.
    rewrite Hval in H.
    apply H.
Qed.

End NNHyperpropertyComponentSplit.
