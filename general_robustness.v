(* Some abandoned development of general robustness *)

Section L_infty_metric.

Context {RSOAM : RealSubsetOAM}.
Import RealSubsetNotations.
Open Scope RSOAM_scope.

(*missin RSOAM Lemmas: *)
Lemma RSOAM_le_transitive:
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

Lemma RSOAM_opp_le_zero :
  forall (x : T RSOAM),
    x <= 0 = true <-> - x >= 0 = true.
Proof.
  intros x.
  split.
  - intro Hle.
    apply ax_real_leq_true.
    apply ax_real_leq_true in Hle.
    RSOAM_realize.
    rewrite ax_zero_is_zero in Hle.
    lra.
  - intro H.
    apply ax_real_leq_true.
    apply ax_real_leq_true in H.
    rewrite ax_zero_is_zero in *.
    rewrite ax_opp_is_opp in H.
    lra.
Qed.

Lemma RSOAM_zero_lt_opp :
  forall (x : T RSOAM),
    0 < x = true <-> -x < 0 = true.
Proof.
  intros x.
  split.
  - intro Hlt.
    unfold RSlt in *.
    destruct (RSOAM_le RSOAM 0 x) eqn:H1; try discriminate.
    destruct (RSOAM_le RSOAM x 0) eqn:H2; try discriminate.
    apply ax_real_leq_true in H1.
    apply ax_real_leq_false in H2.
    destruct (RSOAM_le RSOAM (- x) 0) eqn:H3.
    + destruct (RSOAM_le RSOAM 0 (- x)) eqn:H4.
      * apply ax_real_leq_true in H4.
        rewrite ax_zero_is_zero in *.
        rewrite ax_opp_is_opp in H4.
        lra.
      * reflexivity.
    + apply ax_real_leq_false in H3.
      rewrite ax_zero_is_zero in *.
      rewrite ax_opp_is_opp in H3.
      lra.
  - intro Hlt.
    unfold RSlt in *.
    destruct (RSOAM_le RSOAM (- x) 0) eqn:H1; try discriminate.
    destruct (RSOAM_le RSOAM 0 (- x)) eqn:H2; try discriminate.
    apply ax_real_leq_true in H1.
    apply ax_real_leq_false in H2.
    destruct (RSOAM_le RSOAM 0 x) eqn:H3.
    + destruct (RSOAM_le RSOAM x 0) eqn:H4.
      * apply ax_real_leq_true in H4.
        rewrite ax_zero_is_zero in *.
        rewrite ax_opp_is_opp in H1.
        apply ax_real_leq_true in H3.
        rewrite ax_zero_is_zero in H3.
        assert (INJ_RSOAM RSOAM x = 0)%R as Heq.
        { apply Rle_antisym. apply H4. apply H3. }
        rewrite ax_opp_is_opp in H2.
        rewrite Heq in H2.
        exfalso; lra.
      * reflexivity.
    + apply ax_real_leq_false in H3.
      rewrite ax_zero_is_zero in *.
      rewrite ax_opp_is_opp in H1.
      lra.
Qed.

Lemma RSOAM_opp_lt_zero {RSOAM: RealSubsetOAM}:
  forall (x : T RSOAM),
    x < 0 = true <-> - x > 0 = true.
Proof.
  intros x.
  split.
  - intro Hlt.
    unfold RSgt, RSlt.
    unfold RSlt in Hlt.
    destruct (RSOAM_le RSOAM x 0) eqn:H1; try discriminate.
    destruct (RSOAM_le RSOAM 0 x) eqn:H2; try discriminate.
    apply ax_real_leq_true in H1.
    apply ax_real_leq_false in H2.
    destruct (RSOAM_le RSOAM 0 (- x)) eqn:H3.
    + destruct (RSOAM_le RSOAM (- x) 0) eqn:H4.
      * apply ax_real_leq_true in H4.
        rewrite ax_zero_is_zero in *.
        rewrite ax_opp_is_opp in H4.
        lra.
      * reflexivity.
    + apply ax_real_leq_false in H3.
      rewrite ax_zero_is_zero in *.
      rewrite ax_opp_is_opp in H3.
      lra.
  - intro Hgt.
    unfold RSlt.
    unfold RSgt, RSlt in Hgt.
    destruct (RSOAM_le RSOAM 0 (- x)) eqn:H1; try discriminate.
    destruct (RSOAM_le RSOAM (- x) 0) eqn:H2; try discriminate.
    apply ax_real_leq_true in H1.
    apply ax_real_leq_false in H2.
    destruct (RSOAM_le RSOAM x 0) eqn:H3.
    + destruct (RSOAM_le RSOAM 0 x) eqn:H4.
      * apply ax_real_leq_true in H4.
        rewrite ax_zero_is_zero in *.
        rewrite ax_opp_is_opp in H1.
        apply ax_real_leq_true in H3.
        rewrite ax_zero_is_zero in H3.
        assert (INJ_RSOAM RSOAM x = 0)%R as Heq.
        { apply Rle_antisym. apply H3. apply H4. }
        rewrite ax_opp_is_opp in H2.
        rewrite Heq in H2.
        exfalso; lra.
      * reflexivity.
    + apply ax_real_leq_false in H3.
      rewrite ax_zero_is_zero in *.
      rewrite ax_opp_is_opp in H1.
      lra.
Qed.

(* Following https://arxiv.org/abs/2306.12495 *)

Definition colvec_entry_sum {n: nat} (v1 v2: colvec n) (i:nat) : RS :=
    coeff_colvec (RSOAM:= RSOAM)RSzero v1 i + coeff_colvec (RSOAM:= RSOAM)RSzero v2 i.

Definition colvec_entry_sub {n: nat} (v1 v2: colvec n) (i:nat) : RS :=
    coeff_colvec (RSOAM:= RSOAM)RSzero v1 i + - coeff_colvec (RSOAM:= RSOAM)RSzero v2 i.

Definition colvec_sub {n: nat} (v1 v2: colvec n) : colvec n :=
  mk_colvec (RSOAM:=RSOAM) n (fun i => colvec_entry_sub v1 v2 i).

Fixpoint colvec_max {n: nat} (v: colvec n) : RS :=
  match n as n0 return colvec n0 -> RS with
  | O => fun _ => RSzero
  | S n' => fun v =>
    let head := coeff_colvec (RSOAM:=RSOAM) RSzero v O in
    let tail := mk_colvec (RSOAM:=RSOAM) n'
      (fun i => coeff_colvec (RSOAM:=RSOAM) RSzero v (S i)) in
    let tail_max := colvec_max tail in
    if RSOAM_le RSOAM head tail_max then tail_max else head
  end v.

Definition RSOAM_abs (x: T RSOAM) : T RSOAM :=
    if RSOAM_le RSOAM x 0 then - x else x.

Definition L_infty_metric {n: nat} (v1 v2: colvec n) : RS :=
  colvec_max (mk_colvec (RSOAM:=RSOAM) n
    (fun i => RSOAM_abs (colvec_entry_sub v1 v2 i))).

End L_infty_metric.


(*multi-dimensional variant? *)
Definition is_robust {in_dim out_dim : nat}
  (nn : TPWANNSequential (RSOAM:=Q_RSOAMD)
         (input_dim:=in_dim) (output_dim:=out_dim))
  (epsilon delta : Q_RSOAMD) : Prop :=
  forall (x1 x2 : colvec in_dim),
    L_infty_metric (RSOAM:=Q_RSOAMD) x1 x2 <= delta = true ->
    L_infty_metric (RSOAM:=Q_RSOAMD)
      (nn_eval (RSOAM:=Q_RSOAMD) (in_dim:=in_dim) (out_dim:=out_dim) nn x1)
      (nn_eval (RSOAM:=Q_RSOAMD) (in_dim:=in_dim) (out_dim:=out_dim) nn x2)
      <= epsilon = true.