From Coq Require Import List Reals Lia Lra Bool Logic Classical_Prop Classical_Pred_Type.
Import ListNotations.

From Verinncoq Require Import real_subsets.
Import RealSubsetNotations.

Section RealSubsetsDivision.

Record RSOPMWithDiv := Build_RSOPMD {
   RSOPM :> RealSubsetOPM;
   RSOPM_div: (T RSOPM) -> (T RSOPM) -> (T RSOPM);
   ax_real_div: forall (x y: T RSOPM),
      INJ_RSOPM RSOPM (RSOPM_div x y) = Rdiv (INJ_RSOPM RSOPM x) 
        (INJ_RSOPM RSOPM y);
}.

End RealSubsetsDivision.

Section FourierMotzkinImplementation.

Context { RSOPM : RSOPMWithDiv }.
Open Scope RSOPM_scope.

Definition RSdiv {RSOPM: RSOPMWithDiv} := RSOPM_div RSOPM.
Infix "/" := RSdiv : RSOPM_scope.

(* Linear inequality in form 
    c_1 * x_1 + c_2 * x_2 + ... + c_n * x_n + b <= 0 
   is represented as a function from index of a variable
   to its associated coefficient. Zero is mapped to b.
   The parameter n refers to x_n, the variable with the largest index. *)
Definition LinearInequality (n: nat) := nat -> T RSOPM. 
Definition LinearSystem (n: nat) := list (LinearInequality n).
Definition LinearSystemSolution (n: nat) := nat -> T RSOPM.

Fixpoint interpret_inequality_helper {n: nat} 
    (ineq: LinearInequality n)
    (sol: LinearSystemSolution n)
    : T RSOPM :=
    match n with
    | 0 => ineq 0%nat
    | S i => (ineq n) * (sol n) + interpret_inequality_helper (n:=i) ineq sol
    end.

Lemma interpret_inequality_helper_plus:
  forall n (ineq1 ineq2: LinearInequality n) sol,
    interpret_inequality_helper ineq1 sol + interpret_inequality_helper ineq2 sol =
    interpret_inequality_helper (fun i => ineq1 i + ineq2 i) sol.
Proof.
  intros n ineq1 ineq2 sol.
  induction n.
  * unfold interpret_inequality_helper.
    RSOPM_realize_eq.
    rewrite Rplus_comm. reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
    specialize (IHn ineq1 ineq2 sol).
    rewrite <- IHn.
    RSOPM_realize_eq.
    lra.
Qed.

Lemma interpret_inequality_helper_div:
  forall n (ineq: LinearInequality n) c sol,
    interpret_inequality_helper ineq sol / c = interpret_inequality_helper (fun i => ineq i / c) sol.
Proof.
  intros n ineq c sol.
  induction n.
  * unfold interpret_inequality_helper.
    RSOPM_realize_eq.
    repeat rewrite ax_real_div.
    apply Rdiv_eq_compat_r; reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
    specialize (IHn ineq sol).
    rewrite <- IHn.
    RSOPM_realize_eq.
    repeat (RSOPM_realize; rewrite ax_real_div).
    lra.
Qed.

Definition interpret_inequality {n: nat} 
    (ineq: LinearInequality n) 
    (sol: LinearSystemSolution n)
    : Prop :=
    ((interpret_inequality_helper (n:=n) ineq sol <= 0) = true).

Lemma interpret_inequality_first_zero:
  forall n (ineq: LinearInequality (S n)) sol,
    ineq (S n) = 0 ->
    interpret_inequality (n:=S n) ineq sol ->
    interpret_inequality (n:=n) ineq sol.
Proof.
  intros n ineq sol H0 H.
  unfold interpret_inequality, interpret_inequality_helper in H; fold (interpret_inequality_helper (n:=n)) in H.
  rewrite H0 in H.
  apply ax_real_leq_true in H.
  rewrite ax_real_plus, ax_real_mult, ax_zero_is_zero in H.
  rewrite Rmult_0_l, Rplus_0_l in H.
  apply ax_real_leq_true; rewrite ax_zero_is_zero.
  apply H.
Qed.

Lemma interpet_inequality_plus:
  forall n (ineq1 ineq2: LinearInequality n) sol,
    interpret_inequality ineq1 sol ->
    interpret_inequality ineq2 sol ->
    interpret_inequality (fun i => ineq1 i + ineq2 i) sol.
Proof.
  intros n ineq1 ineq2 sol Hineq1 Hineq2.
  unfold interpret_inequality. unfold interpret_inequality in Hineq1, Hineq2.
  rewrite <- interpret_inequality_helper_plus.
  apply ax_real_leq_true; apply ax_real_leq_true in Hineq1, Hineq2.
  rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hineq1, Hineq2.
  rewrite ax_real_plus; lra.
Qed.

Lemma interpret_inequality_div:
  forall n (ineq: LinearInequality n) c sol,
    (c <= 0) = false ->
    interpret_inequality ineq sol ->
    interpret_inequality (fun i => ineq i / c) sol.
Proof.
  intros n ineq c sol Hc H.
  unfold interpret_inequality.
  rewrite <- interpret_inequality_helper_div.
  unfold interpret_inequality in H.
  apply ax_real_leq_true. rewrite ax_real_div.
  apply ax_real_leq_false in Hc.
  apply ax_real_leq_true in H.
  rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hc, H.
  unfold Rle. unfold Rle in H.
  destruct H as [H|H].
  - left. apply Rdiv_neg_pos; lra.
  - right. nra.
Qed.

Lemma interpret_inequality_compose:
  forall n (ineq1 ineq2: LinearInequality (S n)) sol,
      (0 <= ineq1 (S n)) = false ->
      (ineq2 (S n) <= 0) = false ->
      interpret_inequality (n:= S n) ineq1 sol ->
      interpret_inequality (n:= S n) ineq2 sol ->
      interpret_inequality (n:=n) (fun i: nat => ineq1 i / (RSopp (ineq1 (S n))) + (ineq2 i / ineq2 (S n))) sol.
Proof.
  intros n ineq1 ineq2 sol Hineq1 Hineq2 Hineq1_sol Hineq2_sol.
  apply interpret_inequality_first_zero.
  - apply ax_equality; rewrite ax_zero_is_zero.
    rewrite ax_real_plus, ax_real_div, ax_real_div, ax_opp_is_opp.
    apply ax_real_leq_false in Hineq1, Hineq2.
    rewrite ax_zero_is_zero in Hineq1, Hineq2.
    rewrite Rdiv_diag; last lra. 
    rewrite Rdiv_opp_r, Rdiv_diag; last lra.
    rewrite Rplus_opp_l; reflexivity.
  - apply interpet_inequality_plus.
    * apply interpret_inequality_div.
      - apply ax_real_leq_false; apply ax_real_leq_false in Hineq1.
        rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hineq1.
        rewrite ax_opp_is_opp; lra.
      - apply Hineq1_sol. 
    * apply interpret_inequality_div.
      - apply Hineq2.
      - apply Hineq2_sol.
Qed.

Fixpoint interpret_inequalities {n :nat} 
    (sys: LinearSystem n) 
    (sol: LinearSystemSolution n)
    : Prop :=
    match sys with
    | nil => True
    | ineq :: tail => interpret_inequality ineq sol /\ 
                        interpret_inequalities tail sol
    end.

Lemma interpret_inequalities_cons:
    forall n (ineq: LinearInequality n) 
        (sys: LinearSystem n) (sol: LinearSystemSolution n),
        (interpret_inequalities [ineq] sol /\ interpret_inequalities sys sol) <->
        interpret_inequalities (ineq :: sys) sol.
Proof.
    intros n ineq sys sol.
    split.
    * intro H; destruct H as [Hhead Htail].
      unfold interpret_inequalities.
      split.
      - apply Hhead.
      - apply Htail.
    * unfold interpret_inequalities.
      intro H; split.
      - split; first apply H; last easy.
      - apply H.
Qed.

Lemma interpret_inequalities_app:
    forall n (sys1: LinearSystem n) sys2 sol,
      interpret_inequalities sys1 sol /\ interpret_inequalities sys2 sol <->
      interpret_inequalities (sys1 ++ sys2) sol.
Proof.
    intros n sys1 sys2 sol.
    induction sys1.
    * simpl; easy.
    * rewrite <- app_comm_cons.
      unfold interpret_inequalities; fold (interpret_inequalities (n:=n)).
      split; intro H.
      - split.
        * apply H.
        * apply IHsys1.
          split; apply H.
      - split; try split.
        * apply H.
        * destruct H as [H1 H2].
          apply IHsys1 in H2.
          apply H2.
        * destruct H as [H1 H2].
          apply IHsys1 in H2.
          apply H2.
Qed.

Definition is_linear_system_solution {n: nat} 
    (sys: LinearSystem n) 
    (sol: LinearSystemSolution n)
    : Prop :=
    interpret_inequalities sys sol.

Lemma is_linear_system_solution_cons:
    forall n (ineq: LinearInequality n) 
        (sys: LinearSystem n) (sol: LinearSystemSolution n),
        (is_linear_system_solution [ineq] sol /\
        is_linear_system_solution sys sol) 
        <-> is_linear_system_solution (ineq :: sys) sol.
Proof.
    unfold is_linear_system_solution; apply interpret_inequalities_cons.
Qed.

Lemma no_linear_system_solution_cons:
    forall n (ineq: LinearInequality n) sys,
        (~ (exists sol, is_linear_system_solution sys sol)) ->
        (~ (exists sol, is_linear_system_solution (ineq :: sys) sol)).
Proof.
    intros n ineq sys H Hnot.
    destruct Hnot as [not_sol Hnot].
    apply is_linear_system_solution_cons in Hnot.
    destruct Hnot as [Hnot1 Hnot2].
    apply H.
    exists not_sol.
    apply Hnot2.
Qed.    

Lemma is_linear_system_solution_app:
    forall n (sys1 sys2: LinearSystem n) sol,
      is_linear_system_solution sys1 sol /\ is_linear_system_solution sys2 sol <->
      is_linear_system_solution (sys1 ++ sys2) sol.
Proof.
  intros n sys1 sys2 sol.
  unfold is_linear_system_solution.
  apply interpret_inequalities_app.
Qed.

Fixpoint trivial_consistency (sys: LinearSystem 0): bool :=
match sys with
| nil => true
| ineq :: tail => andb (ineq 0%nat <= 0) (trivial_consistency tail) 
end.

Lemma trivial_consistency_cons:
    forall n (ineq: LinearInequality n) sys,
        (trivial_consistency [ineq] = true /\ trivial_consistency sys = true) <->
        trivial_consistency (ineq :: sys) = true.
Proof.
    intros n ineq sys. 
    split.
    * intros H; destruct H as [Hhead Htail].
      unfold trivial_consistency.
      apply andb_true_intro; split.
      - unfold trivial_consistency in Hhead.
        rewrite Bool.andb_true_r in Hhead; apply Hhead.
      - apply Htail. 
    * intro H.
      unfold trivial_consistency in H.
      apply andb_prop in H.
      split; unfold trivial_consistency.
      - rewrite Bool.andb_true_r; apply H.  
      - apply H.
Qed.

Lemma trivial_consistency_andb:
    forall ineq sys,
    trivial_consistency (ineq :: sys) = 
        andb (trivial_consistency [ineq]) (trivial_consistency sys).
Proof.
    intros ineq sys.
    unfold trivial_consistency.
    rewrite Bool.andb_true_r.
    reflexivity.
Qed.

Lemma trivial_consistency_single_ineq:
    forall ineq sol,
        trivial_consistency [ineq] = true <-> 
        is_linear_system_solution [ineq] sol.
Proof.
    intros ineq sol.
    unfold trivial_consistency,
        is_linear_system_solution,interpret_inequalities,
        interpret_inequality,interpret_inequality_helper.
    rewrite Bool.andb_true_r.
    split; easy.
Qed.

Lemma trivial_consistency_correct:
    forall (sys: LinearSystem 0),
        if trivial_consistency sys
        then (forall sol, is_linear_system_solution sys sol)
        else ~ (exists sol, is_linear_system_solution sys sol).
Proof.
    intros sys.
    induction sys; first easy.
    rewrite trivial_consistency_andb.
    destruct (trivial_consistency [a]) eqn:Hcons_a.
    * rewrite Bool.andb_true_l.
      destruct (trivial_consistency sys) eqn:Hcons_sys.
      - intro sol.
        apply is_linear_system_solution_cons; split.
        * apply trivial_consistency_single_ineq.
          apply Hcons_a.  
        * apply (IHsys sol).
      - apply no_linear_system_solution_cons.
        apply IHsys.
    * unfold andb.
      intro Hcontra.
      destruct Hcontra as [not_sol Hnot_sol].
      apply is_linear_system_solution_cons in Hnot_sol.
      destruct Hnot_sol as [Hnot_sol1 Hnot_sol2].
      apply trivial_consistency_single_ineq in Hnot_sol1.
      rewrite Hcons_a in Hnot_sol1.
      discriminate.
Qed.

Definition partition_inequalities {n: nat} 
    (sys: LinearSystem n)
    : LinearSystem n * LinearSystem n * LinearSystem n :=
    let (le0, gt0) := partition (fun ineq => (ineq n) <= 0) sys in
    let (eq0, lt0) := partition (fun ineq => 0 <= (ineq n)) le0 in
    (lt0, eq0, gt0).

Lemma partition_inequalities_cons:
    forall n (ineq: LinearInequality n) sys,
        let (p_sys, gt0_sys) := partition_inequalities sys in
        let (lt0_sys, eq0_sys) := p_sys in
        let (p_is, gt0_is) := partition_inequalities (ineq :: sys) in
        let (lt0_is, eq0_is) := p_is in
        (ineq n <= 0 = true /\ 0 <= ineq n = true /\
         lt0_is = lt0_sys /\ gt0_is = gt0_sys /\ eq0_is = ineq :: eq0_sys) \/ 
        (ineq n <= 0 = true /\ 0 <= ineq n = false /\  
         lt0_is = ineq :: lt0_sys /\ gt0_is = gt0_sys /\ eq0_is = eq0_sys) \/ 
        (ineq n <= 0 = false /\ 0 <= ineq n = true /\ 
         lt0_is = lt0_sys /\ gt0_is = ineq :: gt0_sys /\ eq0_is = eq0_sys).
Proof.
    (* This proof surely requires some automation *)
    intros n ineq sys.
    destruct (partition_inequalities sys) 
        as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
    destruct (partition_inequalities (ineq :: sys)) 
        as [[lt0_is eq0_is] gt0_is] eqn:Hpart_is.
    destruct (ineq n <= 0) eqn:Hle0; destruct (0 <= ineq n) eqn:Hge0.
    all: (
        unfold partition_inequalities in Hpart_is;
        destruct (partition (fun i => i n <= 0) (ineq :: sys)) 
            as [p_le0_is p_gt0_is] eqn:Hpart1_is;
        destruct (partition (fun i => 0 <= i n) p_le0_is) 
            as [p_eq0_is p_lt0_is] eqn:Hpart2_is;
        unfold partition_inequalities in Hpart_sys;
        destruct (partition (fun i => i n <= 0) sys) 
            as [p_le0_sys p_gt0_sys] eqn:Hpart1_sys;
        destruct (partition (fun i => 0 <= i n) p_le0_sys) 
            as [p_eq0_sys p_lt0_sys] eqn:Hpart2_sys
    ).
    * left.
      pose proof (partition_cons1 _ ineq _ Hpart1_sys Hle0) as Hderived1.
      assert (Hhelp1: ((ineq :: p_le0_sys, p_gt0_sys) = (p_le0_is, p_gt0_is))). {
          apply (eq_ind (partition (fun i => i n <= 0) (ineq :: sys)) 
              (fun a => a = (p_le0_is, p_gt0_is)) Hpart1_is).
          apply Hderived1.
      } 
      apply pair_equal_spec in Hhelp1; destruct Hhelp1 as [Hderived2 Hderived3].
      rewrite <- Hderived2 in Hpart2_is.
      pose proof (partition_cons1 _ ineq _ Hpart2_sys Hge0) as Hderived4.
      assert (Hhelp2: ((ineq :: p_eq0_sys, p_lt0_sys) = (p_eq0_is, p_lt0_is))). {
          apply (eq_ind (partition (fun i => 0 <= i n) (ineq :: p_le0_sys)) 
              (fun a => a = (p_eq0_is, p_lt0_is)) Hpart2_is).
          apply Hderived4.
      } 
      apply pair_equal_spec in Hhelp2; destruct Hhelp2 as [Hderived5 Hderived6].
      rewrite <- Hderived3 in Hpart_is.
      rewrite <- Hderived5 in Hpart_is.
      rewrite <- Hderived6 in Hpart_is.
      apply pair_equal_spec in Hpart_is.
      destruct Hpart_is as [Hpart_is Hpart_is1].
      apply pair_equal_spec in Hpart_is.
      destruct Hpart_is as [Hpart_is2 Hpart_is3].
      apply pair_equal_spec in Hpart_sys.
      destruct Hpart_sys as [Hpart_sys Hpart_sys1].
      apply pair_equal_spec in Hpart_sys.
      destruct Hpart_sys as [Hpart_sys2 Hpart_sys3].
      repeat split.
      - rewrite <- Hpart_is2.
        rewrite Hpart_sys2.
        reflexivity. 
      - rewrite <- Hpart_is1.
        rewrite Hpart_sys1.
        reflexivity. 
      - rewrite <- Hpart_is3.
        rewrite Hpart_sys3.
        reflexivity. 
    * right; left.
      pose proof (partition_cons1 _ ineq _ Hpart1_sys Hle0) as Hderived1.
      assert (Hhelp1: ((ineq :: p_le0_sys, p_gt0_sys) = (p_le0_is, p_gt0_is))). {
          apply (eq_ind (partition (fun i => i n <= 0) (ineq :: sys)) 
              (fun a => a = (p_le0_is, p_gt0_is)) Hpart1_is).
          apply Hderived1.
      } 
      apply pair_equal_spec in Hhelp1; destruct Hhelp1 as [Hderived2 Hderived3].
      rewrite <- Hderived2 in Hpart2_is.
      pose proof (partition_cons2 _ ineq _ Hpart2_sys Hge0) as Hderived4.
      assert (Hhelp2: ((p_eq0_sys, ineq :: p_lt0_sys) = (p_eq0_is, p_lt0_is))). {
          apply (eq_ind (partition (fun i => 0 <= i n) (ineq :: p_le0_sys)) 
              (fun a => a = (p_eq0_is, p_lt0_is)) Hpart2_is).
          apply Hderived4.
      } 
      apply pair_equal_spec in Hhelp2; destruct Hhelp2 as [Hderived5 Hderived6].
      rewrite <- Hderived3 in Hpart_is.
      rewrite <- Hderived5 in Hpart_is.
      rewrite <- Hderived6 in Hpart_is.
      apply pair_equal_spec in Hpart_is.
      destruct Hpart_is as [Hpart_is Hpart_is1].
      apply pair_equal_spec in Hpart_is.
      destruct Hpart_is as [Hpart_is2 Hpart_is3].
      apply pair_equal_spec in Hpart_sys.
      destruct Hpart_sys as [Hpart_sys Hpart_sys1].
      apply pair_equal_spec in Hpart_sys.
      destruct Hpart_sys as [Hpart_sys2 Hpart_sys3].
      repeat split.
      - rewrite <- Hpart_is2.
        rewrite Hpart_sys2.
        reflexivity. 
      - rewrite <- Hpart_is1.
        rewrite Hpart_sys1.
        reflexivity. 
      - rewrite <- Hpart_is3.
        rewrite Hpart_sys3.
        reflexivity.       
    * right; right.
      pose proof (partition_cons2 _ ineq _ Hpart1_sys Hle0) as Hderived1.
      assert (Hhelp1: ((p_le0_sys, ineq :: p_gt0_sys) = (p_le0_is, p_gt0_is))). {
          apply (eq_ind (partition (fun i => i n <= 0) (ineq :: sys)) 
              (fun a => a = (p_le0_is, p_gt0_is)) Hpart1_is).
          apply Hderived1.
      } 
      apply pair_equal_spec in Hhelp1; destruct Hhelp1 as [Hderived2 Hderived3].
      rewrite <- Hderived2 in Hpart2_is.
      assert (Hhelp2: ((p_eq0_sys, p_lt0_sys) = (p_eq0_is, p_lt0_is))). {
          apply (eq_ind (partition (fun i => 0 <= i n) p_le0_sys) 
              (fun a => a = (p_eq0_is, p_lt0_is)) Hpart2_is).
          apply Hpart2_sys.
      } 
      apply pair_equal_spec in Hhelp2; destruct Hhelp2 as [Hderived5 Hderived6].
      rewrite <- Hderived3 in Hpart_is.
      rewrite <- Hderived5 in Hpart_is.
      rewrite <- Hderived6 in Hpart_is.
      apply pair_equal_spec in Hpart_is.
      destruct Hpart_is as [Hpart_is Hpart_is1].
      apply pair_equal_spec in Hpart_is.
      destruct Hpart_is as [Hpart_is2 Hpart_is3].
      apply pair_equal_spec in Hpart_sys.
      destruct Hpart_sys as [Hpart_sys Hpart_sys1].
      apply pair_equal_spec in Hpart_sys.
      destruct Hpart_sys as [Hpart_sys2 Hpart_sys3].
      repeat split.
      - rewrite <- Hpart_is2.
        rewrite Hpart_sys2.
        reflexivity. 
      - rewrite <- Hpart_is1.
        rewrite Hpart_sys1.
        reflexivity. 
      - rewrite <- Hpart_is3.
        rewrite Hpart_sys3.
        reflexivity.
    * apply ax_real_leq_false in Hle0.
      apply ax_real_leq_false in Hge0.
      lra.
Qed. 

Lemma partition_inequalities_lt0:
  forall n (sys: LinearSystem n) lt0 eq0 gt0,
    (lt0, eq0, gt0) = partition_inequalities sys ->
    forall ineq,
      In ineq lt0 -> (0 <= ineq n) = false.
Proof.
  intros n sys.
  induction sys; intros lt0 eq0 gt0 Hpart ineq Hineq.
  * unfold partition_inequalities, partition in Hpart.
    injection Hpart; intros Hgt Heq Hlt.
    rewrite Hlt in Hineq.
    contradiction Hineq.
  * remember (partition_inequalities sys) as part_sys.
    destruct part_sys as [[lt0_sys eq0_sys] gt0_sys].
    pose proof (partition_inequalities_cons _ a sys) as Hpcons.
    rewrite <- Hpart in Hpcons.
    rewrite <- Heqpart_sys in Hpcons.
    destruct Hpcons as [Hpcons|[Hpcons|Hpcons]].
    all: destruct Hpcons as [Ha_lt_0 [H0_lt_a [Hlt0 [Hgt0 Heq0]]]].
    - rewrite Hlt0 in Hineq.
      specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
      apply IHsys.
    - rewrite Hlt0 in Hineq.
      apply in_inv in Hineq.
      destruct Hineq as [Hineq|Hineq].
      * rewrite <- Hineq. apply H0_lt_a.
      * specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
        apply IHsys.
    - rewrite Hlt0 in Hineq.
      specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
      apply IHsys.
Qed.

Lemma partition_inequalities_eq0:
  forall n (sys: LinearSystem n) lt0 eq0 gt0,
    (lt0, eq0, gt0) = partition_inequalities sys ->
    forall ineq,
      In ineq lt0 -> (0 <= ineq n) = false.
Proof.
  intros n sys.
  induction sys; intros lt0 eq0 gt0 Hpart ineq Hineq.
  * unfold partition_inequalities, partition in Hpart.
    injection Hpart; intros Hgt Heq Hlt.
    rewrite Hlt in Hineq.
    contradiction Hineq.
  * remember (partition_inequalities sys) as part_sys.
    destruct part_sys as [[lt0_sys eq0_sys] gt0_sys].
    pose proof (partition_inequalities_cons _ a sys) as Hpcons.
    rewrite <- Hpart in Hpcons.
    rewrite <- Heqpart_sys in Hpcons.
    destruct Hpcons as [Hpcons|[Hpcons|Hpcons]].
    all: destruct Hpcons as [Ha_lt_0 [H0_lt_a [Hlt0 [Hgt0 Heq0]]]].
    - rewrite Hlt0 in Hineq.
      specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
      apply IHsys.
    - rewrite Hlt0 in Hineq.
      apply in_inv in Hineq.
      destruct Hineq as [Hineq|Hineq].
      * rewrite <- Hineq. apply H0_lt_a.
      * specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
        apply IHsys.
    - rewrite Hlt0 in Hineq.
      specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
      apply IHsys.
Qed.

Lemma partition_inequalities_gt0:
  forall n (sys: LinearSystem n) lt0 eq0 gt0,
    (lt0, eq0, gt0) = partition_inequalities sys ->
    forall ineq,
      In ineq gt0 -> (ineq n <= 0) = false.
Proof.
  intros n sys.
  induction sys; intros lt0 eq0 gt0 Hpart ineq Hineq.
  * unfold partition_inequalities, partition in Hpart.
    injection Hpart; intros Hgt Heq Hlt.
    rewrite Hgt in Hineq.
    contradiction Hineq.
  * remember (partition_inequalities sys) as part_sys.
    destruct part_sys as [[lt0_sys eq0_sys] gt0_sys].
    pose proof (partition_inequalities_cons _ a sys) as Hpcons.
    rewrite <- Hpart in Hpcons.
    rewrite <- Heqpart_sys in Hpcons.
    destruct Hpcons as [Hpcons|[Hpcons|Hpcons]].
    all: destruct Hpcons as [Ha_lt_0 [H0_lt_a [Hlt0 [Hgt0 Heq0]]]].
    - rewrite Hgt0 in Hineq.
      specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
      apply IHsys.
    - rewrite Hgt0 in Hineq.
      specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
      apply IHsys.
    - rewrite Hgt0 in Hineq.
      apply in_inv in Hineq.
      destruct Hineq as [Hineq|Hineq].
      * rewrite <- Hineq. apply Ha_lt_0.
      * specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl ineq Hineq).
        apply IHsys.
Qed.

Lemma partition_cons_lt0:
  forall n (ineq: LinearInequality n) sys,
      let (p_sys, gt0_sys) := partition_inequalities sys in
      let (lt0_sys, eq0_sys) := p_sys in
      ineq n <= 0 = true /\ 0 <= ineq n = false ->
      (ineq :: lt0_sys, eq0_sys, gt0_sys) = partition_inequalities (ineq :: sys).
Proof.
  intros n ineq sys.
  pose proof (partition_inequalities_cons n ineq sys).
  remember (partition_inequalities sys) as sys_p.
  destruct sys_p as [[lt0 eq0] gt0].
  remember (partition_inequalities (ineq :: sys)) as sys_p2.
  destruct sys_p2 as [[lt0_2 eq0_2] gt0_2].
  intros Hineq; destruct Hineq as [Hineq1 Hineq2].
  destruct H as [H|[H|H]]; destruct H as [Ha_ge_0 [H0_ge_a [Hsys_lt0 [Hsys_gt0 Hsys_eq0]]]].
  * rewrite H0_ge_a in Hineq2; discriminate.
  * rewrite Hsys_lt0, Hsys_gt0, Hsys_eq0; reflexivity.
  * rewrite Ha_ge_0 in Hineq1; discriminate.
Qed.

Lemma partition_cons_eq0:
  forall n (ineq: LinearInequality n) sys,
      let (p_sys, gt0_sys) := partition_inequalities sys in
      let (lt0_sys, eq0_sys) := p_sys in
      ineq n <= 0 = true /\ 0 <= ineq n = true ->
      (lt0_sys, ineq :: eq0_sys, gt0_sys) = partition_inequalities (ineq :: sys).
Proof.
  intros n ineq sys.
  pose proof (partition_inequalities_cons n ineq sys).
  remember (partition_inequalities sys) as sys_p.
  destruct sys_p as [[lt0 eq0] gt0].
  remember (partition_inequalities (ineq :: sys)) as sys_p2.
  destruct sys_p2 as [[lt0_2 eq0_2] gt0_2].
  intros Hineq; destruct Hineq as [Hineq1 Hineq2].
  destruct H as [H|[H|H]]; destruct H as [Ha_ge_0 [H0_ge_a [Hsys_lt0 [Hsys_gt0 Hsys_eq0]]]].
  * rewrite Hsys_lt0, Hsys_gt0, Hsys_eq0; reflexivity.
  * rewrite H0_ge_a in Hineq2; discriminate. 
  * rewrite Ha_ge_0 in Hineq1; discriminate.
Qed.

Lemma partition_cons_gt0:
  forall n (ineq: LinearInequality n) sys,
      let (p_sys, gt0_sys) := partition_inequalities sys in
      let (lt0_sys, eq0_sys) := p_sys in
      ineq n <= 0 = false /\ 0 <= ineq n = true ->
      (lt0_sys, eq0_sys, ineq :: gt0_sys) = partition_inequalities (ineq :: sys).
Proof.
  intros n ineq sys.
  pose proof (partition_inequalities_cons n ineq sys).
  remember (partition_inequalities sys) as sys_p.
  destruct sys_p as [[lt0 eq0] gt0].
  remember (partition_inequalities (ineq :: sys)) as sys_p2.
  destruct sys_p2 as [[lt0_2 eq0_2] gt0_2].
  intros Hineq; destruct Hineq as [Hineq1 Hineq2].
  destruct H as [H|[H|H]]; destruct H as [Ha_ge_0 [H0_ge_a [Hsys_lt0 [Hsys_gt0 Hsys_eq0]]]].
  * rewrite Ha_ge_0 in Hineq1; discriminate.
  * rewrite H0_ge_a in Hineq2; discriminate.
  * rewrite Hsys_lt0, Hsys_gt0, Hsys_eq0; reflexivity.
Qed.

Definition bool_to_Prop (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.

Coercion bool_to_Prop : bool >-> Sortclass.

Lemma RSOPM_le_refl : forall x : T RSOPM, x <= x = true.
Proof.
  intro x.
  unfold "<=".
  apply ax_real_leq_true.
  apply Rle_refl.
Qed.

Lemma RSOPM_le_and_le_eq: 
  forall x y : T RSOPM, (x <= y) = true /\ (y <= x) = true <-> (x=y).
Proof.
  intros.
  repeat rewrite <- RSOPM_bool_prop.
  split.
  intro.
  apply ax_equality.
  rewrite <- Rle_le_eq.
  split.
  destruct H as [H1 H2].
  rewrite <- ax_real_leq_true.
  exact H1.
  rewrite <- ax_real_leq_true.
  destruct H as [H1 H2].
  exact H2.
  intro.
  rewrite H.
  split.
  apply RSOPM_le_refl.
  apply RSOPM_le_refl.
Qed.

Lemma RSOPM_0_mult : forall x : T RSOPM,  0 *  x = 0.
Proof.
intros.
apply ax_equality.
rewrite ax_real_mult.
rewrite ax_zero_is_zero.
rewrite (Rmult_0_l (INJ_RSOPM RSOPM x)).
reflexivity.
Qed.

Lemma trivial_remove_var_eq0_sol: 
    forall (n:nat) (sys: LinearSystem (S n)) lt0 eq0 gt0,
        (lt0, eq0, gt0) = partition_inequalities sys -> 
        forall sol, (is_linear_system_solution (n:=(S n)) eq0 sol <->
        is_linear_system_solution (n:=n) eq0 sol).
Proof.
intros n sys.
induction sys.
+ intros lt0 eq0 gt0 Hpart sol.
  unfold partition_inequalities in Hpart.
  unfold partition in Hpart.
  injection Hpart; intros.
  subst.
  unfold is_linear_system_solution; unfold interpret_inequalities.
  reflexivity.
+ intros lt0 eq0 gt0 Hpart sol.
  pose proof (partition_inequalities_cons (S n)) as Hcons.
  specialize (Hcons a sys).
  remember (partition_inequalities (n:=(S n)) sys) as part_sys.
  destruct part_sys as [[lt0_sys eq0_sys] gt0_sys].
  rewrite <- Hpart in Hcons.
  specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl sol).
  destruct Hcons as [Hcons|[Hcons|Hcons]].
  all: destruct Hcons as [Ha1 [Ha2 [Hlt0 [Hgt0 Heq0]]]].
  unfold partition_inequalities in Hpart.
  destruct (partition
  (fun ineq : nat -> T RSOPM =>
  ineq (S n) <= 0) (a :: sys)).
  destruct (partition
  (fun ineq : nat -> T RSOPM =>
  0 <= ineq (S n))).
  - subst.
    unfold is_linear_system_solution.
    unfold interpret_inequalities. 
    fold (interpret_inequalities (n:=(S n))).
    fold (interpret_inequalities (n:=n)).
    rewrite IHsys.
    unfold is_linear_system_solution.
    split.
    intro.
    destruct H as [H1 H2].
    split.
    unfold interpret_inequality in H1.
    unfold interpret_inequality_helper in H1.
    fold (interpret_inequality_helper (n:=n)) in H1.
    unfold interpret_inequality.
    assert (a (S n) = 0).
    apply RSOPM_le_and_le_eq.
    split. exact Ha1. exact Ha2.
    rewrite H in H1.
    rewrite RSOPM_0_mult in H1.
    rewrite RSOPM_plus_comm in H1.
    rewrite RSOPM_plus_0_r in H1.
    exact H1.
    exact H2.
    intro.
    destruct H as [H1 H2].
    split.
    unfold interpret_inequality.
    unfold interpret_inequality_helper.
    fold (interpret_inequality_helper (n:=n)).
    assert (a (S n) = 0).
    apply RSOPM_le_and_le_eq.
    split. exact Ha1. exact Ha2.
    unfold interpret_inequality.
    unfold interpret_inequality_helper.
    rewrite H .
    rewrite RSOPM_0_mult.
    rewrite RSOPM_plus_comm.
    rewrite RSOPM_plus_0_r.
    exact H1.
    exact H2.
  - subst.
   exact IHsys.
  - subst.
    exact IHsys.
Qed.


Lemma partition_inequalities_solutions: 
    forall n (sys: LinearSystem n) lt0 eq0 gt0 sol,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        is_linear_system_solution lt0 sol ->
        is_linear_system_solution eq0 sol ->
        is_linear_system_solution gt0 sol ->
        is_linear_system_solution sys sol.
Proof.
   intros n sys. induction sys.
   * intros lt0 eq0 gt0 sol Hpart Hlt0 Heq0 Hgt0. 
      unfold is_linear_system_solution, interpret_inequalities; easy.
   * pose proof (partition_inequalities_cons n a sys) as Hsplit.
     destruct (partition_inequalities sys) 
       as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
     intros lt0_is eq0_is gt0_is sol Hpart_is.
     rewrite <- Hpart_is in Hsplit.  
     destruct Hsplit as [Hsplit|Hsplit]; last destruct Hsplit as [Hsplit|Hsplit].
     all: (intros Hlt0 Heq0 Hgt0; do 4 destruct Hsplit as [? Hsplit]).
     - rewrite Hsplit in Heq0. apply is_linear_system_solution_cons in Heq0.
       destruct Heq0 as [Hsol_a Hsol_eq0sys].
       apply is_linear_system_solution_cons; split.
       * apply Hsol_a.
       * apply (IHsys lt0_sys eq0_sys gt0_sys sol); first reflexivity.
         - rewrite <- H1; apply Hlt0.
         - apply Hsol_eq0sys.
         - rewrite <- H2; apply Hgt0.  
     - rewrite H1 in Hlt0. apply is_linear_system_solution_cons in Hlt0.
       destruct Hlt0 as [Hsol_a Hsol_lt0sys].
       apply is_linear_system_solution_cons; split.
       * apply Hsol_a.
       * apply (IHsys lt0_sys eq0_sys gt0_sys sol); first reflexivity.
         - apply Hsol_lt0sys.
         - rewrite <- Hsplit; apply Heq0.
         - rewrite <- H2; apply Hgt0.  
     - rewrite H2 in Hgt0. apply is_linear_system_solution_cons in Hgt0.
       destruct Hgt0 as [Hsol_a Hsol_gt0sys].
       apply is_linear_system_solution_cons; split.
       * apply Hsol_a.
       * apply (IHsys lt0_sys eq0_sys gt0_sys sol); first reflexivity.
         - rewrite <- H1; apply Hlt0.
         - rewrite <- Hsplit; apply Heq0.
         - apply Hsol_gt0sys.
Qed.

Lemma partition_inequalities_solutions_2 {n:nat}: 
    forall (sys: LinearSystem n) lt0 eq0 gt0 sol,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        is_linear_system_solution sys sol ->
        (is_linear_system_solution lt0 sol /\
        is_linear_system_solution eq0 sol /\
        is_linear_system_solution gt0 sol).
Proof.
induction sys.
intros lt0 eq0 gt0 sol Hpart Hsys.
unfold partition_inequalities in Hpart.
unfold partition in Hpart.
injection Hpart; intros Hgt0 Heq0 Hlt0.
subst.
unfold is_linear_system_solution.
unfold interpret_inequalities.
split. exact I. split. exact I. exact I.
intros lt0_a eq0_a gt0_a sol Hpart Hsys.
remember (partition_inequalities sys) as part_sys.
destruct part_sys as [[lt0 eq0] gt0].
pose proof partition_inequalities_cons as Hcons.
specialize (Hcons n a sys).
rewrite <- Hpart in Hcons.
rewrite <- Heqpart_sys in Hcons.
remember (partition_inequalities sys) as part_sys.
specialize (IHsys lt0 eq0 gt0 sol eq_refl).
destruct Hcons as [Hcons|[Hcons|Hcons]].
all: destruct Hcons as [Ha1 [Ha2 [Hlt0 [Hgt0 Heq0]]]].
- subst.
  unfold is_linear_system_solution in Hsys.
  unfold interpret_inequalities in Hsys.
  fold (interpret_inequalities (n:=1)) in Hsys.
  destruct Hsys as [Hsys1 Hsys2].
  unfold is_linear_system_solution at 2.
  unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
  rewrite <- and_assoc.
  rewrite <- (and_assoc (is_linear_system_solution lt0 sol) (interpret_inequality a sol) (is_linear_system_solution eq0 sol)).
  rewrite (and_comm (is_linear_system_solution lt0 sol) (interpret_inequality a sol)).
  rewrite and_assoc.
  rewrite and_assoc.
  split.
  exact Hsys1.
  apply IHsys.
  exact Hsys2.
- subst.
  unfold is_linear_system_solution in Hsys.
  unfold interpret_inequalities in Hsys.
  fold (interpret_inequalities (n:=1)) in Hsys.
  destruct Hsys as [Hsys1 Hsys2].
  unfold is_linear_system_solution at 1.
  unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
  rewrite and_assoc.
  split.
  exact Hsys1.
  apply IHsys.
  exact Hsys2.
- - subst.
  unfold is_linear_system_solution in Hsys.
  unfold interpret_inequalities in Hsys.
  fold (interpret_inequalities (n:=1)) in Hsys.
  destruct Hsys as [Hsys1 Hsys2].
  unfold is_linear_system_solution at 3.
  unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
  rewrite (and_comm (interpret_inequality a sol) (interpret_inequalities gt0 sol)).
  rewrite <- and_assoc.
  rewrite <- and_assoc.
  split.
  rewrite and_assoc.
  apply IHsys.
  exact Hsys2.
  exact Hsys1.
Qed.

Lemma partition_inequalities_solutions_contraposition {n:nat}: 
    forall (sys: LinearSystem n) lt0 eq0 gt0 sol,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        (~ (is_linear_system_solution lt0 sol) \/
        ~(is_linear_system_solution eq0 sol) \/
        ~(is_linear_system_solution gt0 sol)) ->
        ~(is_linear_system_solution sys sol ).
Proof.
pose proof (partition_inequalities_solutions_2 (n:=n))as Hsplit.
intros sys lt0 eq0 gt0 sol Hpartition Hneg Hsys.
specialize (Hsplit sys lt0 eq0 gt0 sol Hpartition).
tauto.
Qed.

Lemma trivial_consistency_partition_solution:
    forall (sys: LinearSystem 1) lt0 eq0 gt0 sol,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        trivial_consistency eq0 = true ->
        is_linear_system_solution (n:=1) eq0 sol.
Proof.
    intros sys; induction sys.
    * intros lt0 eq0 gt0 sol Hpart Hconsis.
      unfold partition_inequalities in Hpart.
      unfold partition in Hpart.
      injection Hpart; intros Hgt0 Heq0 Hlt0.
      rewrite Heq0; unfold is_linear_system_solution, interpret_inequalities; easy.
    * intros lt0_is eq0_is gt0_is sol Hpart_is Htriv_cons.
      pose proof (partition_inequalities_cons _ a sys) as Hsplit.
      destruct (partition_inequalities sys) 
        as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
      rewrite <-Hpart_is in Hsplit.
      destruct Hsplit as [Hsplit|[Hsplit|Hsplit]];
      destruct Hsplit as [Ha_le0 [Ha_ge0 [Hlt0 [Hgt0 Heq0]]]].
      - rewrite Heq0.
        rewrite Heq0 in Htriv_cons.
        unfold trivial_consistency in Htriv_cons.
        apply Bool.andb_true_iff in Htriv_cons.
        fold trivial_consistency in Htriv_cons.
        destruct Htriv_cons as [Ha_cons Htriv_cons].
        apply is_linear_system_solution_cons; split.
        * unfold is_linear_system_solution, interpret_inequalities,
          interpret_inequality, interpret_inequality_helper; split; last easy.
          apply ax_real_leq_true in Ha_le0, Ha_ge0.
          apply ax_real_leq_true; RSOPM_realize.
          rewrite ax_zero_is_zero in Ha_le0, Ha_ge0.
          assert (INJ_RSOPM RSOPM (a 1%nat) = 0%R) as Hhelp. lra.
          rewrite Hhelp. field_simplify.
          apply ax_real_leq_true in Ha_cons.
          rewrite ax_zero_is_zero in Ha_cons.
          apply Ha_cons.
        * specialize (IHsys lt0_sys eq0_sys gt0_sys sol).
          apply IHsys.
          - reflexivity.
          - apply Htriv_cons.
    * rewrite Heq0.
      specialize (IHsys lt0_sys eq0_sys gt0_sys sol).
      apply IHsys.
      - reflexivity.
      - rewrite Heq0 in Htriv_cons; apply Htriv_cons.
    * rewrite Heq0.
      specialize (IHsys lt0_sys eq0_sys gt0_sys sol).
      apply IHsys.
      - reflexivity.
      - rewrite Heq0 in Htriv_cons; apply Htriv_cons.
Qed.


Fixpoint RSOPM_list_min (l: list (T RSOPM)): option (T RSOPM) :=
match l with
| nil => None
| head :: tail => 
    match RSOPM_list_min tail with
    | None => Some head
    | Some previous_min =>
        if head <= previous_min then Some head else Some previous_min
    end
end. 

(*MJ: changed previous_min to previous_max for clarity*)
Fixpoint RSOPM_list_max (l: list (T RSOPM)): option (T RSOPM) :=
match l with
| nil => None
| head :: tail => 
    match RSOPM_list_max tail with
    | None => Some head
    | Some previous_max => 
        if head <= previous_max then Some previous_max else Some head
    end
end. 


Lemma Some_eq_Some: forall x y : T RSOPM, Some x = Some y -> x = y.
Proof.
  intros x y H. (* Introduce the variables and hypothesis *)
  injection H. (* Use injection to derive x = y from Some x = Some y *)
  intros Hxy. (* Introduce the resulting hypothesis *)
  assumption. (* Conclude the goal using the derived hypothesis *)
Qed.

(* following lemma just says if you add element to list, 
the maximum stays the same or is the new element*)
Lemma RSOPM_list_max_monotonic_helper :
  forall (head : T RSOPM) (tail : list (T RSOPM)),
    match (RSOPM_list_max tail) with 
    | None => True 
    | Some previous_max => 
      match RSOPM_list_max (head :: tail) with
      | None => False
      | Some new_max => new_max = previous_max \/ new_max = head
      end 
    end.
Proof.
intros head tail.
destruct (RSOPM_list_max tail) as [previous_max |] eqn: Htail.
destruct (RSOPM_list_max (head :: tail)) as [new_max |] eqn: Hheadtail.
unfold RSOPM_list_max in Hheadtail.
* destruct ((fix RSOPM_list_max (l : list (T RSOPM)) : option (T RSOPM) :=
            match l with
              | [] => None
              | head :: tail =>
              match RSOPM_list_max tail with
                | Some previous_max =>
                  if head <= previous_max
                  then Some previous_max
                  else Some head
                | None => Some head
              end
            end) tail) eqn:Hmaxtail.
rewrite <- Hmaxtail in Hheadtail.
destruct (head <= t) eqn:Hcompare.
destruct tail as [| head' tail'] eqn:Htail2.
- unfold RSOPM_list_max in Htail.
  rewrite Htail in Hheadtail.
  injection Hheadtail.
  intro H. left. symmetry. exact H.
- unfold RSOPM_list_max in Htail.
  fold RSOPM_list_max in Htail.
  fold RSOPM_list_max in Hmaxtail.
  fold RSOPM_list_max in Hheadtail.
  rewrite Htail in Hheadtail.
  injection Hheadtail.
  intro H. left. symmetry. exact H.
- right. injection Hheadtail. intro H. symmetry. exact H.
- right. injection Hheadtail. intro H. symmetry. exact H.
- unfold RSOPM_list_max in Hheadtail.
  unfold RSOPM_list_max in Htail.
  destruct tail as [| head' tail'] eqn:Htail2.  
  - discriminate Hheadtail.
  - rewrite Htail in Hheadtail.
    destruct (head <= previous_max).
    - discriminate Hheadtail.
    - discriminate Hheadtail.
apply I.
Qed.

Lemma max_none_for_empty:
    forall l,
        RSOPM_list_max l = None -> l = [].
Proof.
  intros l H.
  induction l; first reflexivity.
  unfold RSOPM_list_max in H; fold RSOPM_list_max in H.
  destruct (RSOPM_list_max l); last discriminate.
  destruct (a <= t); discriminate.
Qed.

Lemma min_none_for_empty:
    forall l,
        RSOPM_list_min l = None -> l = [].
Proof.
  intros l H.
  induction l; first reflexivity.
  unfold RSOPM_list_min in H; fold RSOPM_list_min in H.
  destruct (RSOPM_list_min l); last discriminate.
  destruct (a <= t); discriminate.
Qed.

Definition compute_lb (lt0_partition: LinearSystem 1): option (T RSOPM) :=
    RSOPM_list_max (map (fun ineq => - (ineq 0%nat / ineq 1%nat)) lt0_partition).

Lemma compute_lb_correct:
  forall sys sol lt0 eq0 gt0,
      (lt0, eq0, gt0) = partition_inequalities sys ->
      match (compute_lb lt0) with
      | Some lb => lb <= sol 1%nat = true
      | None => True 
      end ->
      is_linear_system_solution lt0 sol.
Proof.
  intros sys sol.
  induction sys; intros lt0 eq0 gt0 Hpart H.
  * unfold partition_inequalities in Hpart.
    unfold partition in Hpart.
    apply pair_equal_spec in Hpart; destruct Hpart as [Hpart1 Hpart2].
    apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
    rewrite Hpart1.
    unfold is_linear_system_solution,interpret_inequalities. easy.
  * pose proof partition_inequalities_cons as Hcons.
    specialize (Hcons 1%nat a sys).
    rewrite <- Hpart in Hcons.
    remember (partition_inequalities sys) as part_sys.
    destruct part_sys as [[lt0_sys eq0_sys] gt0_sys].
    specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl).
    destruct Hcons as [Hcons|[Hcons|Hcons]].
    all: destruct Hcons as [Ha1 [Ha2 [Hlt0 [Hg0 Heq0]]]]. 
    - rewrite Hlt0 in H.
      specialize (IHsys H).
      rewrite <- Hlt0 in IHsys.
      apply IHsys.
    - rewrite Hlt0 in H.
      unfold compute_lb in H.
      rewrite map_cons in H.
      unfold RSOPM_list_max in H; fold RSOPM_list_max in H.
      pose proof (eq_refl (compute_lb (lt0_sys))) as Hlb_sys.
      unfold compute_lb in Hlb_sys at 1.
      remember (RSOPM_list_max (map _ lt0_sys)) as lb_sys.
      pose proof (eq_trans Heqlb_sys Hlb_sys) as Hlb_eq.
      unfold is_linear_system_solution.
      rewrite Hlt0.
      unfold interpret_inequalities; fold (interpret_inequalities lt0_sys sol).
      destruct lb_sys as [lb_sys|]; rewrite <- Hlb_eq in IHsys.
      * remember (- (a 0%nat / a 1%nat) <= lb_sys) as le_res.
        destruct le_res.
        - specialize (IHsys H).
          split; last apply IHsys.
          unfold interpret_inequality, interpret_inequality_helper.
          rewrite ax_real_leq_true.
          RSOPM_realize.
          symmetry in Heqle_res.
          rewrite ax_real_leq_false in Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite ax_real_leq_true in Heqle_res.
          rewrite ax_opp_is_opp, ax_real_div in Heqle_res.
          rewrite ax_real_leq_true in H.
          pose proof (Rle_trans _ _ _ Heqle_res H) as Hfinal.
          rewrite <- Rdiv_opp_r in Hfinal.
          rewrite Rcomplements.Rle_div_l in Hfinal; last lra.
          apply Rle_minus in Hfinal.
          rewrite Ropp_mult_distr_r_reverse in Hfinal.
          unfold Rminus in Hfinal.
          rewrite Ropp_involutive in Hfinal.
          rewrite Rplus_comm in Hfinal.
          rewrite Rmult_comm in Hfinal.
          apply Hfinal.
        - symmetry in Heqle_res.
          rewrite ax_real_leq_false in Heqle_res.
          rewrite ax_real_leq_true in H.
          assert (Hhelp: (forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 <= r3)%R). {
            intros r1 r2 r3 H1 H2.
            apply (Rle_trans r1 r2 r3).
            * apply Rlt_le, H1.
            * apply H2.
          }
          specialize (Hhelp _ _ _ Heqle_res H).
          rewrite <- ax_real_leq_true in Hhelp.
          specialize (IHsys Hhelp).
          split; last apply (IHsys).
          unfold interpret_inequality, interpret_inequality_helper.
          rewrite ax_real_leq_true; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in H.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r in H.
          rewrite Rcomplements.Rle_div_l in H; last lra.
          apply Rle_minus in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          unfold Rminus in H.
          rewrite Ropp_involutive in H.
          rewrite Rplus_comm in H.
          rewrite Rmult_comm in H.       
          apply H.  
      * specialize (IHsys I).
        split; last apply IHsys.
        unfold interpret_inequality, interpret_inequality_helper.
        rewrite ax_real_leq_true.
        RSOPM_realize.
        rewrite ax_real_leq_true in H.
        rewrite ax_opp_is_opp in H.
        rewrite ax_real_div in H.
        rewrite ax_real_leq_false in Ha2.
        rewrite ax_zero_is_zero in Ha2.
        rewrite <- Rdiv_opp_r in H.
        rewrite Rcomplements.Rle_div_l in H; last lra.
        apply Rle_minus in H.
        rewrite Ropp_mult_distr_r_reverse in H.
        unfold Rminus in H.
        rewrite Ropp_involutive in H.
        rewrite Rplus_comm in H.
        rewrite Rmult_comm in H.       
        apply H.
    - rewrite Hlt0 in H.
      specialize (IHsys H).
      rewrite <- Hlt0 in IHsys. 
      apply IHsys.
Qed.

Lemma RSOPM_le_neg : forall x y : T RSOPM, x <= y = false -> y <= x = true.
Proof.
  intros x y.
  intro H.
  apply ax_real_leq_true.
  apply ax_real_leq_false in H.
  apply Rlt_le.
  exact H.
Qed.

Lemma Reals_leq : forall x y : R, (x <= y)%R \/ (y <= x)%R <-> (x < y)%R \/ (y <= x)%R.
Proof.
intros.
split.
  - (* Forward direction: (x <= y) \/ (y <= x) -> (x < y) \/ (y <= x) *)
    intros [Hxy | Hyx].
    + (* Case x <= y *)
      destruct (Rlt_or_le x y) as [Hlt | Heq]. (* Use standard order decomposition *)
      * left; assumption. (* x < y case *)
      * right. exact Heq. (* x = y case implies y <= x *)
    + (* Case y <= x *)
      right; assumption.
  
  - (* Backward direction: (x < y) \/ (y <= x) -> (x <= y) \/ (y <= x) *)
    intros [Hlt | Hyx].
    + left. apply Rlt_le. assumption. (* x < y implies x <= y *)
    + right. assumption.
Qed.


Lemma RSOPM_total_order_bool : forall x y : T RSOPM, (x <= y) = true \/ (y <= x) = true.
Proof.
intros.
repeat rewrite ax_real_leq_true.
rewrite Reals_leq.
apply Rlt_or_le.
Qed.

Lemma RSOPM_bool_prop : forall x y : T RSOPM, (x <= y) = true <-> (x <= y).
Proof.
intros.
split.
intro.
rewrite H.
exact I.
intros.
apply Is_true_eq_true.
unfold Is_true.
destruct (x <= y).
exact I.
exact H.
Qed.


Lemma RSOPM_total_order_prop : forall x y : T RSOPM, (x <= y) \/ (y <= x).
Proof.
intros.
repeat rewrite <- RSOPM_bool_prop.
repeat rewrite ax_real_leq_true.
rewrite Reals_leq.
apply Rlt_or_le.
Qed.

Lemma Quantoren_demorgan_helper (A:Type): forall P Q : A -> Prop, ~ (exists a, P a /\ Q a) <-> forall a, ~(P a/\  Q a). 
Proof.
  intros.
  split.
  intro.
  apply not_ex_all_not.
  exact H.
  intros.
  apply all_not_not_ex.
  exact H.
Qed.

Lemma Quantoren_demorgan (A:Type): forall P Q : A -> Prop, ~ (exists a, P a /\ Q a) <-> forall a, ~(P a) \/  ~(Q a). 
Proof.
intros.
assert (forall T U : Prop, (~T \/ ~U) <-> (~(T /\ U))).
intros.
split.
intros.
apply or_not_and. exact H.
intros. apply not_and_or. exact H.
setoid_rewrite H.
apply Quantoren_demorgan_helper.
Qed.


Lemma RSOPM_list_max_monotone : forall head tail max1,
    RSOPM_list_max tail = Some max1 ->
    (exists max2,
      	RSOPM_list_max (head :: tail) = Some max2 /\
        max1 <= max2 = true).
Proof.
intros head tail max1 H1.
destruct (RSOPM_list_max (head :: tail)) as [max2 |] eqn:H2.
destruct (RSOPM_list_max tail) as [previous_max |] eqn:Hmax_tail.
- destruct (head <= previous_max) eqn:Hhead.
  + exists previous_max.
    split.
    rewrite <- H2.
    unfold RSOPM_list_max in H2.
    simpl.
    rewrite Hmax_tail.
    rewrite Hhead.
    reflexivity.
- injection H1 as ->.
unfold "<=". apply RSOPM_le_refl. 
- exists head.
  split.
  rewrite <- H2.
  simpl.
  unfold RSOPM_list_max in H2.
  rewrite Hmax_tail.
  rewrite Hhead. 
  reflexivity.
- assert (previous_max = max1) as H3.
  + apply Some_eq_Some. exact H1.
  rewrite H3 in Hhead. apply RSOPM_le_neg. exact Hhead. (*EASY RSOPM LEMMA*)
- exists head.
  split.
  rewrite <- H2.
  unfold RSOPM_list_max. fold RSOPM_list_max.
  rewrite Hmax_tail.
  reflexivity.
  discriminate.
- exists head.
  split.
  unfold RSOPM_list_max in H2. fold RSOPM_list_max in H2.
  destruct (RSOPM_list_max tail).
  destruct (head <= t).
  discriminate. discriminate. discriminate.
  - unfold RSOPM_list_max in H2. fold RSOPM_list_max in H2.
  destruct (RSOPM_list_max tail).
  destruct (head <= t).
  discriminate. discriminate. discriminate. 
Qed.

Lemma compute_lb_monotone:
  forall head tail lb1,
      compute_lb tail = Some lb1 ->
      (exists lb2, 
          compute_lb (head :: tail) = Some lb2 /\
          lb1 <= lb2 = true).
Proof.
  intros head tail lb1.
  intro H1.
  unfold compute_lb.
  apply RSOPM_list_max_monotone. 
  rewrite <- H1.
  unfold compute_lb.
  unfold map.
  reflexivity.
Qed.

Lemma compute_lb_none_for_empty:
    forall l,
        compute_lb l = None -> l = [].
Proof.
    intros l H.
    unfold compute_lb in H.
    apply max_none_for_empty in H.
    apply map_eq_nil in H.
    apply H.
Qed.

Definition compute_ub (gt0_partition: LinearSystem 1): option (T RSOPM) :=
    RSOPM_list_min (map (fun ineq => - (ineq 0%nat / ineq 1%nat)) gt0_partition).

Lemma compute_ub_none_for_empty:
    forall l,
        compute_ub l = None -> l = [].
Proof.
    intros l H.
    unfold compute_lb in H.
    apply min_none_for_empty in H.
    apply map_eq_nil in H.
    apply H.
Qed.

Lemma compute_ub_correct:
    forall sys sol lt0 eq0 gt0,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        match (compute_ub gt0) with
        | Some ub => sol 1%nat <= ub = true
        | None => True 
        end ->
        is_linear_system_solution gt0 sol.
Proof.
  intros sys sol.
  induction sys; intros lt0 eq0 gt0 Hpart H.
  * unfold partition_inequalities in Hpart.
    unfold partition in Hpart.
    apply pair_equal_spec in Hpart; destruct Hpart as [Hpart1 Hpart2].
    apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
    rewrite Hpart2.
    unfold is_linear_system_solution,interpret_inequalities. easy.
  * pose proof partition_inequalities_cons as Hcons.
    specialize (Hcons 1%nat a sys).
    rewrite <- Hpart in Hcons.
    remember (partition_inequalities sys) as part_sys.
    destruct part_sys as [[lt0_sys eq0_sys] gt0_sys].
    specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl).
    destruct Hcons as [Hcons|[Hcons|Hcons]].
    all: destruct Hcons as [Ha1 [Ha2 [Hlt0 [Hgt0 Heq0]]]]. 
    - rewrite Hgt0 in H.
      specialize (IHsys H).
      rewrite <- Hgt0 in IHsys.
      apply IHsys.
    - rewrite Hgt0 in H.
      specialize (IHsys H).
      rewrite <- Hgt0 in IHsys. 
      apply IHsys.
    - rewrite Hgt0 in H.
      unfold compute_ub in H.
      rewrite map_cons in H.
      unfold RSOPM_list_min in H; fold RSOPM_list_min in H.
      pose proof (eq_refl (compute_ub (gt0_sys))) as Hub_sys.
      unfold compute_ub in Hub_sys at 1.
      remember (RSOPM_list_min (map _ gt0_sys)) as ub_sys.
      pose proof (eq_trans Hequb_sys Hub_sys) as Hub_eq.
      unfold is_linear_system_solution.
      rewrite Hgt0.
      unfold interpret_inequalities; fold (interpret_inequalities gt0_sys sol).
      destruct ub_sys as [ub_sys|]; rewrite <- Hub_eq in IHsys.
      * remember (- (a 0%nat / a 1%nat) <= ub_sys) as le_res.
        destruct le_res.
        - symmetry in Heqle_res.
          rewrite ax_real_leq_true in Heqle_res.
          rewrite ax_real_leq_true in H.
          pose proof (Rle_trans _ _ _ H Heqle_res) as Hhelp.
          rewrite <- ax_real_leq_true in Hhelp.
          specialize (IHsys Hhelp).
          split; last apply (IHsys).
          unfold interpret_inequality, interpret_inequality_helper.
          rewrite ax_real_leq_true; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in H.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha1.
          rewrite Ropp_div_distr_l in H.
          apply Rcomplements.Rle_div_r in H; last lra.
          apply Rle_minus in H.
          unfold Rminus in H.
          rewrite Ropp_involutive in H.
          rewrite Rmult_comm in H.
          apply H.
        - specialize (IHsys H).
          split; last apply IHsys.
          unfold interpret_inequality, interpret_inequality_helper.
          rewrite ax_real_leq_true.
          RSOPM_realize.
          symmetry in Heqle_res.
          rewrite ax_real_leq_false in Ha1.
          rewrite ax_zero_is_zero in Ha1.
          rewrite ax_real_leq_false in Heqle_res.
          rewrite ax_opp_is_opp, ax_real_div in Heqle_res.
          rewrite ax_real_leq_true in H.
          apply Rlt_le in Heqle_res.
          pose proof (Rle_trans _ _ _ H Heqle_res) as Hfinal.
          rewrite Ropp_div_distr_l in Hfinal.
          apply Rcomplements.Rle_div_r in Hfinal; last lra.
          apply Rle_minus in Hfinal.
          unfold Rminus in Hfinal.
          rewrite Ropp_involutive in Hfinal.
          rewrite Rmult_comm in Hfinal.
          apply Hfinal.
      * specialize (IHsys I).
        split; last apply IHsys.
        unfold interpret_inequality, interpret_inequality_helper.
        rewrite ax_real_leq_true.
        RSOPM_realize.
        rewrite ax_real_leq_true in H.
        rewrite ax_opp_is_opp in H.
        rewrite ax_real_div in H.
        rewrite ax_real_leq_false in Ha1.
        rewrite ax_zero_is_zero in Ha1.
        rewrite Ropp_div_distr_l in H.
        apply Rcomplements.Rle_div_r in H; last lra.
        apply Rle_minus in H.
        unfold Rminus in H.
        rewrite Ropp_involutive in H.
        rewrite Rmult_comm in H.
        apply H.
Qed.

Lemma RSOPM_mult_comm:
    forall (x y: T RSOPM),
        x * y = y * x.
Proof.
    intros x y. apply ax_equality.
    RSOPM_realize; apply Rmult_comm.
Qed.

Lemma compute_lb_none : forall sys sol lt0 eq0 gt0,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        match (compute_lb lt0) with
        | Some lb => (lb <= sol 1%nat = false) ->
        (~ is_linear_system_solution lt0 sol)
        | None => True 
        end.
Proof.
 intros sys sol.
  induction sys; intros lt0 eq0 gt0 Hpart.
  * unfold partition_inequalities in Hpart.
    unfold partition in Hpart.
    apply pair_equal_spec in Hpart; destruct Hpart as [Hpart1 Hpart2].
    apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
    rewrite Hpart1.
    unfold is_linear_system_solution,interpret_inequalities.
    destruct (compute_ub []) eqn:Hub.
    + cbn. exact I.
    + cbn. exact I.
    (*Induktionsschlusss*)
  * pose proof partition_inequalities_cons as Hcons.
    specialize (Hcons 1%nat a sys).
    rewrite <- Hpart in Hcons.
    remember (partition_inequalities sys) as part_sys.
    destruct part_sys as [[lt0_sys eq0_sys] gt0_sys].
    specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl).
    destruct Hcons as [Hcons|[Hcons|Hcons]].
    all: destruct Hcons as [Ha1 [Ha2 [Hlt0 [Hgt0 Heq0]]]]. 
    - rewrite Hlt0.
      apply IHsys.
    - rewrite Hlt0.
      unfold compute_lb.
      rewrite map_cons.
      unfold RSOPM_list_max; fold RSOPM_list_max.
      pose proof (eq_refl (compute_lb (lt0_sys))) as Hlb_sys.
      unfold compute_lb in Hlb_sys at 1.
      remember (RSOPM_list_max (map _ lt0_sys)) as lb_sys.
      pose proof (eq_trans Heqlb_sys Hlb_sys) as Hlb_eq.
      unfold is_linear_system_solution.
      destruct lb_sys.
      + destruct (- (a 0%nat / a 1%nat) <= t) eqn:Hta.
        * intro.
          unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
          rewrite <- Hlb_eq in IHsys.
          apply or_not_and.
          right.
          apply IHsys.
          exact H.
        * intro.
          unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
          rewrite <- Hlb_eq in IHsys.
          apply or_not_and.
          left.
          unfold "~".
          intro.
          unfold interpret_inequality in H0.
          unfold interpret_inequality_helper in H0.
          rewrite ax_real_leq_false in H.
          rewrite ax_opp_is_opp in H.
          rewrite ax_real_div in H.
          rewrite ax_real_leq_false in Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite <- Ropp_div_distr_r in H.
          apply Rcomplements.Rlt_div_r in H.
          apply (Rplus_gt_compat_r (- INJ_RSOPM RSOPM (a 0%nat))) in H.
          rewrite Rplus_opp_r in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          rewrite <- Ropp_plus_distr in H.
          rewrite <- Ropp_0 in H.
          apply Ropp_lt_cancel in H.
          rewrite <- ax_real_mult in H.
          rewrite <- ax_real_plus in H.
          apply Rgt_lt in H.
          rewrite <- (ax_zero_is_zero RSOPM) in H.
          rewrite RSOPM_plus_comm in H.
          rewrite <- (ax_real_leq_false RSOPM (RSOPM_plus RSOPM (a 0%nat) (RSOPM_mult RSOPM (sol 1%nat) (a 1%nat))) 0) in H.
          rewrite RSOPM_plus_comm in H.
          rewrite RSOPM_mult_comm in H.
          unfold "<=" in H0.
          rewrite H in H0.
          discriminate.
          rewrite <- Ropp_0.
          apply Ropp_lt_cancel.
          repeat rewrite Ropp_involutive.
          exact Ha2.
        + intro.
          symmetry in Hlb_eq.
        apply compute_lb_none_for_empty in Hlb_eq.
        subst.
        unfold interpret_inequalities.
        unfold interpret_inequality.
        unfold interpret_inequality_helper.
        intro.
        rewrite ax_real_leq_false in H.
          rewrite ax_opp_is_opp in H.
          rewrite ax_real_div in H.
          rewrite ax_real_leq_false in Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite <- Ropp_div_distr_r in H.
          apply Rcomplements.Rlt_div_r in H.
          apply (Rplus_gt_compat_r (- INJ_RSOPM RSOPM (a 0%nat))) in H.
          rewrite Rplus_opp_r in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          rewrite <- Ropp_plus_distr in H.
          rewrite <- Ropp_0 in H.
          apply Ropp_lt_cancel in H.
          rewrite <- ax_real_mult in H.
          rewrite <- ax_real_plus in H.
          apply Rgt_lt in H.
          rewrite <- (ax_zero_is_zero RSOPM) in H.
          rewrite RSOPM_plus_comm in H.
          rewrite <- (ax_real_leq_false RSOPM (RSOPM_plus RSOPM (a 0%nat) (RSOPM_mult RSOPM (sol 1%nat) (a 1%nat))) 0) in H.
          rewrite RSOPM_plus_comm in H.
          rewrite RSOPM_mult_comm in H.
          unfold "<=" in H0.
          rewrite H in H0.
          destruct H0 as [H1 H2].
          discriminate.
          rewrite <- Ropp_0.
          apply Ropp_lt_cancel.
          repeat rewrite Ropp_involutive.
          exact Ha2.
    - rewrite Hlt0.
      apply IHsys.
Qed.

Lemma compute_ub_none : forall sys sol lt0 eq0 gt0,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        match (compute_ub gt0) with
        | Some ub => (sol 1%nat <= ub = false) ->
        (~ is_linear_system_solution gt0 sol)
        | None => True 
        end.
Proof.
  intros sys sol.
  induction sys; intros lt0 eq0 gt0 Hpart.
  * unfold partition_inequalities in Hpart.
    unfold partition in Hpart.
    apply pair_equal_spec in Hpart; destruct Hpart as [Hpart1 Hpart2].
    apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
    rewrite Hpart2.
    unfold is_linear_system_solution,interpret_inequalities.
    destruct (compute_ub []) eqn:Hub.
    + cbn. exact I.
    + cbn. exact I.
    (*Induktionsschlusss*)
  * pose proof partition_inequalities_cons as Hcons.
    specialize (Hcons 1%nat a sys).
    rewrite <- Hpart in Hcons.
    remember (partition_inequalities sys) as part_sys.
    destruct part_sys as [[lt0_sys eq0_sys] gt0_sys].
    specialize (IHsys lt0_sys eq0_sys gt0_sys eq_refl).
    destruct Hcons as [Hcons|[Hcons|Hcons]].
    all: destruct Hcons as [Ha1 [Ha2 [Hlt0 [Hgt0 Heq0]]]]. 
    - rewrite Hgt0.
      apply IHsys.
    - rewrite Hgt0.
      apply IHsys.
    - rewrite Hgt0.
      unfold compute_ub.
      rewrite map_cons.
      unfold RSOPM_list_min; fold RSOPM_list_min.
      pose proof (eq_refl (compute_ub (gt0_sys))) as Hub_sys.
      unfold compute_ub in Hub_sys at 1.
      remember (RSOPM_list_min (map _ gt0_sys)) as ub_sys.
      pose proof (eq_trans Hequb_sys Hub_sys) as Hub_eq.
      unfold is_linear_system_solution.
      destruct ub_sys.
      + destruct (- (a 0%nat / a 1%nat) <= t) eqn:Hta.
        * intro.
          unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
          rewrite <- Hub_eq in IHsys.
          apply or_not_and.
          left.
          unfold "~".
          intro.
          unfold interpret_inequality in H0.
          unfold interpret_inequality_helper in H0.
          rewrite ax_real_leq_false in H.
          rewrite ax_opp_is_opp in H.
          rewrite ax_real_div in H.
          rewrite ax_real_leq_false in Ha1.
          rewrite ax_zero_is_zero in Ha1.
          rewrite Ropp_div_distr_l in H.
          apply Rcomplements.Rlt_div_l in H.
          apply (Rplus_gt_compat_l (INJ_RSOPM RSOPM (a 0%nat))) in H.
          rewrite Rplus_opp_r in H.
          rewrite <- ax_real_mult in H.
          rewrite <- ax_real_plus in H.
          apply Rgt_lt in H.
          rewrite <- (ax_zero_is_zero RSOPM) in H.
          rewrite <- (ax_real_leq_false RSOPM (RSOPM_plus RSOPM (a 0%nat) (RSOPM_mult RSOPM (sol 1%nat) (a 1%nat))) 0) in H.
          rewrite RSOPM_plus_comm in H.
          rewrite RSOPM_mult_comm in H.
          unfold "<=" in H0.
          rewrite H in H0.
          discriminate.
          exact Ha1.
        * intro.
          rewrite <- Hub_eq in IHsys.
          apply IHsys in H.
          unfold "~".
           unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
          intro. 
          destruct H0 as [H1 H2].
          unfold is_linear_system_solution in H.
          contradiction.
      + symmetry in Hub_eq.
        apply compute_ub_none_for_empty in Hub_eq.
        subst.
        unfold interpret_inequalities.
        unfold interpret_inequality.
        unfold interpret_inequality_helper.
        intro.
        rewrite ax_real_leq_false in H.
        rewrite ax_opp_is_opp in H.
        rewrite ax_real_div in H.
        rewrite ax_real_leq_false in Ha1.
        rewrite ax_zero_is_zero in Ha1.
        rewrite Ropp_div_distr_l in H.
        apply Rcomplements.Rlt_div_l in H.
        apply (Rplus_gt_compat_l (INJ_RSOPM RSOPM (a 0%nat))) in H.
        rewrite Rplus_opp_r in H.
        rewrite <- ax_real_mult in H.
        rewrite <- ax_real_plus in H.
        apply Rgt_lt in H.
        rewrite <- (ax_zero_is_zero RSOPM) in H.
        rewrite <- (ax_real_leq_false RSOPM (RSOPM_plus RSOPM (a 0%nat) (RSOPM_mult RSOPM (sol 1%nat) (a 1%nat))) 0) in H.
        rewrite RSOPM_plus_comm in H.
        rewrite RSOPM_mult_comm in H.
        unfold "<=".
        rewrite H.
        intro.
        destruct H0 as [H1 H2].
        inversion H1.
        exact Ha1.
Qed.

Definition satisfy_bounds 
    (lbo: option (T RSOPM)) 
    (ubo: option (T RSOPM)) 
    : option (T RSOPM) :=
    match lbo, ubo with
    | None, None => Some 0
    | None, Some ub => Some ub
    | Some lb, None => Some lb
    | Some lb, Some ub =>
        if lb <= ub then Some lb else None
    end.

Lemma satisfy_bounds_none_preservation:
    forall head tail v2,
        satisfy_bounds (compute_lb tail) v2 = None ->
        satisfy_bounds (compute_lb (head :: tail)) v2 = None.
Proof.
    intros head tail v2 H.
    unfold satisfy_bounds in H.
    unfold satisfy_bounds.
    destruct (compute_lb tail) eqn:Htail.
    * destruct v2 eqn:Hv2.
      - destruct (t <= t0) eqn:Hcmp.
        * discriminate H.
        * apply (compute_lb_monotone head tail t) in Htail.
          destruct Htail as [lb2 [Hlb2_1 Hlb2_2]].
          rewrite Hlb2_1.
          assert (Hhelp: lb2 <= t0 = false). {
            apply ax_real_leq_false.
            apply ax_real_leq_true in Hlb2_2.
            apply ax_real_leq_false in Hcmp.
            lra.
          }
          rewrite Hhelp; reflexivity. 
      - discriminate H.
    * destruct v2; discriminate H.
Qed.

Definition trivial_extract (sys: LinearSystem 1): option (T RSOPM) :=
    let (p, gt0) := partition_inequalities sys in
    let (lt0, eq0) := p in
    match trivial_consistency eq0 with
    | true => satisfy_bounds (compute_lb lt0) (compute_ub gt0)
    | false => None
    end.

Lemma trivial_extract_correct_helper:
    forall a (sys: LinearSystem 1) sol r,
        trivial_extract (a::sys) = Some r ->
        sol 1%nat = r ->
        is_linear_system_solution (a::sys) sol
        -> is_linear_system_solution sys sol.
Proof.
    intros a sys sol r H1 H2 H3.
    unfold is_linear_system_solution in H3.
             unfold interpret_inequalities in H3. fold (interpret_inequalities sys sol) in H3.
              destruct H3 as [H3a H3b].
              exact H3b.
Qed.


Lemma trivial_extract_correct:
    forall (sys: LinearSystem 1),
        match trivial_extract sys with
        | Some r => (forall sol, 
            sol 1%nat = r -> is_linear_system_solution sys sol)
        | None => ~ (exists sol, is_linear_system_solution sys sol)
        end. 
Proof.
    intro sys.
    destruct (trivial_extract sys) eqn:Hextract.
    unfold trivial_extract in Hextract.
    destruct (partition_inequalities sys) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
   * intros sol Hsol.
     destruct (trivial_consistency eq0_sys) eqn:Htriv_cons; try discriminate.
     apply (partition_inequalities_solutions 1 _ lt0_sys eq0_sys gt0_sys). 
     - symmetry; apply Hpart_sys.
     - apply (compute_lb_correct sys _ lt0_sys eq0_sys gt0_sys).
       * symmetry; apply Hpart_sys.
       * unfold satisfy_bounds in Hextract.
         destruct (compute_lb lt0_sys) eqn:Hlb; try easy.
         - destruct (compute_ub gt0_sys) eqn:Hub.
           * destruct (t0 <= t1) eqn:Hcmp; try discriminate.
             injection Hextract; intro Hinject.
             rewrite Hinject. rewrite Hsol.
             apply ax_real_leq_true. lra.
           * injection Hextract; intro Hinject.
             rewrite Hinject. rewrite Hsol.
             apply ax_real_leq_true. lra.
     - apply (trivial_consistency_partition_solution 
                    sys lt0_sys eq0_sys gt0_sys sol).
       * symmetry; apply Hpart_sys.
       * apply Htriv_cons.
     - apply (compute_ub_correct sys _ lt0_sys eq0_sys gt0_sys).
       * symmetry; apply Hpart_sys.
       * unfold satisfy_bounds in Hextract.
         destruct (compute_lb lt0_sys) eqn:Hlb.
         - destruct (compute_ub gt0_sys) eqn:Hub; try easy.
           destruct (t0 <= t1) eqn:Hcmp; try discriminate.
           injection Hextract; intro Hinject.
           rewrite Hsol. rewrite <- Hinject.
           apply Hcmp.
         - destruct (compute_ub gt0_sys) eqn:Hub; try easy.
           injection Hextract; intro Hinject.
           rewrite Hsol. rewrite <- Hinject.
           apply ax_real_leq_true. lra.
           apply all_not_not_ex.
           intro sol.
           unfold trivial_extract in Hextract.
           remember (partition_inequalities (sys)) as part eqn:Hpart.
            destruct part as ((lt0, eq0), gt0).
            destruct trivial_consistency eqn:Htriv_cons; try discriminate.
            unfold satisfy_bounds in Hextract.
            destruct compute_lb eqn:Hlb; try easy.
            destruct compute_ub eqn:Hub; try easy.
            destruct (t <= t0) eqn:Hcmp; try discriminate.
            unfold is_linear_system_solution.
            destruct (t <= sol 1%nat) eqn:Hsol; try easy.
            + destruct (sol 1%nat <= t0) eqn:Hsol2; try easy.
              * rewrite ax_real_leq_false in Hcmp.
                rewrite ax_real_leq_true in Hsol.
                rewrite ax_real_leq_true in Hsol2.
                lra.
              * apply (partition_inequalities_solutions_contraposition sys lt0 eq0 gt0).
                exact Hpart.
                right. right.
                pose proof (compute_ub_none sys sol lt0 eq0 gt0) as Hub_correct.
                rewrite Hub in Hub_correct.
                apply Hub_correct.
                exact Hpart.
                exact Hsol2.
            + destruct (sol 1%nat <= t0) eqn:Hsol2; try easy.
              * apply (partition_inequalities_solutions_contraposition sys lt0 eq0 gt0).
                exact Hpart.
                left.
                pose proof (compute_lb_none sys sol lt0 eq0 gt0) as Hlb_correct.
                rewrite Hlb in Hlb_correct.
                apply Hlb_correct.
                exact Hpart.
                exact Hsol.
              * apply (partition_inequalities_solutions_contraposition sys lt0 eq0 gt0).
                exact Hpart.
                left.
                pose proof (compute_lb_none sys sol lt0 eq0 gt0) as Hlb_correct.
                rewrite Hlb in Hlb_correct.
                apply Hlb_correct.
                exact Hpart.
                exact Hsol.
            destruct compute_ub eqn:Hub; try easy.
            apply (partition_inequalities_solutions_contraposition sys lt0 eq0 gt0).
            exact Hpart.
            right. left.
            rewrite (trivial_remove_var_eq0_sol 0 sys lt0 eq0 gt0).
            pose proof trivial_consistency_correct as Hcons.
            specialize (Hcons eq0).
            rewrite Htriv_cons in Hcons.
            assert (forall n0 : LinearSystemSolution 0, ~ is_linear_system_solution (n:=0) eq0 n0).
            apply not_ex_all_not.
            exact Hcons.
            apply H.
            exact Hpart.
Qed.
 
Definition compose_inequalities {n: nat} (sys1 sys2: LinearSystem (S n)): LinearSystem n :=
    map
    (fun prod_el: LinearInequality (S n) * LinearInequality (S n) =>
         let (ineq1, ineq2) := prod_el in 
        (fun i => (ineq1 i/ - ineq1 (S n)) + (ineq2 i/ineq2 (S n))))
    (list_prod sys1 sys2).

Lemma compose_inequalities_correct:
  forall n (lt0 gt0: LinearSystem (S n)) sol,
    (forall ineq, In ineq lt0 -> (0 <= ineq (S n)) = false) ->
    (forall ineq, In ineq gt0 -> (ineq (S n) <= 0) = false) ->
    is_linear_system_solution (n:=S n) lt0 sol ->
    is_linear_system_solution (n:=S n) gt0 sol ->
    is_linear_system_solution (n:= n) (compose_inequalities lt0 gt0) sol.
Proof.
  intros n lt0 gt0 sol Hineq_lt0 Hineq_gt0 Hlt0 Hgt0.
  induction lt0; first exact I.
  * unfold compose_inequalities.
    unfold list_prod; fold (list_prod lt0 gt0).
    rewrite map_app.
    fold (compose_inequalities (n:=n) lt0 gt0).
    rewrite <- is_linear_system_solution_app; split.
    - induction gt0; first exact I.
      do 2 rewrite map_cons.
      apply is_linear_system_solution_cons; split.
      * apply is_linear_system_solution_cons in Hlt0,Hgt0.
        destruct Hlt0 as [Ha Hlt0].
        destruct Hgt0 as [Ha0 Hgt0].
        specialize (Hineq_lt0 a (in_eq a lt0)).
        specialize (Hineq_gt0 a0 (in_eq a0 gt0)).
        unfold is_linear_system_solution, interpret_inequalities; split; last exact I.
        unfold is_linear_system_solution, interpret_inequalities in Ha,Ha0.
        destruct Ha as [Ha Hrem]; clear Hrem.
        destruct Ha0 as [Ha0 Hrem]; clear Hrem.
        apply (interpret_inequality_compose n a a0 sol).
        - apply Hineq_lt0.
        - apply Hineq_gt0.
        - apply Ha.
        - apply Ha0.
      * apply IHgt0.
        - intros ineq Hineq.
          apply Hineq_gt0.
          right; apply Hineq.  
        - apply is_linear_system_solution_cons in Hgt0.
          apply Hgt0. 
        - intros H1 H2.
          specialize (IHlt0 H1 H2).
          clear Hineq_lt0. clear Hlt0. clear IHgt0. clear H1.
          clear H2.
          induction lt0; first exact I.
          unfold compose_inequalities, list_prod in IHlt0; fold (list_prod lt0 (a0 :: gt0)) in IHlt0.
          rewrite map_app in IHlt0.
          apply is_linear_system_solution_app in IHlt0.
          destruct IHlt0 as [H1 H2].
          specialize (IHlt1 H2).
          unfold compose_inequalities, list_prod; fold (list_prod lt0 gt0).
          repeat rewrite map_app.
          apply is_linear_system_solution_app; split.
          * repeat rewrite map_cons in H1.
            apply is_linear_system_solution_cons in H1.
            apply H1.
          * fold (compose_inequalities lt0 gt0).
            apply IHlt1.
    - apply IHlt0.
      * intros ineq Hineq.
        apply Hineq_lt0.
        right; apply Hineq.
      * apply is_linear_system_solution_cons in Hlt0.
        apply Hlt0.    
Qed.

Definition remove_var {n: nat} (sys: LinearSystem (S n)): LinearSystem n :=
    let (p, gt0) := partition_inequalities sys in
    let (lt0, eq0) := p in
    (compose_inequalities lt0 gt0) ++ eq0.

Lemma remove_var_preserves_solution:
    forall n (sys: LinearSystem (S n)) sol,
      is_linear_system_solution sys sol ->
      is_linear_system_solution (remove_var sys) sol.
Proof.
    intros n sys sol H.
    unfold remove_var.
    remember (partition_inequalities sys) as sys_p.
    destruct sys_p as [sys_p sys_gt0].
    destruct sys_p as [sys_lt0 sys_eq0].
    apply is_linear_system_solution_app; split.
    * apply compose_inequalities_correct.
      - apply (partition_inequalities_lt0 _ sys sys_lt0 sys_eq0 sys_gt0).
        apply Heqsys_p.
      - apply (partition_inequalities_gt0 _ sys sys_lt0 sys_eq0 sys_gt0).
        apply Heqsys_p.
      - apply (partition_inequalities_solutions_2 sys _ _ _ sol) in Heqsys_p.
        * apply Heqsys_p.
        * apply H.
      - apply (partition_inequalities_solutions_2 sys _ _ _ sol) in Heqsys_p.
        * apply Heqsys_p.
        * apply H.
    * pose proof (partition_inequalities_solutions_2 sys sys_lt0 sys_eq0 sys_gt0 sol Heqsys_p H) as Hp_ineq.
      destruct Hp_ineq as [H1 H2].
      destruct H2 as [Hmain H2].
      apply (trivial_remove_var_eq0_sol n sys sys_lt0 sys_eq0 sys_gt0).
      - apply Heqsys_p.
      - apply Hmain.
Qed.

Lemma remove_var_no_solution:
    forall n (sys: LinearSystem (S n)),
      ~ (exists sol: LinearSystemSolution n, is_linear_system_solution (remove_var sys) sol) ->
      ~ (exists sol: LinearSystemSolution (S n), is_linear_system_solution sys sol).
Proof.
    intros n sys Hrvar Hsol.
    unfold not in Hrvar.
    apply Hrvar.
    destruct Hsol as [sol Hsol].
    exists sol.
    apply remove_var_preserves_solution.
    apply Hsol.
Qed.

Definition insert_solution {n: nat} 
    (sys: LinearSystem (S n))
    (sol: LinearSystemSolution n)
    : LinearSystem 1 :=
    map
    (fun ineq => 
        fun i =>
        match i with
        | 1 => ineq (S n)
        | _ => interpret_inequality_helper ineq sol
        end)
    sys.

Lemma insert_solution_cons:
  forall n ineq (sys: LinearSystem (S n)) sol,
    insert_solution (ineq :: sys) sol = insert_solution [ineq] sol ++ insert_solution sys sol.
Proof.
  intros n ineq sys sol.
  unfold insert_solution at 1 2.
  unfold map at 2.
  rewrite map_cons.
  unfold app.
  reflexivity.
Qed.

Lemma insert_solution_cons_solution:
  forall n ineq (sys: LinearSystem (S n)) sol sol_full,
    is_linear_system_solution (insert_solution (ineq :: sys) sol) sol_full <->
    is_linear_system_solution (insert_solution [ineq] sol ++ insert_solution sys sol) sol_full.
Proof.
  intros n ineq sys sol sol_full.
  rewrite insert_solution_cons.
  split; intros H; apply H.
Qed.

Definition prepend_to_solution {n} (s: T RSOPM) (sol: LinearSystemSolution n)
  : nat -> T RSOPM 
  :=
  (fun sol_arg: nat => if sol_arg =? S n then s else sol sol_arg).  

Lemma prepend_to_solution_not_last:
  forall n1 n2 n3 s (sol: LinearSystemSolution n2),
    (S n1 <> n3)%nat ->
    prepend_to_solution (n:=n1) s sol n3 = sol n3.
Proof.
  intros n1 n2 n3 s sol Hn13.
  unfold prepend_to_solution.
  assert (Hhelp: n3 =? S n1 = false). {
    apply Nat.eqb_neq.
    lia.
  }
  rewrite Hhelp.
  reflexivity.
Qed.

Lemma prepend_to_solution_last:
  forall n1 n2 n3 s (sol: LinearSystemSolution n2),
    (S n1 = n3)%nat ->
    prepend_to_solution (n:=n1) s sol n3 = s.
Proof.
  intros n1 n2 n3 s sol Hn13.
  unfold prepend_to_solution.
  rewrite Hn13.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma prepend_interpret_rank:
  forall n n2 (a: LinearInequality (S n2)) s (sol: LinearSystemSolution n2),
    (n2 > n)%nat ->
    interpret_inequality_helper (n:=n) a (prepend_to_solution (n:=n2) s sol) = 
    interpret_inequality_helper (n:=n) a (prepend_to_solution (n:=S n2) s sol).
Proof.
  intros n.
  induction n; intros n2 a s sol Hn2.
  * unfold interpret_inequality_helper. reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
    rewrite (prepend_to_solution_not_last n2 n2 (S n)); last lia.
    rewrite (prepend_to_solution_not_last (S n2) n2 (S n)); last lia.
    rewrite (IHn n2 a s sol).
    reflexivity. lia.
Qed.

Lemma prepend_interpret:
  forall n (a: LinearInequality (S (S n))) s (sol: LinearSystemSolution (S n)),
    interpret_inequality_helper (n:=n) a (prepend_to_solution s sol) = 
    interpret_inequality_helper (n:=n) a sol.
Proof.
  intros n a s sol.
  induction n.
  * unfold interpret_inequality_helper; reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
    rewrite <- (IHn a sol).
    rewrite (prepend_to_solution_not_last (S (S n)) (S (S n)) (S n)); last lia.
    rewrite (prepend_interpret_rank n (S n)).
    reflexivity. lia.
Qed.

Lemma prepend_insert_split:
  forall n (sys: LinearSystem (S n)) s (sol: LinearSystemSolution n),
    is_linear_system_solution (n:=1) (insert_solution sys sol) (fun _ => s) ->
    is_linear_system_solution (n:=S n) sys (prepend_to_solution (n:=n) s sol).
Proof.
  intros n sys s sol Hs.
  induction sys; first exact I.
  rewrite insert_solution_cons_solution in Hs.
  apply is_linear_system_solution_app in Hs.
  destruct Hs as [Ha_s Ha_sys].
  apply is_linear_system_solution_cons; split.
  * unfold is_linear_system_solution, interpret_inequalities; split; last (exact I).
    unfold insert_solution, map in Ha_s.
    unfold is_linear_system_solution, interpret_inequalities in Ha_s.
    destruct Ha_s as [Ha_s Hrem]; clear Hrem.
    unfold interpret_inequality in Ha_s.
    unfold interpret_inequality.
    induction n.
    - unfold interpret_inequality_helper in Ha_s.
      unfold interpret_inequality_helper.
      unfold prepend_to_solution.
      unfold Nat.eqb.
      apply Ha_s.
    - unfold interpret_inequality_helper. fold (interpret_inequality_helper (n:=n)).
      unfold interpret_inequality_helper in Ha_s; fold (interpret_inequality_helper (n:=n)) in Ha_s.
      unfold prepend_to_solution at 1.
      rewrite Nat.eqb_refl.
      rewrite (prepend_to_solution_not_last (S n) (S n) (S n)); last lia.
      rewrite (prepend_interpret n a s sol).
      apply Ha_s.
  * apply IHsys.
    apply Ha_sys.
Qed.

Lemma absurd_reconstruction_helper:
  forall (sys: LinearSystem 1) sol,
    (exists sol_full, is_linear_system_solution sys sol_full) ->
    (exists sol1, is_linear_system_solution (insert_solution sys sol) sol1).
Proof.
  intros sys sol Hfull.
  destruct Hfull as [sol_full Hfull].
  exists (fun i => sol_full 1%nat).
  induction sys; first exact I.
  rewrite insert_solution_cons_solution.
  apply is_linear_system_solution_app.
  apply is_linear_system_solution_cons in Hfull.
  destruct Hfull as [Ha Hrest].
  split.
  * unfold is_linear_system_solution.
    unfold is_linear_system_solution in Ha.
    unfold insert_solution, map, interpret_inequalities; split; last exact I.
    unfold interpret_inequalities in Ha.
    destruct Ha as [Ha Htrash]; clear Htrash.
    unfold interpret_inequality.
    unfold interpret_inequality in Ha.
    clear IHsys; clear Hrest.
    unfold interpret_inequality_helper.
    unfold interpret_inequality_helper in Ha.
    apply Ha.
  * apply (IHsys Hrest).
Qed.

Definition insert_solution_ineq {n}
    (ineq: LinearInequality (S n))
    (sol: LinearSystemSolution n)
    : LinearInequality 1 :=
    (fun i =>
        match i with
        | 1 => ineq (S n)
        | _ => interpret_inequality_helper (n:=n) ineq sol
        end).
  
Lemma insert_solution_single:
  forall n (ineq: LinearInequality (S n)) sol,
    insert_solution [ineq] sol = [insert_solution_ineq ineq sol].
Proof.
  intros n ineq sol.
  unfold insert_solution, map, insert_solution_ineq.
  reflexivity.
Qed.

Lemma insert_partition:
  forall n (sys: LinearSystem (S n)) sol sys_lt0 sys_eq0 sys_gt0,
    (sys_lt0, sys_eq0, sys_gt0) = partition_inequalities sys ->
    ((insert_solution sys_lt0 sol), (insert_solution sys_eq0 sol), (insert_solution sys_gt0 sol)) =
      partition_inequalities (insert_solution sys sol).
Proof.
  intros n sys sol.
  induction sys; intros sys_lt0 sys_eq0 sys_gt0 Hpart.
  * unfold partition_inequalities, partition in Hpart.
    injection Hpart; intros Hlt0 Heq0 Hgt0.
    rewrite Hlt0, Heq0, Hgt0.
    unfold insert_solution, map; reflexivity.
  * pose proof (partition_inequalities_cons _ a sys) as Hcons.
    rewrite <- Hpart in Hcons.
    remember (partition_inequalities sys) as sys_part.
    destruct sys_part as [[sysp_lt0 sysp_eq0] sysp_gt0].
    specialize (IHsys sysp_lt0 sysp_eq0 sysp_gt0 eq_refl).
    rewrite insert_solution_cons.
    rewrite insert_solution_single; unfold app.
    destruct Hcons as [Hcons|[Hcons|Hcons]]; destruct Hcons as [Ha_ge_0 [H0_ge_a [Hsys_lt0 [Hsys_gt0 Hsys_eq0]]]].
    (* Duplication here *)
    - rewrite Hsys_lt0, Hsys_eq0, Hsys_gt0.
      rewrite insert_solution_cons.
      rewrite insert_solution_single; unfold app.
      pose proof (partition_cons_eq0 _ (insert_solution_ineq a sol) (insert_solution sys sol)) as Hmain.
      rewrite <- IHsys in Hmain.
      apply Hmain; split.
      * unfold insert_solution_ineq; apply Ha_ge_0.
      * unfold insert_solution_ineq; apply H0_ge_a.  
    - rewrite Hsys_lt0, Hsys_eq0, Hsys_gt0.
      rewrite insert_solution_cons.
      rewrite insert_solution_single; unfold app.
      pose proof (partition_cons_lt0 _ (insert_solution_ineq a sol) (insert_solution sys sol)) as Hmain.
      rewrite <- IHsys in Hmain.
      apply Hmain; split.
      * unfold insert_solution_ineq; apply Ha_ge_0.
      * unfold insert_solution_ineq; apply H0_ge_a.  
    - rewrite Hsys_lt0, Hsys_eq0, Hsys_gt0.
      rewrite insert_solution_cons.
      rewrite insert_solution_single; unfold app.
      pose proof (partition_cons_gt0 _ (insert_solution_ineq a sol) (insert_solution sys sol)) as Hmain.
      rewrite <- IHsys in Hmain.
      apply Hmain; split.
      * unfold insert_solution_ineq; apply Ha_ge_0.
      * unfold insert_solution_ineq; apply H0_ge_a. 
Qed.

Lemma trivial_consistency_insert_solution_eq0:
  forall n (sys: LinearSystem (S (S n))) sol sys_lt0 sys_eq0 sys_gt0 sys1_lt0 sys1_eq0 sys1_gt0,
    (sys_lt0, sys_eq0, sys_gt0) = partition_inequalities sys ->
    is_linear_system_solution (n:=(S n)) sys_eq0 sol ->
    (sys1_lt0, sys1_eq0, sys1_gt0) = partition_inequalities (insert_solution sys sol) ->
    trivial_consistency sys1_eq0 = true.
Proof.
  intros n sys sol sys_lt0 sys_eq0 sys_gt0 sys1_lt0 sys1_eq0 sys1_gt0 Hpart_sys Hsol Hpart_sys1.
  pose proof (partition_inequalities_eq0 _ _ _ _ _ Hpart_sys1) as Heq0.
  rewrite <- (insert_partition _ _ _ sys_lt0 sys_eq0 sys_gt0) in Hpart_sys1; last apply Hpart_sys.
  injection Hpart_sys1; intros Hsys1_gt0 Hsys1_eq0 Hsys1_lt0.
  clear Hpart_sys; clear Hpart_sys1.
  rewrite Hsys1_eq0; clear Hsys1_eq0.
  induction sys_eq0; first reflexivity.
  rewrite insert_solution_cons.
  rewrite insert_solution_single; unfold app.
  unfold trivial_consistency; fold (trivial_consistency).
  rewrite <- (is_linear_system_solution_cons (S n) a sys_eq0 sol) in Hsol.
  destruct Hsol as [Ha Hsol].
  apply andb_true_intro; split.
  * unfold is_linear_system_solution in Ha.
    unfold interpret_inequalities in Ha.
    unfold insert_solution_ineq.
    unfold interpret_inequality in Ha.
    apply Ha. 
  * apply IHsys_eq0.
    apply Hsol. 
Qed.

Lemma compute_lb_exists:
  forall n (sys: LinearSystem (S (S n))) sol lb,
    Some lb = compute_lb (insert_solution sys sol) ->
    exists ineq, In ineq sys /\ lb = - ((insert_solution_ineq ineq sol) 0%nat / (insert_solution_ineq ineq sol) 1%nat).
Proof.
  intros n sys.
  induction sys; intros sol lb Hlb.
  * unfold insert_solution, compute_lb, map, RSOPM_list_max in Hlb.
    discriminate. 
  * rewrite insert_solution_cons in Hlb.
    rewrite insert_solution_single in Hlb.
    unfold app in Hlb.
    unfold compute_lb in Hlb.
    rewrite map_cons in Hlb.
    unfold RSOPM_list_max in Hlb. fold RSOPM_list_max in Hlb.
    destruct (RSOPM_list_max (map _ (insert_solution sys sol))) eqn:Hmax_prev.
    * destruct (- (insert_solution_ineq a sol 0%nat / insert_solution_ineq a sol 1%nat) <= t) eqn:Hdec.
      - specialize (IHsys sol t).
        symmetry in Hmax_prev.
        unfold compute_lb in IHsys.
        specialize (IHsys Hmax_prev).
        destruct IHsys as [ineq_past Hpast].
        exists ineq_past; split.
        * apply in_cons; apply Hpast.
        * injection Hlb; intros Hlb_def.
          rewrite Hlb_def.
          apply Hpast.
      - exists a; split.
        - apply in_eq.
        - injection Hlb; intros Hlb_def.
          unfold insert_solution_ineq.
          unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
          apply Hlb_def.  
    * exists a; split.
      - apply in_eq.
      - injection Hlb; intros Hlb_def.
        unfold insert_solution_ineq.
        unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
        apply Hlb_def. 
Qed.

Lemma compute_ub_exists:
  forall n (sys: LinearSystem (S (S n))) sol ub,
    Some ub = compute_ub (insert_solution sys sol) ->
    exists ineq, In ineq sys /\ ub = - ((insert_solution_ineq ineq sol) 0%nat / (insert_solution_ineq ineq sol) 1%nat).
Proof.
  intros n sys.
  induction sys; intros sol ub Hub.
  * unfold insert_solution, compute_ub, map, RSOPM_list_min in Hub.
    discriminate. 
  * rewrite insert_solution_cons in Hub.
    rewrite insert_solution_single in Hub.
    unfold app in Hub.
    unfold compute_ub in Hub.
    rewrite map_cons in Hub.
    unfold RSOPM_list_min in Hub. fold RSOPM_list_min in Hub.
    destruct (RSOPM_list_min (map _ (insert_solution sys sol))) eqn:Hmin_prev.
    * destruct (- (insert_solution_ineq a sol 0%nat / insert_solution_ineq a sol 1%nat) <= t) eqn:Hdec.
      - exists a; split.
        - apply in_eq.
        - injection Hub; intros Hub_def.
          unfold insert_solution_ineq.
          unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
          apply Hub_def.  
      - specialize (IHsys sol t).
        symmetry in Hmin_prev.
        unfold compute_ub in IHsys.
        specialize (IHsys Hmin_prev).
        destruct IHsys as [ineq_past Hpast].
        exists ineq_past; split.
        * apply in_cons; apply Hpast.
        * injection Hub; intros Hub_def.
          rewrite Hub_def.
          apply Hpast.
    * exists a; split.
      - apply in_eq.
      - injection Hub; intros Hub_def.
        unfold insert_solution_ineq.
        unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
        apply Hub_def. 
Qed.

Lemma compose_inequalities_in:
    forall n (sys1 sys2: LinearSystem (S n)) ineq1 ineq2,
      In ineq1 sys1 -> In ineq2 sys2 ->
      forall ineq,
        In ineq (compose_inequalities [ineq1] [ineq2]) ->
        In ineq (compose_inequalities sys1 sys2).
Proof.
  intros n sys1 sys2 ineq1 ineq2 HIn1 HIn2 ineq Hin.
  unfold compose_inequalities.
  unfold compose_inequalities in Hin.
  apply in_map_iff.
  apply in_map_iff in Hin.
  destruct Hin as [ineq_compose Hineq_compose].
  exists ineq_compose.
  split; first apply Hineq_compose.
  destruct Hineq_compose as [Htrash Hineq_compose]; clear Htrash.
  destruct ineq_compose as [ineq_c1 ineq_c2].
  apply in_prod_iff in Hineq_compose.
  destruct Hineq_compose as [Hineq_c1 Hineq_c2].
  unfold In in Hineq_c1, Hineq_c2.
  destruct Hineq_c1; last contradiction.
  destruct Hineq_c2; last contradiction.
  apply in_prod.
  * rewrite <- H. apply HIn1.
  * rewrite <- H0. apply HIn2.
Qed.

Lemma is_linear_system_solution_subset:
  forall n (sys1 sys2: LinearSystem n) sol,
    is_linear_system_solution sys2 sol ->
    (forall ineq, In ineq sys1 -> In ineq sys2) ->
    is_linear_system_solution sys1 sol.
Proof.
  intros n sys1 sys2 sol Hsol Hsubset.
  induction sys1; first exact I.
  apply is_linear_system_solution_cons; split.
  * specialize (Hsubset a (in_eq a sys1)).
    unfold is_linear_system_solution, interpret_inequalities; split; last exact I.
    clear IHsys1.
    induction sys2.
    - contradiction Hsubset.
    - apply in_inv in Hsubset.
      destruct Hsubset as [Ha | Ha].
      * rewrite Ha in Hsol.
        apply is_linear_system_solution_cons in Hsol.
        apply Hsol.
      * apply IHsys2.
        - apply is_linear_system_solution_cons in Hsol.
          apply Hsol.
        - apply Ha.
  * apply IHsys1.
    intros ineq Hineq.
    specialize (Hsubset ineq).
    apply (in_cons a) in Hineq.
    apply Hsubset, Hineq.
Qed.

Lemma compose_inequalities_reduce:
  forall n (sys1 sys2: LinearSystem (S (S n))) sol,
    is_linear_system_solution (compose_inequalities sys1 sys2) sol ->
    forall ineq1 ineq2,
      In ineq1 sys1 -> In ineq2 sys2 ->
      is_linear_system_solution (compose_inequalities [ineq1] [ineq2]) sol.
Proof.
  intros n sys1 sys2 sol Hsol ineq1 ineq2 Hin1 Hin2.
  apply (is_linear_system_solution_subset _ (compose_inequalities [ineq1] [ineq2])
    (compose_inequalities sys1 sys2) sol). 
  * apply Hsol.
  * pose proof (compose_inequalities_in (S n) sys1 sys2 ineq1 ineq2 Hin1 Hin2) as Hcompose.
    apply Hcompose.
Qed.

Lemma interpret_inequality_helper_reconstruction:
  forall n e1 e2 sol,
    - interpret_inequality_helper (n:=n) (fun i => (e1 i) / e2) sol =
    interpret_inequality_helper (n:=n) (fun i => (e1 i) / - e2) sol.
Proof.
  intros n e1 e2 sol.
  induction n.
  * unfold interpret_inequality_helper.
    RSOPM_realize_eq; repeat rewrite ax_real_div; RSOPM_realize.
    rewrite Ropp_div_distr_r; reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper (n:=n)).
    specialize (IHn sol).
    rewrite <- IHn.
    RSOPM_realize_eq; repeat rewrite ax_real_div; RSOPM_realize.
    rewrite Ropp_div_distr_r.
    rewrite Ropp_mult_distr_l_reverse.
    rewrite <- Ropp_plus_distr.
    reflexivity.
Qed.

Lemma reconstruction_algebra_helper:
  forall n (lb_ineq ub_ineq: LinearInequality (S (S n))) sol,
    ((interpret_inequality_helper 
    (fun i : nat => lb_ineq i / - lb_ineq (S (S n)) + ub_ineq i / ub_ineq (S (S n))) sol) <= 0) = true ->
    (- (insert_solution_ineq lb_ineq sol 0%nat / insert_solution_ineq lb_ineq sol 1%nat) <=
    - (insert_solution_ineq ub_ineq sol 0%nat / insert_solution_ineq ub_ineq sol 1%nat)) = true.
Proof.
  intros n lb_ineq ub_ineq sol H.
  unfold insert_solution_ineq.
  do 2 rewrite interpret_inequality_helper_div.
  assert (Hhelp: (forall (r1: T RSOPM) r2, (r1 + r2 <= 0) = true -> (r1 <= - r2) = true )%RS). {
    intros r1 r2.
    do 2 rewrite ax_real_leq_true.
    RSOPM_realize.
    lra.
  }
  apply Hhelp; clear Hhelp.
  rewrite interpret_inequality_helper_reconstruction.
  rewrite interpret_inequality_helper_plus.
  apply H.
Qed.

Lemma reconstruction_bounds:
  forall n (sys: LinearSystem (S (S n))) sol sys_lt0 sys_eq0 sys_gt0 lb ub,
    (sys_lt0, sys_eq0, sys_gt0) = partition_inequalities sys ->
    is_linear_system_solution (compose_inequalities sys_lt0 sys_gt0) sol ->
    Some lb = compute_lb (insert_solution sys_lt0 sol) ->
    Some ub = compute_ub (insert_solution sys_gt0 sol) ->
    lb <= ub = true.
Proof.
  intros n sys sol sys_lt0 sys_eq0 sys_gt0 lb ub Hpart Hcompose Hlb Hub.
  apply compute_lb_exists in Hlb.
  apply compute_ub_exists in Hub.
  destruct Hlb as [lb_ineq [Hlbin Hlb]].
  destruct Hub as [ub_ineq [Hubin Hub]].
  pose proof (compose_inequalities_reduce _ _ _ _ Hcompose lb_ineq ub_ineq Hlbin Hubin) as Hineqs.
  unfold compose_inequalities,list_prod, app, map in Hineqs.
  rewrite Hlb, Hub.
  unfold is_linear_system_solution, interpret_inequalities, interpret_inequality in Hineqs.
  apply reconstruction_algebra_helper.
  apply Hineqs.
Qed.

Lemma reconstruction_always_succeds:
  forall n (sys: LinearSystem (S (S n))) sol,
    (exists sol_full, is_linear_system_solution sys sol_full) ->
    is_linear_system_solution (remove_var sys) sol ->
    exists sol1, is_linear_system_solution (insert_solution sys sol) sol1.
Proof.
  intros n sys sol Hfull Hrvar.
  unfold remove_var in Hrvar.
  remember (partition_inequalities sys) as sys_p.
  destruct sys_p as [[sys_lt0 sys_eq0] sys_gt0].
  apply is_linear_system_solution_app in Hrvar.
  destruct Hrvar as [Hcompose Heq0].
  exists (match trivial_extract (insert_solution sys sol) with | Some s => (fun _ => s) | None => (fun _ => 0) end).
  pose proof (trivial_extract_correct (insert_solution sys sol)).
  remember (trivial_extract (insert_solution sys sol)) as ext_res.
  unfold trivial_extract in Heqext_res.
  remember (partition_inequalities (insert_solution sys sol)) as sys1_part.
  destruct sys1_part as [[sys1_lt0 sys1_eq0] sys1_gt0].
  rewrite (trivial_consistency_insert_solution_eq0 
              n sys sol sys_lt0 sys_eq0 sys_gt0 sys1_lt0 sys1_eq0 sys1_gt0 Heqsys_p Heq0 Heqsys1_part) in Heqext_res.
  remember (compute_lb sys1_lt0) as sys1_lbo.
  remember (compute_ub sys1_gt0) as sys1_ubo.
  unfold satisfy_bounds in Heqext_res.
  rewrite <- (insert_partition _ _ _ _ _ _ Heqsys_p) in Heqsys1_part.
  injection Heqsys1_part; intros Hsys1_gt0 Hsys1_eq0 Hsys1_lt0.
  destruct sys1_lbo; destruct sys1_ubo.
  * rewrite (reconstruction_bounds n sys sol sys_lt0 sys_eq0 sys_gt0 t t0) in Heqext_res.
    - rewrite Heqext_res.
      rewrite Heqext_res in H.
      specialize (H (fun _ => t) eq_refl).
      apply H. 
    - apply Heqsys_p.
    - apply Hcompose.
    - rewrite Hsys1_lt0 in Heqsys1_lbo.
      apply Heqsys1_lbo.
    - rewrite Hsys1_gt0 in Heqsys1_ubo.
      apply Heqsys1_ubo.
  * rewrite Heqext_res.
    rewrite Heqext_res in H.
    specialize (H (fun _ => t) eq_refl).
    apply H. 
  * rewrite Heqext_res.
    rewrite Heqext_res in H.
    specialize (H (fun _ => t) eq_refl).
    apply H. 
  * rewrite Heqext_res.
    rewrite Heqext_res in H.
    specialize (H (fun _ => 0) eq_refl).
    apply H. 
Qed.

Fixpoint fme_solve {n: nat} (sys: LinearSystem n)
    : option (LinearSystemSolution n) :=
    match n with
    | 0 => if trivial_consistency sys then Some (fun _ => 0) else None
    | 1 => match trivial_extract sys with
           | Some s => Some (fun _ => s)
           | None => None
           end
    | S i => 
        match fme_solve (n:=i) (remove_var sys) with
        | Some subsol => 
            match trivial_extract (insert_solution sys subsol) with
            | Some s => Some (prepend_to_solution s subsol) 
            | None => None
            end
        | None => None
        end
    end.

Lemma fme_solve_SSn:
    forall n (sys: LinearSystem (S (S n))),
      fme_solve sys = 
        match fme_solve (n:=S n) (remove_var sys) with
        | Some subsol => 
            match trivial_extract (insert_solution sys subsol) with
            | Some s => Some (prepend_to_solution s subsol) 
            | None => None
            end
        | None => None
        end.
Proof.
    intros n sys.
    unfold fme_solve; fold (fme_solve (n:=n)).
    reflexivity. 
Qed.

Theorem fme_correct:
    forall n (sys: LinearSystem n),
        match fme_solve sys with
        | None => ~ exists sol, is_linear_system_solution sys sol
        | Some sol => is_linear_system_solution sys sol
        end.
Proof.
    intros n sys.
    destruct n; last induction n.
    * unfold fme_solve.
      pose proof (trivial_consistency_correct sys) as Htrivial.
      destruct (trivial_consistency sys) eqn:Hresult; apply Htrivial.
    * unfold fme_solve.
      destruct (trivial_extract sys) as [s |] eqn:Htrivial.
      - pose proof (trivial_extract_correct sys) as Hcorrect.
        rewrite Htrivial in Hcorrect.
        apply Hcorrect.
        reflexivity.
      - pose proof (trivial_extract_correct sys) as Hcorrect.
        rewrite Htrivial in Hcorrect.
        apply Hcorrect.
    * rewrite fme_solve_SSn.
      specialize (IHn (remove_var sys)).
      remember (fme_solve (remove_var sys)) as subsol.
      destruct subsol.
      - remember (trivial_extract (insert_solution sys l)) as sol1.
        destruct sol1.
        * pose proof (trivial_extract_correct (insert_solution sys l)) as Htriv.
          rewrite <- Heqsol1 in Htriv.
          specialize (Htriv (fun _ => t) eq_refl).
          apply prepend_insert_split. apply Htriv. 
        * pose proof (trivial_extract_correct (insert_solution sys l)) as Htriv.
          rewrite <- Heqsol1 in Htriv.
          intros Hsol.
          pose proof (reconstruction_always_succeds n sys l Hsol IHn) as Hinsert.
          contradiction.
      - apply remove_var_no_solution.
        apply IHn.  
Qed.     


End FourierMotzkinImplementation.