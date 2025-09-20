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
    c_1 * x_1 + c_2 * x_2 + ... + c_n * x_n + b <= 0 (inclusive)
    or
    c_1 * x_1 + c_2 * x_2 + ... + c_n * x_n + b < 0 (strict)
   is represented as a function from index of a variable
   to its associated coefficient. Zero is mapped to b.
   The parameter n refers to x_n, the variable with the largest index. *)
Inductive LinearInequality (n: nat) := 
| Strict (coeffs: nat -> T RSOPM)
| Inclusive (coeffs: nat -> T RSOPM). 
Definition LinearSystem (n: nat) := list (LinearInequality n).
Definition LinearSystemSolution (n: nat) := nat -> T RSOPM.

Definition ineq_coeffs {n} (ineq: LinearInequality n): nat -> T RSOPM :=
  match ineq with
  | Strict coeffs => coeffs
  | Inclusive coeffs => coeffs
  end.

Definition ineq_rank_change {n} (ineq: LinearInequality n) (new_rank: nat) : LinearInequality new_rank :=
  match ineq with
  | Strict coeffs => Strict new_rank coeffs
  | Inclusive coeffs => Inclusive new_rank coeffs
  end.

Fixpoint interpret_inequality_helper 
    (n: nat) 
    (coeffs: nat -> T RSOPM)
    (sol: LinearSystemSolution n)
    : T RSOPM :=
    match n with
    | 0 => coeffs 0%nat
    | S i => (coeffs n) * (sol n) + interpret_inequality_helper i coeffs sol
    end.

Lemma interpret_inequality_helper_plus:
  forall n coeffs1 coeffs2 sol,
    interpret_inequality_helper n coeffs1 sol + interpret_inequality_helper n coeffs2 sol =
    interpret_inequality_helper n (fun i => coeffs1 i + coeffs2 i) sol.
Proof.
  intros n coeffs1 coeffs2 sol.
  induction n.
  * unfold interpret_inequality_helper.
    RSOPM_realize_eq.
    rewrite Rplus_comm. reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper n).
    specialize (IHn sol).
    rewrite <- IHn.
    RSOPM_realize_eq.
    lra.
Qed.

Lemma interpret_inequality_helper_div:
  forall n (coeffs: nat -> T RSOPM) c sol,
    interpret_inequality_helper n coeffs sol / c = interpret_inequality_helper n (fun i => coeffs i / c) sol.
Proof.
  intros n coeffs c sol.
  induction n.
  * unfold interpret_inequality_helper.
    RSOPM_realize_eq.
    repeat rewrite ax_real_div.
    apply Rdiv_eq_compat_r; reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper n).
    specialize (IHn sol).
    rewrite <- IHn.
    RSOPM_realize_eq.
    repeat (RSOPM_realize; rewrite ax_real_div).
    lra.
Qed.

Definition interpret_inequality {n: nat} 
    (ineq: LinearInequality n) 
    (sol: LinearSystemSolution n)
    : Prop :=
    match ineq with
    | Strict coeffs => ((0 <= interpret_inequality_helper n coeffs sol) = false)
    | Inclusive coeffs => ((interpret_inequality_helper n coeffs sol <= 0) = true)
    end.

Lemma interpret_inequality_first_zero:
  forall n (ineq: LinearInequality (S n)) sol,
    (ineq_coeffs ineq) (S n) = 0 ->
    interpret_inequality (n:=S n) ineq sol ->
    interpret_inequality (n:=n) (ineq_rank_change ineq n) sol.
Proof.
  intros n ineq sol H0 H.
  unfold interpret_inequality, interpret_inequality_helper in H; fold (interpret_inequality_helper n) in H.
  unfold ineq_rank_change; unfold ineq_coeffs in H0.
  destruct ineq.
  * rewrite H0 in H.
    apply ax_real_leq_false in H.
    rewrite ax_real_plus, ax_real_mult, ax_zero_is_zero in H.
    rewrite Rmult_0_l, Rplus_0_l in H.
    apply ax_real_leq_false; rewrite ax_zero_is_zero.
    apply H.
  * rewrite H0 in H.
    apply ax_real_leq_true in H.
    rewrite ax_real_plus, ax_real_mult, ax_zero_is_zero in H.
    rewrite Rmult_0_l, Rplus_0_l in H.
    apply ax_real_leq_true; rewrite ax_zero_is_zero.
    apply H.
Qed.

Definition ineq_plus {n} (ineq1 ineq2: LinearInequality n) :=
match ineq1, ineq2 with
| Inclusive coeffs1, Inclusive coeffs2 => Inclusive n (fun i => coeffs1 i + coeffs2 i)
| Strict coeffs1, Inclusive coeffs2 => Strict n (fun i => coeffs1 i + coeffs2 i)
| Inclusive coeffs1, Strict coeffs2 => Strict n (fun i => coeffs1 i + coeffs2 i)
| Strict coeffs1, Strict coeffs2 => Strict n (fun i => coeffs1 i + coeffs2 i)
end.

Lemma interpet_inequality_plus:
  forall n (ineq1 ineq2: LinearInequality n) sol,
    interpret_inequality ineq1 sol ->
    interpret_inequality ineq2 sol ->
    interpret_inequality (ineq_plus ineq1 ineq2) sol.
Proof.
  intros n ineq1 ineq2 sol Hineq1 Hineq2.
  unfold interpret_inequality, ineq_plus. 
  unfold interpret_inequality in Hineq1, Hineq2.
  destruct ineq1; destruct ineq2; rewrite <- interpret_inequality_helper_plus.
  * apply ax_real_leq_false; apply ax_real_leq_false in Hineq1, Hineq2.
    rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hineq1, Hineq2.
    rewrite ax_real_plus; lra.    
  * apply ax_real_leq_false; apply ax_real_leq_false in Hineq1; apply ax_real_leq_true in Hineq2.
    rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hineq1, Hineq2.
    rewrite ax_real_plus; lra.
  * apply ax_real_leq_false; apply ax_real_leq_true in Hineq1; apply ax_real_leq_false in Hineq2.
    rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hineq1, Hineq2.
    rewrite ax_real_plus; lra.
  * apply ax_real_leq_true; apply ax_real_leq_true in Hineq1; apply ax_real_leq_true in Hineq2.
    rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hineq1, Hineq2.
    rewrite ax_real_plus; lra.
Qed.

Definition ineq_constdiv {n} (ineq: LinearInequality n) (c: T RSOPM) :=
  match ineq with
  | Strict coeffs => Strict n (fun i => coeffs i / c)
  | Inclusive coeffs => Inclusive n (fun i => coeffs i / c)
  end.

Lemma interpret_inequality_div:
  forall n (ineq: LinearInequality n) c sol,
    (c <= 0) = false ->
    interpret_inequality ineq sol ->
    interpret_inequality (ineq_constdiv ineq c) sol.
Proof.
  intros n ineq c sol Hc H.
  unfold interpret_inequality, ineq_constdiv.
  destruct ineq; rewrite <- interpret_inequality_helper_div.
  * unfold interpret_inequality in H.
    apply ax_real_leq_false. rewrite ax_real_div.
    apply ax_real_leq_false in Hc.
    apply ax_real_leq_false in H.
    rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hc, H.
    apply Rdiv_neg_pos; lra.
  * unfold interpret_inequality in H.
    apply ax_real_leq_true. rewrite ax_real_div.
    apply ax_real_leq_false in Hc.
    apply ax_real_leq_true in H.
    rewrite ax_zero_is_zero; rewrite ax_zero_is_zero in Hc, H.
    unfold Rle. unfold Rle in H.
    destruct H as [H|H].
    - left. apply Rdiv_neg_pos; lra.
    - right. nra. 
Qed.

Definition ineq_compose {n} (ineq1 ineq2: LinearInequality (S n)): LinearInequality n :=
  ineq_rank_change
    ( ineq_plus
        (ineq_constdiv ineq1 (RSopp ((ineq_coeffs ineq1) (S n))))
        (ineq_constdiv ineq2 ((ineq_coeffs ineq2) (S n)))
    ) n.

Lemma interpret_inequality_compose:
  forall n (ineq1 ineq2: LinearInequality (S n)) sol,
      (0 <= (ineq_coeffs ineq1) (S n)) = false ->
      ((ineq_coeffs ineq2) (S n) <= 0) = false ->
      interpret_inequality (n:= S n) ineq1 sol ->
      interpret_inequality (n:= S n) ineq2 sol ->
      interpret_inequality (n:=n) (ineq_compose ineq1 ineq2) sol.
Proof.
  intros n ineq1 ineq2 sol Hineq1 Hineq2 Hineq1_sol Hineq2_sol.
  unfold ineq_compose.
  apply interpret_inequality_first_zero.
  - unfold ineq_coeffs in Hineq1, Hineq2.
    apply ax_equality; rewrite ax_zero_is_zero.
    unfold ineq_coeffs, ineq_plus, ineq_constdiv.
    destruct ineq1; destruct ineq2.
    1-4: rewrite ax_real_plus, ax_real_div, ax_real_div, ax_opp_is_opp.
    1-4: apply ax_real_leq_false in Hineq1, Hineq2.
    1-4: rewrite ax_zero_is_zero in Hineq1, Hineq2.
    1-4: rewrite Rdiv_diag; last lra. 
    1-4: rewrite Rdiv_opp_r, Rdiv_diag; last lra.
    1-4: rewrite Rplus_opp_l; reflexivity.
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

Definition system_rank_change {n} (sys: LinearSystem n) (rank: nat): LinearSystem rank :=
  map (fun ineq => ineq_rank_change ineq rank) sys.

Lemma system_rank_change_cons:
  forall n ineq (sys: LinearSystem n) new_rank,
    system_rank_change (ineq :: sys) new_rank =
    ineq_rank_change ineq new_rank :: system_rank_change sys new_rank.
Proof.
  intros n ineq sys new_rank.
  unfold system_rank_change.
  apply map_cons.
Qed.

Lemma system_rank_change_id:
  forall n (sys: LinearSystem n),
    system_rank_change sys n = sys.
Proof.
  intros n sys.
  induction sys.
  * unfold system_rank_change; reflexivity.
  * unfold system_rank_change.
    rewrite map_cons.
    rewrite <- IHsys at 2; f_equal.
    unfold ineq_rank_change.
    destruct a; reflexivity.
Qed.

Fixpoint trivial_consistency (sys: LinearSystem 0): bool :=
match sys with
| nil => true
| ineq :: tail => 
    match ineq with
    | Strict coeffs => andb (negb (0 <= coeffs 0%nat)) (trivial_consistency tail) 
    | Inclusive coeffs => andb (coeffs 0%nat <= 0) (trivial_consistency tail)
    end
end.

Lemma trivial_consistency_cons:
    forall (ineq: LinearInequality 0) sys,
        (trivial_consistency [ineq] = true /\ trivial_consistency sys = true) <->
        trivial_consistency (ineq :: sys) = true.
Proof.
    intros ineq sys. 
    split.
    * intros H; destruct H as [Hhead Htail].
      unfold trivial_consistency.
      destruct ineq; fold (trivial_consistency sys).
      1-2: apply andb_true_intro; split.
      - 2,4: apply Htail.
      - 1,2: unfold trivial_consistency in Hhead.
        1,2: rewrite Bool.andb_true_r in Hhead; apply Hhead.
    * intro H.
      unfold trivial_consistency in H.
      destruct ineq; fold (trivial_consistency sys) in H.
      - all: apply andb_prop in H.
        all: split; unfold trivial_consistency.
        - 1,3: rewrite Bool.andb_true_r; apply H.  
        - all: apply H.
Qed.

Lemma trivial_consistency_andb:
    forall ineq sys,
    trivial_consistency (ineq :: sys) = 
        andb (trivial_consistency [ineq]) (trivial_consistency sys).
Proof.
    intros ineq sys.
    unfold trivial_consistency.
    destruct ineq; fold (trivial_consistency sys).
    all: rewrite Bool.andb_true_r; reflexivity.
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
    destruct ineq.
    all: rewrite Bool.andb_true_r; split; intro H.
    all: try easy.
    * apply negb_true_iff in H; easy. 
    * apply negb_true_iff; easy.
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
    let (le0, gt0) := partition (fun ineq => (ineq_coeffs ineq) n <= 0) sys in
    let (eq0, lt0) := partition (fun ineq => 0 <= (ineq_coeffs ineq) n) le0 in
    (lt0, eq0, gt0).

Lemma partition_inequalities_cons:
    forall n (ineq: LinearInequality n) sys,
        let (p_sys, gt0_sys) := partition_inequalities sys in
        let (lt0_sys, eq0_sys) := p_sys in
        let (p_is, gt0_is) := partition_inequalities (ineq :: sys) in
        let (lt0_is, eq0_is) := p_is in
        ((ineq_coeffs ineq) n <= 0 = true /\ 0 <= (ineq_coeffs ineq) n = true /\
         lt0_is = lt0_sys /\ gt0_is = gt0_sys /\ eq0_is = ineq :: eq0_sys) \/ 
        ((ineq_coeffs ineq) n <= 0 = true /\ 0 <= (ineq_coeffs ineq) n = false /\  
         lt0_is = ineq :: lt0_sys /\ gt0_is = gt0_sys /\ eq0_is = eq0_sys) \/ 
        ((ineq_coeffs ineq) n <= 0 = false /\ 0 <= (ineq_coeffs ineq) n = true /\ 
         lt0_is = lt0_sys /\ gt0_is = ineq :: gt0_sys /\ eq0_is = eq0_sys).
Proof.
    (* This proof surely requires some automation *)
    intros n ineq sys.
    destruct (partition_inequalities sys) 
        as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
    destruct (partition_inequalities (ineq :: sys)) 
        as [[lt0_is eq0_is] gt0_is] eqn:Hpart_is.
    destruct ((ineq_coeffs ineq) n <= 0) eqn:Hle0; destruct (0 <= (ineq_coeffs ineq) n) eqn:Hge0.
    all: (
        unfold partition_inequalities in Hpart_is;
        destruct (partition (fun i => (ineq_coeffs i) n <= 0) (ineq :: sys)) 
            as [p_le0_is p_gt0_is] eqn:Hpart1_is;
        destruct (partition (fun i => 0 <= (ineq_coeffs i) n) p_le0_is) 
            as [p_eq0_is p_lt0_is] eqn:Hpart2_is;
        unfold partition_inequalities in Hpart_sys;
        destruct (partition (fun i => (ineq_coeffs i) n <= 0) sys) 
            as [p_le0_sys p_gt0_sys] eqn:Hpart1_sys;
        destruct (partition (fun i => 0 <= (ineq_coeffs i) n) p_le0_sys) 
            as [p_eq0_sys p_lt0_sys] eqn:Hpart2_sys
    ).
    * left.
      pose proof (partition_cons1 _ ineq _ Hpart1_sys Hle0) as Hderived1.
      assert (Hhelp1: ((ineq :: p_le0_sys, p_gt0_sys) = (p_le0_is, p_gt0_is))). {
          apply (eq_ind (partition (fun i => (ineq_coeffs i) n <= 0) (ineq :: sys)) 
              (fun a => a = (p_le0_is, p_gt0_is)) Hpart1_is).
          apply Hderived1.
      } 
      apply pair_equal_spec in Hhelp1; destruct Hhelp1 as [Hderived2 Hderived3].
      rewrite <- Hderived2 in Hpart2_is.
      pose proof (partition_cons1 _ ineq _ Hpart2_sys Hge0) as Hderived4.
      assert (Hhelp2: ((ineq :: p_eq0_sys, p_lt0_sys) = (p_eq0_is, p_lt0_is))). {
          apply (eq_ind (partition (fun i => 0 <= (ineq_coeffs i) n) (ineq :: p_le0_sys)) 
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
          apply (eq_ind (partition (fun i => (ineq_coeffs i) n <= 0) (ineq :: sys)) 
              (fun a => a = (p_le0_is, p_gt0_is)) Hpart1_is).
          apply Hderived1.
      } 
      apply pair_equal_spec in Hhelp1; destruct Hhelp1 as [Hderived2 Hderived3].
      rewrite <- Hderived2 in Hpart2_is.
      pose proof (partition_cons2 _ ineq _ Hpart2_sys Hge0) as Hderived4.
      assert (Hhelp2: ((p_eq0_sys, ineq :: p_lt0_sys) = (p_eq0_is, p_lt0_is))). {
          apply (eq_ind (partition (fun i => 0 <= (ineq_coeffs i) n) (ineq :: p_le0_sys)) 
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
          apply (eq_ind (partition (fun i => (ineq_coeffs i) n <= 0) (ineq :: sys)) 
              (fun a => a = (p_le0_is, p_gt0_is)) Hpart1_is).
          apply Hderived1.
      } 
      apply pair_equal_spec in Hhelp1; destruct Hhelp1 as [Hderived2 Hderived3].
      rewrite <- Hderived2 in Hpart2_is.
      assert (Hhelp2: ((p_eq0_sys, p_lt0_sys) = (p_eq0_is, p_lt0_is))). {
          apply (eq_ind (partition (fun i => 0 <= (ineq_coeffs i) n) p_le0_sys) 
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
      In ineq lt0 -> (0 <= (ineq_coeffs ineq) n) = false.
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
      In ineq lt0 -> (0 <= (ineq_coeffs ineq) n) = false.
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
      In ineq gt0 -> ((ineq_coeffs ineq) n <= 0) = false.
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
      (ineq_coeffs ineq) n <= 0 = true /\ 0 <= (ineq_coeffs ineq) n = false ->
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
      (ineq_coeffs ineq) n <= 0 = true /\ 0 <= (ineq_coeffs ineq) n = true ->
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
      (ineq_coeffs ineq) n <= 0 = false /\ 0 <= (ineq_coeffs ineq) n = true ->
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
        is_linear_system_solution (system_rank_change eq0 n) sol).
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
  destruct (partition (fun ineq => ineq_coeffs ineq (S n) <= 0) (a :: sys)).
  destruct (partition (fun ineq => 0 <= ineq_coeffs ineq (S n))).
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
    fold interpret_inequality_helper in H1.
    unfold interpret_inequality.
    assert ((ineq_coeffs a) (S n) = 0).
    apply RSOPM_le_and_le_eq.
    split. exact Ha1. exact Ha2.
    destruct a.
    1,2: unfold ineq_coeffs in H; unfold ineq_rank_change.
    1,2: rewrite H in H1.
    1,2: rewrite RSOPM_0_mult in H1.
    1,2: rewrite RSOPM_plus_comm in H1.
    1,2: rewrite RSOPM_plus_0_r in H1.
    1,2: exact H1.
    exact H2.
    intro.
    destruct H as [H1 H2].
    split.
    unfold interpret_inequality.
    unfold interpret_inequality_helper.
    fold (interpret_inequality_helper n).
    assert ((ineq_coeffs a) (S n) = 0).
    apply RSOPM_le_and_le_eq.
    split. exact Ha1. exact Ha2.
    destruct a.
    1,2: unfold ineq_coeffs in H.
    1,2: rewrite H.
    1,2: rewrite RSOPM_0_mult.
    1,2: rewrite RSOPM_plus_comm.
    1,2: rewrite RSOPM_plus_0_r.
    1,2: exact H1.
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
        trivial_consistency (system_rank_change eq0 0%nat) = true ->
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
        rewrite system_rank_change_cons in Htriv_cons.
        destruct a; unfold ineq_rank_change in Htriv_cons.
        1,2: unfold trivial_consistency in Htriv_cons. 
        1,2: apply Bool.andb_true_iff in Htriv_cons.
        1,2: fold trivial_consistency in Htriv_cons.
        1,2: destruct Htriv_cons as [Ha_cons Htriv_cons].
        1,2: apply is_linear_system_solution_cons; split.
        1,3: unfold is_linear_system_solution, interpret_inequalities,
          interpret_inequality, interpret_inequality_helper; split; last easy.
        1,3: apply ax_real_leq_true in Ha_le0, Ha_ge0.
        * apply ax_real_leq_false; RSOPM_realize.
          rewrite ax_zero_is_zero in Ha_le0, Ha_ge0.
          unfold ineq_coeffs in Ha_le0, Ha_ge0.
          assert (INJ_RSOPM RSOPM (coeffs 1%nat) = 0%R) as Hhelp. lra.
          rewrite Hhelp. field_simplify.
          apply negb_true_iff in Ha_cons.
          apply ax_real_leq_false in Ha_cons.
          rewrite ax_zero_is_zero in Ha_cons.
          apply Ha_cons.
        * specialize (IHsys lt0_sys eq0_sys gt0_sys sol).
          apply IHsys.
          - reflexivity.
          - apply Htriv_cons.
        * apply ax_real_leq_true in Ha_le0, Ha_ge0.
          apply ax_real_leq_true; RSOPM_realize.
          rewrite ax_zero_is_zero in Ha_le0, Ha_ge0.
          unfold ineq_coeffs in Ha_le0, Ha_ge0.
          assert (INJ_RSOPM RSOPM (coeffs 1%nat) = 0%R) as Hhelp. lra.
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

Inductive SolutionBound :=
| Unbounded
| StrictBound (value: T RSOPM)
| InclusiveBound (value: T RSOPM).

Fixpoint compute_lb (lt0_partition: LinearSystem 1): SolutionBound :=
  match lt0_partition with
  | nil => Unbounded
  | ineq :: rest => 
      let candidate_bound := (- (ineq_coeffs ineq 0%nat / ineq_coeffs ineq 1%nat)) in
      match ineq, (compute_lb rest) with
      | Strict coeffs, Unbounded => 
          StrictBound candidate_bound
      | Strict coeffs, StrictBound rest_bound =>
          if rest_bound <= candidate_bound then StrictBound candidate_bound else StrictBound rest_bound
      | Strict coeffs, InclusiveBound rest_bound =>
          if rest_bound <= candidate_bound then StrictBound candidate_bound else  InclusiveBound rest_bound
      | Inclusive coeffs, Unbounded =>
          InclusiveBound candidate_bound
      | Inclusive coeffs, StrictBound rest_bound =>
          if candidate_bound <= rest_bound then StrictBound rest_bound else InclusiveBound candidate_bound 
      | Inclusive coeffs, InclusiveBound rest_bound =>
          if rest_bound <= candidate_bound then InclusiveBound candidate_bound else InclusiveBound rest_bound
      end
  end.

Lemma compute_lb_finds_solution:
  forall sys sol lt0 eq0 gt0,
      (lt0, eq0, gt0) = partition_inequalities sys ->
      match (compute_lb lt0) with
      | Unbounded => True
      | StrictBound lb => sol 1%nat <= lb = false
      | InclusiveBound lb => lb <= sol 1%nat = true
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
    - rewrite Hlt0 in H; rewrite Hlt0.
      apply is_linear_system_solution_cons.
      destruct a eqn:Ha; unfold compute_lb in H; fold (compute_lb lt0_sys) in H; destruct (compute_lb lt0_sys) eqn:Hlb.
      * split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in H, Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_false; RSOPM_realize.
          rewrite <- Rdiv_opp_r in H.
          rewrite Rcomplements.Rlt_div_l in H; last lra.
          apply Rlt_minus in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          unfold Rminus in H.
          rewrite Ropp_involutive in H.
          rewrite Rplus_comm in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys; exact I.
      * unfold ineq_coeffs in H.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hval; split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in H, Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_false; RSOPM_realize.
          rewrite <- Rdiv_opp_r in H.
          rewrite Rcomplements.Rlt_div_l in H; last lra.
          apply Rlt_minus in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          unfold Rminus in H.
          rewrite Ropp_involutive in H.
          rewrite Rplus_comm in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys.
          apply ax_real_leq_true in Hval.
          apply ax_real_leq_false in H.
          apply ax_real_leq_false.
          lra.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_false in Hval.
          rewrite ax_real_leq_false in H.
          pose proof (Rlt_trans _ _ _ Hval H) as Hfinal.
          rewrite ax_real_leq_false; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in Hfinal.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r in Hfinal.
          rewrite Rcomplements.Rlt_div_l in Hfinal; last lra.
          apply Rlt_minus in Hfinal.
          rewrite Ropp_mult_distr_r_reverse in Hfinal.
          unfold Rminus in Hfinal.
          rewrite Ropp_involutive in Hfinal.
          rewrite Rplus_comm in Hfinal.
          rewrite Rmult_comm in Hfinal.       
          apply Hfinal.
        - apply (IHsys H).
      * unfold ineq_coeffs in H.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hval; split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in H, Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_false; RSOPM_realize.
          rewrite <- Rdiv_opp_r in H.
          rewrite Rcomplements.Rlt_div_l in H; last lra.
          apply Rlt_minus in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          unfold Rminus in H.
          rewrite Ropp_involutive in H.
          rewrite Rplus_comm in H.
          rewrite Rmult_comm in H.
          apply H.   
        - apply IHsys.
          apply ax_real_leq_true in Hval.
          apply ax_real_leq_false in H.
          apply ax_real_leq_true.
          lra.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_false in Hval.
          rewrite ax_real_leq_true in H.
          assert (Hfinal: (forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 < r3)%R). {
            intros r1 r2 r3 H1 H2. lra.
          }
          specialize (Hfinal _ _ _ Hval H).
          rewrite ax_real_leq_false; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in Hfinal.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r in Hfinal.
          rewrite Rcomplements.Rlt_div_l in Hfinal; last lra.
          apply Rlt_minus in Hfinal.
          rewrite Ropp_mult_distr_r_reverse in Hfinal.
          unfold Rminus in Hfinal.
          rewrite Ropp_involutive in Hfinal.
          rewrite Rplus_comm in Hfinal.
          rewrite Rmult_comm in Hfinal.       
          apply Hfinal.
        - apply (IHsys H).   
      * split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in Ha2.
          apply ax_real_leq_true in H.
          rewrite ax_zero_is_zero in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_true; RSOPM_realize.
          rewrite <- Rdiv_opp_r in H.
          rewrite Rcomplements.Rle_div_l in H; last lra.
          apply Rle_minus in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          unfold Rminus in H.
          rewrite Ropp_involutive in H.
          rewrite Rplus_comm in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys; exact I.
      * unfold ineq_coeffs in H.
        destruct ( - (coeffs 0%nat / coeffs 1%nat) <= value) eqn:Hval; split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_true in Hval.
          rewrite ax_real_leq_false in H.
          assert (Hfinal: (forall r1 r2 r3, r1 <= r2 -> r2 < r3 -> r1 <= r3)%R). {
            intros r1 r2 r3 H1 H2. lra.
          }
          specialize (Hfinal _ _ _ Hval H).
          rewrite ax_real_leq_true; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in Hfinal.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r in Hfinal.
          rewrite Rcomplements.Rle_div_l in Hfinal; last lra.
          apply Rle_minus in Hfinal.
          rewrite Ropp_mult_distr_r_reverse in Hfinal.
          unfold Rminus in Hfinal.
          rewrite Ropp_involutive in Hfinal.
          rewrite Rplus_comm in Hfinal.
          rewrite Rmult_comm in Hfinal.       
          apply Hfinal.  
        - apply (IHsys H).
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2. 
          apply ax_real_leq_true in H.
          apply ax_real_leq_false in Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_true; RSOPM_realize.
          rewrite <- Rdiv_opp_r in H.
          rewrite Rcomplements.Rle_div_l in H; last lra.
          apply Rle_minus in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          unfold Rminus in H.
          rewrite Ropp_involutive in H.
          rewrite Rplus_comm in H.
          rewrite Rmult_comm in H.
          apply H.   
        - apply IHsys.
          apply ax_real_leq_false in Hval.
          apply ax_real_leq_true in H.
          apply ax_real_leq_false.
          lra.
      * unfold ineq_coeffs in H.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hval; split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_true in H.
          apply ax_real_leq_false in Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_true; RSOPM_realize.
          rewrite <- Rdiv_opp_r in H.
          rewrite Rcomplements.Rle_div_l in H; last lra.
          apply Rle_minus in H.
          rewrite Ropp_mult_distr_r_reverse in H.
          unfold Rminus in H.
          rewrite Ropp_involutive in H.
          rewrite Rplus_comm in H.
          rewrite Rmult_comm in H.
          apply H.   
        - apply IHsys.
          apply ax_real_leq_true in Hval.
          apply ax_real_leq_true in H.
          apply ax_real_leq_true.
          lra.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_false in Hval.
          rewrite ax_real_leq_true in H.
          assert (Hfinal: (forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 <= r3)%R). {
            intros r1 r2 r3 H1 H2. lra.
          }
          specialize (Hfinal _ _ _ Hval H).
          rewrite ax_real_leq_true; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in Hfinal.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r in Hfinal.
          rewrite Rcomplements.Rle_div_l in Hfinal; last lra.
          apply Rle_minus in Hfinal.
          rewrite Ropp_mult_distr_r_reverse in Hfinal.
          unfold Rminus in Hfinal.
          rewrite Ropp_involutive in Hfinal.
          rewrite Rplus_comm in Hfinal.
          rewrite Rmult_comm in Hfinal.       
          apply Hfinal.
        - apply (IHsys H).
    - rewrite Hlt0 in H.
      specialize (IHsys H).
      rewrite <- Hlt0 in IHsys. 
      apply IHsys.    
Qed.

Lemma compute_lb_sound : 
  forall sys sol lt0 eq0 gt0,
    (lt0, eq0, gt0) = partition_inequalities sys ->
    match (compute_lb lt0) with
    | Unbounded => True
    | StrictBound lb => 
        (sol 1%nat <= lb = true) -> (~ is_linear_system_solution lt0 sol)
    | InclusiveBound lb =>
        (lb <= sol 1%nat = false) -> (~ is_linear_system_solution lt0 sol)
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
    unfold compute_lb; exact I.
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
      unfold compute_lb; fold (compute_lb lt0_sys).
      destruct a; destruct (compute_lb lt0_sys).
      * intros Hformula Hsol.
        apply is_linear_system_solution_cons in Hsol.
        destruct Hsol as [Ha Hsol].
        unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                interpret_inequality_helper in Ha.
        destruct Ha as [Ha Hclear]; clear Hclear.
        apply ax_real_leq_false in Ha.
        apply ax_real_leq_true in Hformula.
        apply ax_real_leq_false in Ha2.
        rewrite ax_opp_is_opp, ax_real_div in Hformula.
        rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
        rewrite ax_zero_is_zero in Ha2.
        rewrite <- Rdiv_opp_r, <- Rcomplements.Rle_div_r in Hformula; try lra.
        unfold ineq_coeffs in Hformula; lra.
      * unfold ineq_coeffs.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; intros Hformula Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                  interpret_inequality_helper in Ha.
          apply ax_real_leq_false in Ha.
          apply ax_real_leq_true in Hformula.
          apply ax_real_leq_false in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in Hformula.
          rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
          unfold ineq_coeffs in Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r, <- Rcomplements.Rle_div_r in Hformula; try lra.          
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          apply (IHsys Hformula), Hsol.
      * unfold ineq_coeffs.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; intros Hformula Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                  interpret_inequality_helper in Ha.
          apply ax_real_leq_false in Ha.
          apply ax_real_leq_true in Hformula.
          apply ax_real_leq_false in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in Hformula.
          rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
          unfold ineq_coeffs in Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r, <- Rcomplements.Rle_div_r in Hformula; try lra.        
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          apply (IHsys Hformula), Hsol.
      * intros Hformula Hsol.
        apply is_linear_system_solution_cons in Hsol.
        destruct Hsol as [Ha Hsol].
        unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                interpret_inequality_helper in Ha.
        destruct Ha as [Ha Hclear]; clear Hclear.
        apply ax_real_leq_true in Ha.
        apply ax_real_leq_false in Hformula.
        apply ax_real_leq_false in Ha2.
        rewrite ax_opp_is_opp, ax_real_div in Hformula.
        rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
        rewrite ax_zero_is_zero in Ha2.
        rewrite <- Rdiv_opp_r, <- Rcomplements.Rlt_div_r in Hformula; try lra.
        unfold ineq_coeffs in Hformula; lra.
      * unfold ineq_coeffs.
        destruct (- (coeffs 0%nat / coeffs 1%nat) <= value) eqn:Hcoeffs; intros Hformula Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          apply (IHsys Hformula), Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                  interpret_inequality_helper in Ha.
          apply ax_real_leq_true in Ha.
          apply ax_real_leq_false in Hformula.
          apply ax_real_leq_false in Ha2.
          unfold ineq_coeffs in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in Hformula.
          rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
          rewrite ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r, <- Rcomplements.Rlt_div_r in Hformula; try lra.    
      * unfold ineq_coeffs.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; intros Hformula Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                  interpret_inequality_helper in Ha.
          apply ax_real_leq_true in Ha.
          apply ax_real_leq_false in Hformula.
          apply ax_real_leq_false in Ha2.
          rewrite ax_opp_is_opp, ax_real_div in Hformula.
          rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
          unfold ineq_coeffs in Ha2.
          rewrite ax_zero_is_zero in Ha2.
          rewrite <- Rdiv_opp_r, <- Rcomplements.Rlt_div_r in Hformula; try lra.      
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          apply (IHsys Hformula), Hsol.
    - rewrite Hlt0.
      apply IHsys.
Qed.

Lemma compute_lb_monotone:
  forall head tail,
      match compute_lb tail, compute_lb (head :: tail) with
      | StrictBound lb1, StrictBound lb2 => lb1 <= lb2 = true
      | StrictBound lb1, InclusiveBound lb2 => lb2 <= lb1 = false
      | InclusiveBound lb1, StrictBound lb2 => lb1 <= lb2 = true
      | InclusiveBound lb1, InclusiveBound lb2 => lb1 <= lb2 = true
      | _, _ => True
      end.
Proof.
  intros head tail.
  destruct (compute_lb tail) eqn:Hlb_tail; destruct (compute_lb (head :: tail)) eqn:Hlb_head; try (exact I).
  * unfold compute_lb in Hlb_head; fold (compute_lb tail) in Hlb_head.
    destruct head; rewrite Hlb_tail in Hlb_head; unfold ineq_coeffs in Hlb_head.
    - destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; inversion Hlb_head.
      * apply Hcoeffs.
      * apply ax_real_leq_true, Rle_refl.
    - destruct (- (coeffs 0%nat / coeffs 1%nat) <= value) eqn:Hcoeffs; inversion Hlb_head.
      apply ax_real_leq_true, Rle_refl.   
  * unfold compute_lb in Hlb_head; fold (compute_lb tail) in Hlb_head.
    destruct head; rewrite Hlb_tail in Hlb_head; unfold ineq_coeffs in Hlb_head.
    - destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; inversion Hlb_head.
    - destruct (- (coeffs 0%nat / coeffs 1%nat) <= value) eqn:Hcoeffs; inversion Hlb_head.
      apply Hcoeffs.  
  * unfold compute_lb in Hlb_head; fold (compute_lb tail) in Hlb_head.
    destruct head; rewrite Hlb_tail in Hlb_head; unfold ineq_coeffs in Hlb_head.
    - destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; inversion Hlb_head.
      apply Hcoeffs.
    - destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; inversion Hlb_head.
  * unfold compute_lb in Hlb_head; fold (compute_lb tail) in Hlb_head.
    destruct head; rewrite Hlb_tail in Hlb_head; unfold ineq_coeffs in Hlb_head.
    - destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; inversion Hlb_head.
      apply ax_real_leq_true, Rle_refl.
    - destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; inversion Hlb_head.
      * apply Hcoeffs.
      * apply ax_real_leq_true, Rle_refl. 
Qed. 

Fixpoint compute_ub (gt0_partition: LinearSystem 1): SolutionBound :=
  match gt0_partition with
  | nil => Unbounded
  | ineq :: rest => 
      let candidate_bound := (- (ineq_coeffs ineq 0%nat / ineq_coeffs ineq 1%nat)) in
      match ineq, (compute_ub rest) with
      | Strict coeffs, Unbounded => 
          StrictBound candidate_bound
      | Strict coeffs, StrictBound rest_bound =>
          if rest_bound <= candidate_bound then StrictBound rest_bound else StrictBound candidate_bound
      | Strict coeffs, InclusiveBound rest_bound =>
          if candidate_bound <= rest_bound then StrictBound candidate_bound else InclusiveBound rest_bound 
      | Inclusive coeffs, Unbounded =>
          InclusiveBound candidate_bound
      | Inclusive coeffs, StrictBound rest_bound =>
          if rest_bound <= candidate_bound then StrictBound rest_bound else InclusiveBound candidate_bound 
      | Inclusive coeffs, InclusiveBound rest_bound =>
          if rest_bound <= candidate_bound then InclusiveBound rest_bound else InclusiveBound candidate_bound
      end
  end.

Lemma compute_ub_finds_solution:
    forall sys sol lt0 eq0 gt0,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        match (compute_ub gt0) with
        | Unbounded => True
        | StrictBound ub => ub <= sol 1%nat = false
        | InclusiveBound ub => sol 1%nat <= ub = true
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
    - rewrite Hgt0 in H; rewrite Hgt0.
      apply is_linear_system_solution_cons.
      destruct a eqn:Ha; unfold compute_ub in H; fold (compute_ub gt0_sys) in H; destruct (compute_ub gt0_sys) eqn:Hub.
      * split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in H, Ha1.
          rewrite ax_zero_is_zero in Ha1.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_false; RSOPM_realize.
          rewrite <- Rdiv_opp_l in H.
          rewrite <- Rcomplements.Rlt_div_r in H; last lra.
          apply Rlt_minus in H.
          unfold Rminus in H; rewrite Ropp_involutive in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys; exact I.
      * unfold ineq_coeffs in H.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hval; split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_true in Hval.
          rewrite ax_real_leq_false in H.
          assert (Hfinal: (forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 < r3)%R). {
            intros r1 r2 r3 H1 H2. lra.
          }
          specialize (Hfinal _ _ _ H Hval).
          rewrite ax_real_leq_false; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in Hfinal.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha1.
          rewrite <- Rdiv_opp_l in Hfinal.
          rewrite <- Rcomplements.Rlt_div_r in Hfinal; last lra.
          apply Rlt_minus in Hfinal.
          unfold Rminus in Hfinal; rewrite Ropp_involutive in Hfinal.
          rewrite Rmult_comm in Hfinal.
          apply Hfinal.
        - apply (IHsys H).
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in H, Ha1.
          rewrite ax_zero_is_zero in Ha1.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_false; RSOPM_realize.
          rewrite <- Rdiv_opp_l in H.
          rewrite <- Rcomplements.Rlt_div_r in H; last lra.
          apply Rlt_minus in H.
          unfold Rminus in H; rewrite Ropp_involutive in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys.
          apply ax_real_leq_false in Hval.
          apply ax_real_leq_false in H.
          apply ax_real_leq_false.
          lra.
      * unfold ineq_coeffs in H.
        destruct (- (coeffs 0%nat / coeffs 1%nat) <= value) eqn:Hval; split.        
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_true in Hval.
          rewrite ax_real_leq_false in H.
          rewrite ax_real_leq_false; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in H.
          rewrite <- Rdiv_opp_l in H.
          apply ax_real_leq_false in Ha1.
          rewrite ax_zero_is_zero in Ha1.
          rewrite <- Rcomplements.Rlt_div_r in H; last lra.
          apply Rlt_minus in H.
          unfold Rminus in H; rewrite Ropp_involutive in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys.
          apply ax_real_leq_true in Hval.
          apply ax_real_leq_false in H.
          apply ax_real_leq_true.
          lra.  
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_false in Hval, Ha1.
          rewrite ax_real_leq_true in H.
          rewrite ax_real_leq_false; RSOPM_realize.
          assert (Hfinal: (forall r1 r2 r3, r1 <= r2 -> r2 < r3 -> r1 < r3)%R). {
            intros r1 r2 r3 H1 H2. lra.
          }
          specialize (Hfinal _ _ _ H Hval).
          rewrite ax_opp_is_opp, ax_real_div in Hfinal.
          rewrite <- Rdiv_opp_l in Hfinal.
          rewrite ax_zero_is_zero in Ha1.
          rewrite <- Rcomplements.Rlt_div_r in Hfinal; last lra.
          apply Rlt_minus in Hfinal.
          unfold Rminus in Hfinal; rewrite Ropp_involutive in Hfinal.
          rewrite Rmult_comm in Hfinal.
          apply Hfinal.
        - apply (IHsys H).
      * unfold ineq_coeffs in H.
        split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in Ha1.
          apply ax_real_leq_true in H.
          rewrite ax_zero_is_zero in Ha1.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_true; RSOPM_realize.
          rewrite <- Rdiv_opp_l in H.
          rewrite <- Rcomplements.Rle_div_r in H; last lra.
          apply Rle_minus in H.
          unfold Rminus in H; rewrite Ropp_involutive in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys; exact I.
      * unfold ineq_coeffs in H.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hval; split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_true in Hval.
          rewrite ax_real_leq_false in H.
          assert (Hfinal: (forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 <= r3)%R). {
            intros r1 r2 r3 H1 H2. lra.
          }
          specialize (Hfinal _ _ _ H Hval).
          rewrite ax_real_leq_true; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in Hfinal.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha1.
          rewrite <- Rdiv_opp_l in Hfinal.
          rewrite <- Rcomplements.Rle_div_r in Hfinal; last lra.
          apply Rle_minus in Hfinal.
          unfold Rminus in Hfinal; rewrite Ropp_involutive in Hfinal.
          rewrite Rmult_comm in Hfinal.
          apply Hfinal.
        - apply (IHsys H).
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in Ha1.
          rewrite ax_zero_is_zero in Ha1.
          apply ax_real_leq_true in H.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_true; RSOPM_realize.
          rewrite <- Rdiv_opp_l in H.
          rewrite <- Rcomplements.Rle_div_r in H; last lra.
          apply Rle_minus in H.
          unfold Rminus in H; rewrite Ropp_involutive in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys.
          apply ax_real_leq_false in Hval.
          apply ax_real_leq_true in H.
          apply ax_real_leq_false.
          lra.
      * unfold ineq_coeffs in H.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hval; split.
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          rewrite ax_real_leq_true in Hval.
          rewrite ax_real_leq_true in H.
          pose proof (Rle_trans _ _ _ H Hval) as Hfinal.
          rewrite ax_real_leq_true; RSOPM_realize.
          rewrite ax_opp_is_opp, ax_real_div in Hfinal.
          rewrite ax_real_leq_false, ax_zero_is_zero in Ha1.
          rewrite <- Rdiv_opp_l in Hfinal.
          rewrite <- Rcomplements.Rle_div_r in Hfinal; last lra.
          apply Rle_minus in Hfinal.
          unfold Rminus in Hfinal; rewrite Ropp_involutive in Hfinal.
          rewrite Rmult_comm in Hfinal.
          apply Hfinal.
        - apply (IHsys H).
        - unfold is_linear_system_solution, interpret_inequalities, 
                  interpret_inequality, interpret_inequality_helper.
          split; last exact I.
          unfold ineq_coeffs in H, Ha1, Ha2.
          apply ax_real_leq_false in Ha1.
          rewrite ax_zero_is_zero in Ha1.
          apply ax_real_leq_true in H.
          rewrite ax_opp_is_opp, ax_real_div in H.
          apply ax_real_leq_true; RSOPM_realize.
          rewrite <- Rdiv_opp_l in H.
          rewrite <- Rcomplements.Rle_div_r in H; last lra.
          apply Rle_minus in H.
          unfold Rminus in H; rewrite Ropp_involutive in H.
          rewrite Rmult_comm in H.
          apply H.
        - apply IHsys.
          apply ax_real_leq_false in Hval.
          apply ax_real_leq_true in H.
          apply ax_real_leq_true.
          lra.
Qed.

Lemma compute_ub_sound:
  forall sys sol lt0 eq0 gt0,
    (lt0, eq0, gt0) = partition_inequalities sys ->
    match (compute_ub gt0) with
    | Unbounded => True
    | StrictBound ub => 
        (ub <= sol 1%nat = true) -> (~ is_linear_system_solution gt0 sol)
    | InclusiveBound ub =>
        (sol 1%nat <= ub = false) -> (~ is_linear_system_solution gt0 sol)
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
    unfold compute_lb; exact I.
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
      unfold compute_ub; fold (compute_ub gt0_sys).
      destruct a; destruct (compute_ub gt0_sys).
      * intros Hformula Hsol.
        apply is_linear_system_solution_cons in Hsol.
        destruct Hsol as [Ha Hsol].
        unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                interpret_inequality_helper in Ha.
        destruct Ha as [Ha Hclear]; clear Hclear.
        apply ax_real_leq_false in Ha.
        apply ax_real_leq_true in Hformula.
        apply ax_real_leq_false in Ha1.
        rewrite ax_opp_is_opp, ax_real_div in Hformula.
        rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
        rewrite ax_zero_is_zero in Ha1.
        rewrite <- Rdiv_opp_l, Rcomplements.Rle_div_l in Hformula; try lra.
        unfold ineq_coeffs in Hformula; lra.
      * unfold ineq_coeffs.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; intros Hformula Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          apply (IHsys Hformula), Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                  interpret_inequality_helper in Ha.
          apply ax_real_leq_false in Ha.
          apply ax_real_leq_true in Hformula.
          apply ax_real_leq_false in Ha1.
          rewrite ax_opp_is_opp, ax_real_div in Hformula.
          rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
          unfold ineq_coeffs in Ha1.
          rewrite ax_zero_is_zero in Ha1.
          rewrite <- Rdiv_opp_l, Rcomplements.Rle_div_l in Hformula; try lra.          
      * unfold ineq_coeffs.
        destruct (- (coeffs 0%nat / coeffs 1%nat) <= value) eqn:Hcoeffs; intros Hformula Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                  interpret_inequality_helper in Ha.
          apply ax_real_leq_false in Ha.
          apply ax_real_leq_true in Hformula.
          apply ax_real_leq_false in Ha1.
          unfold ineq_coeffs in Ha1.
          rewrite ax_opp_is_opp, ax_real_div in Hformula.
          rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
          rewrite ax_zero_is_zero in Ha1.
          rewrite <- Rdiv_opp_l, Rcomplements.Rle_div_l in Hformula; try lra.   
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          apply (IHsys Hformula), Hsol. 
      * intros Hformula Hsol.
        apply is_linear_system_solution_cons in Hsol.
        destruct Hsol as [Ha Hsol].
        unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                interpret_inequality_helper in Ha.
        destruct Ha as [Ha Hclear]; clear Hclear.
        apply ax_real_leq_true in Ha.
        apply ax_real_leq_false in Hformula.
        apply ax_real_leq_false in Ha1.
        rewrite ax_opp_is_opp, ax_real_div in Hformula.
        rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
        rewrite ax_zero_is_zero in Ha1.
        rewrite <- Rdiv_opp_l, Rcomplements.Rlt_div_l in Hformula; try lra.
        unfold ineq_coeffs in Hformula; lra.
      * unfold ineq_coeffs.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; intros Hformula Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          apply (IHsys Hformula), Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                  interpret_inequality_helper in Ha.
          apply ax_real_leq_true in Ha.
          apply ax_real_leq_false in Hformula.
          apply ax_real_leq_false in Ha1.
          rewrite ax_opp_is_opp, ax_real_div in Hformula.
          rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
          unfold ineq_coeffs in Ha1.
          rewrite ax_zero_is_zero in Ha1.
          rewrite <- Rdiv_opp_l, Rcomplements.Rlt_div_l in Hformula; try lra.     
      * unfold ineq_coeffs.
        destruct (value <= - (coeffs 0%nat / coeffs 1%nat)) eqn:Hcoeffs; intros Hformula Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          apply (IHsys Hformula), Hsol.
        - apply is_linear_system_solution_cons in Hsol.
          destruct Hsol as [[Ha Hclear] Hsol]; clear Hclear.
          unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
                  interpret_inequality_helper in Ha.
          apply ax_real_leq_true in Ha.
          apply ax_real_leq_false in Hformula.
          apply ax_real_leq_false in Ha1.
          rewrite ax_opp_is_opp, ax_real_div in Hformula.
          rewrite ax_zero_is_zero, ax_real_plus, ax_real_mult in Ha.
          unfold ineq_coeffs in Ha1.
          rewrite ax_zero_is_zero in Ha1.
          rewrite <- Rdiv_opp_l, Rcomplements.Rlt_div_l in Hformula; try lra.      
Qed.

Definition satisfy_bounds 
    (lbb: SolutionBound) 
    (ubb: SolutionBound) 
    : option (T RSOPM) :=
    match lbb, ubb with
    | Unbounded, Unbounded => Some 0
    | Unbounded, StrictBound ub => Some (ub + - (1))
    | Unbounded, InclusiveBound ub => Some ub
    | StrictBound lb, Unbounded => Some (lb + 1)
    | StrictBound lb, StrictBound ub => if ub <= lb then None else Some ((lb + ub) / (1 + 1))
    | StrictBound lb, InclusiveBound ub => if ub <= lb then None else Some ub
    | InclusiveBound lb, Unbounded => Some lb
    | InclusiveBound lb, StrictBound ub => if ub <= lb then None else Some lb 
    | InclusiveBound lb, InclusiveBound ub => if lb <= ub then Some lb else None
end.

Lemma satisfy_bounds_none_preservation:
    forall head tail ub,
        satisfy_bounds (compute_lb tail) ub = None ->
        satisfy_bounds (compute_lb (head :: tail)) ub = None.
Proof.
    intros head tail v2 H.
    unfold satisfy_bounds in H.
    unfold satisfy_bounds.
    destruct (compute_lb tail) eqn:Htail.
    * destruct v2 eqn:Hv2; discriminate.
    * destruct v2 eqn:Hv2; try discriminate. 
      - destruct (value0 <= value) eqn:Hcmp; try discriminate.
        pose proof (compute_lb_monotone head tail) as Hmonotone.
        rewrite Htail in Hmonotone.
        remember (compute_lb (head :: tail)) as lb2.
        destruct lb2.
        * unfold compute_lb in Heqlb2; fold (compute_lb tail) in Heqlb2.
          rewrite Htail in Heqlb2.
          destruct head. 
          - destruct (value <= _); discriminate.
          - destruct (- _ <= value); discriminate.
        * remember (value0 <= value1) as b eqn:Hb; destruct b.
          - reflexivity.
          - apply ax_real_leq_true in Hcmp.
            apply ax_real_leq_true in Hmonotone.
            symmetry in Hb; apply ax_real_leq_false in Hb.
            lra.
        * remember (value0 <= value1) as b eqn:Hb; destruct b.
          - reflexivity.
          - apply ax_real_leq_true in Hcmp.
            apply ax_real_leq_false in Hmonotone.
            symmetry in Hb; apply ax_real_leq_false in Hb.
            lra.
      - destruct (value0 <= value) eqn:Hcmp; try discriminate.
        pose proof (compute_lb_monotone head tail) as Hmonotone.
        rewrite Htail in Hmonotone.
        remember (compute_lb (head :: tail)) as lb2.
        destruct lb2.
        * unfold compute_lb in Heqlb2; fold (compute_lb tail) in Heqlb2.
          rewrite Htail in Heqlb2.
          destruct head. 
          - destruct (value <= _); discriminate.
          - destruct (- _ <= value); discriminate.
        * remember (value0 <= value1) as b eqn:Hb; destruct b.
          - reflexivity.
          - apply ax_real_leq_true in Hcmp.
            apply ax_real_leq_true in Hmonotone.
            symmetry in Hb; apply ax_real_leq_false in Hb.
            lra.
        * remember (value1 <= value0) as b eqn:Hb; destruct b.
          - apply ax_real_leq_true in Hcmp.
            apply ax_real_leq_false in Hmonotone.
            symmetry in Hb; apply ax_real_leq_true in Hb.
            lra.
          - reflexivity.
    * destruct v2 eqn:Hv2; try discriminate. 
      - destruct (value0 <= value) eqn:Hcmp; try discriminate.
        pose proof (compute_lb_monotone head tail) as Hmonotone.
        rewrite Htail in Hmonotone.
        remember (compute_lb (head :: tail)) as lb2.
        destruct lb2.
        * unfold compute_lb in Heqlb2; fold (compute_lb tail) in Heqlb2.
          rewrite Htail in Heqlb2.
          destruct head. 
          - destruct (value <= _); discriminate.
          - destruct (value <= - _); discriminate.
        * remember (value0 <= value1) as b eqn:Hb; destruct b.
          - reflexivity.
          - apply ax_real_leq_true in Hcmp.
            apply ax_real_leq_true in Hmonotone.
            symmetry in Hb; apply ax_real_leq_false in Hb.
            lra.
        * remember (value0 <= value1) as b eqn:Hb; destruct b.
          - reflexivity.
          - apply ax_real_leq_true in Hcmp.
            apply ax_real_leq_true in Hmonotone.
            symmetry in Hb; apply ax_real_leq_false in Hb.
            lra.
      - destruct (value <= value0) eqn:Hcmp; try discriminate.
        pose proof (compute_lb_monotone head tail) as Hmonotone.
        rewrite Htail in Hmonotone.
        remember (compute_lb (head :: tail)) as lb2.
        destruct lb2.
        * unfold compute_lb in Heqlb2; fold (compute_lb tail) in Heqlb2.
          rewrite Htail in Heqlb2.
          destruct head. 
          - destruct (value <= - _); discriminate.
          - destruct (value <= - _); discriminate.
        * remember (value0 <= value1) as b eqn:Hb; destruct b.
          - reflexivity.
          - apply ax_real_leq_false in Hcmp.
            apply ax_real_leq_true in Hmonotone.
            symmetry in Hb; apply ax_real_leq_false in Hb.
            lra.
        * remember (value1 <= value0) as b eqn:Hb; destruct b.
          - apply ax_real_leq_false in Hcmp.
            apply ax_real_leq_true in Hmonotone.
            symmetry in Hb; apply ax_real_leq_true in Hb.
            lra.
          - reflexivity.
Qed.

Definition trivial_extract (sys: LinearSystem 1): option (T RSOPM) :=
    let (p, gt0) := partition_inequalities sys in
    let (lt0, eq0) := p in
    match trivial_consistency (system_rank_change eq0 0%nat) with
    | true => satisfy_bounds (compute_lb lt0) (compute_ub gt0)
    | false => None
    end.

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
  * unfold trivial_extract in Hextract.
    destruct (partition_inequalities sys) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
    intros sol Hsol.
    destruct (trivial_consistency (system_rank_change eq0_sys 0)) eqn:Htriv_cons; try discriminate.
    apply (partition_inequalities_solutions 1 _ lt0_sys eq0_sys gt0_sys). 
    - symmetry; apply Hpart_sys.
    - apply (compute_lb_finds_solution sys _ lt0_sys eq0_sys gt0_sys).
      * symmetry; apply Hpart_sys.
      * unfold satisfy_bounds in Hextract.
        destruct (compute_lb lt0_sys) eqn:Hlb; destruct (compute_ub gt0_sys) eqn:Hub; try easy.
        - injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply ax_real_leq_false; RSOPM_realize; lra.
        - destruct (value0 <= value) eqn:Hcmp; try discriminate.
          injection Hextract; intro Hinject.
          rewrite Hsol, <- Hinject.
          apply ax_real_leq_false.
          apply ax_real_leq_false in Hcmp.
          pose proof (Rlt_half_plus (INJ_RSOPM _ value) (INJ_RSOPM _ value0) Hcmp) as Hhalf.
          rewrite ax_real_div; RSOPM_realize.
          apply Hhalf.  
        - destruct (value0 <= value) eqn:Hcmp; try discriminate.
          injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply Hcmp.
        - injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply ax_real_leq_true; RSOPM_realize; lra.
        - destruct (value0 <= value) eqn:Hcmp; try discriminate.
          injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply ax_real_leq_true; RSOPM_realize; lra.
        - destruct (value <= value0) eqn:Hcmp; try discriminate.
          injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply ax_real_leq_true; RSOPM_realize; lra.
    - apply (trivial_consistency_partition_solution 
                    sys lt0_sys eq0_sys gt0_sys sol).
      * symmetry; apply Hpart_sys.
      * apply Htriv_cons.
    - apply (compute_ub_finds_solution sys _ lt0_sys eq0_sys gt0_sys).
      * symmetry; apply Hpart_sys.
      * unfold satisfy_bounds in Hextract.
        destruct (compute_ub gt0_sys) eqn:Hlb; destruct (compute_lb lt0_sys) eqn:Hub; try easy.
        - injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply ax_real_leq_false; RSOPM_realize; lra.
        - destruct (value <= value0) eqn:Hcmp; try discriminate.
          injection Hextract; intro Hinject.
          rewrite Hsol, <- Hinject.
          apply ax_real_leq_false.
          apply ax_real_leq_false in Hcmp.
          pose proof (Rlt_half_plus (INJ_RSOPM _ value0) (INJ_RSOPM _ value) Hcmp) as Hhalf.
          rewrite ax_real_div; RSOPM_realize.
          apply Hhalf.  
        - destruct (value <= value0) eqn:Hcmp; try discriminate.
          injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply Hcmp.
        - injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply ax_real_leq_true; RSOPM_realize; lra.
        - destruct (value <= value0) eqn:Hcmp; try discriminate.
          injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply ax_real_leq_true; RSOPM_realize; lra.
        - destruct (value0 <= value) eqn:Hcmp; try discriminate.
          injection Hextract; intro Hinject.
          rewrite <- Hinject in Hsol.
          rewrite Hsol.
          apply Hcmp.
  * apply all_not_not_ex.
    intro sol.
    unfold trivial_extract in Hextract.
    remember (partition_inequalities (sys)) as part eqn:Hpart.
    destruct part as ((lt0, eq0), gt0).
    apply (partition_inequalities_solutions_contraposition sys lt0 eq0 gt0 _ Hpart).
    destruct trivial_consistency eqn:Htriv_cons.
    * unfold satisfy_bounds in Hextract.
      pose proof (compute_ub_sound sys sol lt0 eq0 gt0 Hpart) as Hub_correct.
      pose proof (compute_lb_sound sys sol lt0 eq0 gt0 Hpart) as Hlb_correct.     
      destruct (compute_lb lt0) eqn:Hlb; destruct (compute_ub gt0) eqn:Hub; try easy.
      - destruct (value0 <= value) eqn:Hcmp; try discriminate.
        destruct (sol 1%nat <= value) eqn:Hsol.
        * left; apply Hlb_correct; reflexivity.
        * destruct (value0 <= sol 1%nat) eqn:Hsol2.
          - right; right; apply Hub_correct; reflexivity.
          - apply ax_real_leq_false in Hsol2.
            apply ax_real_leq_false in Hsol.
            apply ax_real_leq_true in Hcmp.
            lra.
      - destruct (value0 <= value) eqn:Hcmp; try discriminate.
        destruct (sol 1%nat <= value) eqn:Hsol.
        * left; apply Hlb_correct; reflexivity.
        * right; right; apply Hub_correct.
          apply ax_real_leq_false.
          apply ax_real_leq_false in Hsol.
          apply ax_real_leq_true in Hcmp.
          lra.
      - destruct (value0 <= value) eqn:Hcmp; try discriminate.
        destruct (value0 <= sol 1%nat) eqn:Hsol.
        * right; right; apply Hub_correct; reflexivity.
        * destruct (value0 <= sol 1%nat) eqn:Hsol2; try discriminate.
          left; apply Hlb_correct.
          apply ax_real_leq_false.
          apply ax_real_leq_false in Hsol2.
          apply ax_real_leq_true in Hcmp.
          lra.
      - destruct (value <= value0) eqn:Hcmp; try discriminate.
        destruct (value <= sol 1%nat) eqn:Hsol.
        * right; right; apply Hub_correct.
          apply ax_real_leq_false.
          apply ax_real_leq_false in Hcmp.
          apply ax_real_leq_true in Hsol.
          lra.
        * left; apply Hlb_correct; reflexivity. 
    * right; left.
      rewrite (trivial_remove_var_eq0_sol 0 sys lt0 eq0 gt0 Hpart).
      pose proof trivial_consistency_correct as Hcons.
      specialize (Hcons (system_rank_change eq0 0)).
      rewrite Htriv_cons in Hcons.
      assert (forall n0 : LinearSystemSolution 0, ~ is_linear_system_solution (n:=0) (system_rank_change eq0 0) n0).
      apply not_ex_all_not.
      exact Hcons.
      apply H.
Qed.
 
Definition compose_inequalities {n: nat} (sys1 sys2: LinearSystem (S n)): LinearSystem n :=
    map
    (fun prod_el: LinearInequality (S n) * LinearInequality (S n) =>
         let (ineq1, ineq2) := prod_el in ineq_compose ineq1 ineq2)
    (list_prod sys1 sys2).

Lemma compose_inequalities_correct:
  forall n (lt0 gt0: LinearSystem (S n)) sol,
    (forall ineq, In ineq lt0 -> (0 <= (ineq_coeffs ineq) (S n)) = false) ->
    (forall ineq, In ineq gt0 -> ((ineq_coeffs ineq) (S n) <= 0) = false) ->
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
    (compose_inequalities lt0 gt0) ++ (system_rank_change eq0 n).

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

Definition ineq_insert_solution {n}
    (ineq: LinearInequality (S n))
    (sol: LinearSystemSolution n)
    : LinearInequality 1 
    :=
    match ineq with
    | Strict coeffs => 
        Strict 1 (fun i => if i =? 1 then coeffs (S n) else interpret_inequality_helper n coeffs sol)
    | Inclusive coeffs => 
        Inclusive 1 (fun i => if i =? 1 then coeffs (S n) else interpret_inequality_helper n coeffs sol)
    end.

Definition insert_solution {n: nat} 
    (sys: LinearSystem (S n))
    (sol: LinearSystemSolution n)
    : LinearSystem 1 :=
    map (fun ineq => ineq_insert_solution ineq sol) sys.

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
  forall n n2 (a: nat -> T RSOPM) s (sol: LinearSystemSolution n2),
    (n2 > n)%nat ->
    interpret_inequality_helper n a (prepend_to_solution (n:=n2) s sol) = 
    interpret_inequality_helper n a (prepend_to_solution (n:=S n2) s sol).
Proof.
  intros n.
  induction n; intros n2 a s sol Hn2.
  * unfold interpret_inequality_helper. reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper n).
    rewrite (prepend_to_solution_not_last n2 n2 (S n)); last lia.
    rewrite (prepend_to_solution_not_last (S n2) n2 (S n)); last lia.
    rewrite (IHn n2 a s sol).
    reflexivity. lia.
Qed.

Lemma prepend_interpret:
  forall n (a: nat -> T RSOPM) s (sol: LinearSystemSolution (S n)),
    interpret_inequality_helper n a (prepend_to_solution s sol) = 
    interpret_inequality_helper n a sol.
Proof.
  intros n a s sol.
  induction n.
  * unfold interpret_inequality_helper; reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper n).
    rewrite <- (IHn sol).
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
    unfold interpret_inequality, ineq_insert_solution in Ha_s.
    unfold interpret_inequality.
    destruct n.
    - unfold interpret_inequality_helper in Ha_s.
      unfold interpret_inequality_helper.
      unfold prepend_to_solution.
      unfold Nat.eqb.
      destruct a; simpl in Ha_s; apply Ha_s.
    - unfold interpret_inequality_helper. fold (interpret_inequality_helper n).
      unfold interpret_inequality_helper in Ha_s; fold (interpret_inequality_helper n) in Ha_s.
      unfold prepend_to_solution at 1 4.
      rewrite Nat.eqb_refl.
      rewrite (prepend_to_solution_not_last (S n) (S n) (S n)); last lia.
      destruct a; simpl in Ha_s; rewrite (prepend_interpret n coeffs s sol); apply Ha_s.
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
    destruct a; apply Ha.
  * apply (IHsys Hrest).
Qed.
  
Lemma insert_solution_single:
  forall n (ineq: LinearInequality (S n)) sol,
    insert_solution [ineq] sol = [ineq_insert_solution ineq sol].
Proof.
  intros n ineq sol.
  unfold insert_solution, map, ineq_insert_solution.
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
      pose proof (partition_cons_eq0 _ (ineq_insert_solution a sol) (insert_solution sys sol)) as Hmain.
      rewrite <- IHsys in Hmain.
      apply Hmain; split.
      * unfold ineq_insert_solution; destruct a; apply Ha_ge_0.
      * unfold ineq_insert_solution; destruct a; apply H0_ge_a.  
    - rewrite Hsys_lt0, Hsys_eq0, Hsys_gt0.
      rewrite insert_solution_cons.
      rewrite insert_solution_single; unfold app.
      pose proof (partition_cons_lt0 _ (ineq_insert_solution a sol) (insert_solution sys sol)) as Hmain.
      rewrite <- IHsys in Hmain.
      apply Hmain; split.
      * unfold ineq_insert_solution; destruct a; apply Ha_ge_0.
      * unfold ineq_insert_solution; destruct a; apply H0_ge_a.  
    - rewrite Hsys_lt0, Hsys_eq0, Hsys_gt0.
      rewrite insert_solution_cons.
      rewrite insert_solution_single; unfold app.
      pose proof (partition_cons_gt0 _ (ineq_insert_solution a sol) (insert_solution sys sol)) as Hmain.
      rewrite <- IHsys in Hmain.
      apply Hmain; split.
      * unfold ineq_insert_solution; destruct a; apply Ha_ge_0.
      * unfold ineq_insert_solution; destruct a; apply H0_ge_a. 
Qed.

Lemma trivial_consistency_insert_solution_eq0:
  forall n (sys: LinearSystem (S (S n))) sol sys_lt0 sys_eq0 sys_gt0 sys1_lt0 sys1_eq0 sys1_gt0,
    (sys_lt0, sys_eq0, sys_gt0) = partition_inequalities sys ->
    is_linear_system_solution (system_rank_change sys_eq0 (S n)) sol ->
    (sys1_lt0, sys1_eq0, sys1_gt0) = partition_inequalities (insert_solution sys sol) ->
    trivial_consistency (system_rank_change sys1_eq0 0) = true.
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
  rewrite system_rank_change_cons.
  unfold trivial_consistency; fold (trivial_consistency).
  rewrite system_rank_change_cons in Hsol.
  rewrite <- is_linear_system_solution_cons in Hsol.
  destruct Hsol as [Ha Hsol].
  destruct a; unfold ineq_rank_change, ineq_insert_solution.
  * apply andb_true_intro; split. 
    - unfold is_linear_system_solution in Ha.
      unfold interpret_inequalities in Ha.
      unfold interpret_inequality in Ha.
      unfold ineq_rank_change, ineq_insert_solution in Ha.
      rewrite negb_true_iff.
      apply Ha.   
    - apply IHsys_eq0.
      apply Hsol. 
  * apply andb_true_intro; split. 
    - unfold is_linear_system_solution in Ha.
      unfold interpret_inequalities in Ha.
      unfold interpret_inequality in Ha.
      unfold ineq_rank_change, ineq_insert_solution in Ha; simpl.
      apply Ha.
    - apply IHsys_eq0.
      apply Hsol. 
Qed.

Lemma compute_lb_exists_strict:
  forall n (sys: LinearSystem (S (S n))) sol lb,
    StrictBound lb = compute_lb (insert_solution sys sol) ->
    exists coeffs, 
      In (Strict _ coeffs) sys /\ 
      lb = - (ineq_coeffs (ineq_insert_solution (Strict _ coeffs) sol) 0%nat / 
                ineq_coeffs (ineq_insert_solution (Strict _ coeffs) sol) 1%nat).
Proof.
  intros n sys.
  induction sys; intros sol lb Hlb.
  * unfold insert_solution, compute_lb, map in Hlb.
    discriminate.
  * rewrite insert_solution_cons in Hlb.
    rewrite insert_solution_single in Hlb.
    unfold app in Hlb.
    unfold compute_lb in Hlb; fold (compute_lb (insert_solution sys sol)) in Hlb.
    destruct a eqn:Ha; destruct (compute_lb (insert_solution sys sol)) eqn:Hlbval; unfold ineq_insert_solution in Hlb.
    * exists coeffs; split.
      - apply in_eq.
      - injection Hlb; intros Hlb_def.
        rewrite Hlb_def.
        unfold ineq_coeffs, ineq_insert_solution; simpl.
        reflexivity.
    * unfold ineq_coeffs in Hlb; simpl in Hlb.
      destruct (value <= _) eqn:Hval.
      - exists coeffs; split.
        * apply in_eq.
        * injection Hlb; intros Hlb_def.
          rewrite Hlb_def.
          unfold ineq_coeffs, ineq_insert_solution; simpl.
          reflexivity.
      - specialize (IHsys sol lb).
        rewrite <- Hlb in Hlbval.
        symmetry in Hlbval.
        specialize (IHsys Hlbval).
        destruct IHsys as [coeff_past Hpast].
        exists coeff_past; split.
        * apply in_cons; apply Hpast.
        * apply Hpast.
    * unfold ineq_coeffs in Hlb; simpl in Hlb.
      destruct (value <= _) eqn:Hval.
      - exists coeffs; split.
        * apply in_eq.
        * injection Hlb; intros Hlb_def.
          rewrite Hlb_def.
          unfold ineq_coeffs, ineq_insert_solution; simpl.
          reflexivity.
      - specialize (IHsys sol lb).
        rewrite <- Hlb in Hlbval.
        symmetry in Hlbval.
        specialize (IHsys Hlbval).
        destruct IHsys as [coeff_past Hpast].
        exists coeff_past; split.
        * apply in_cons; apply Hpast.
        * apply Hpast.
    * discriminate.
    * unfold ineq_coeffs in Hlb; simpl in Hlb.
      destruct (_ <= value) eqn:Hval.
      - specialize (IHsys sol lb).
        rewrite <- Hlb in Hlbval.
        symmetry in Hlbval.
        specialize (IHsys Hlbval).
        destruct IHsys as [coeff_past Hpast].
        exists coeff_past; split.
        * apply in_cons; apply Hpast.
        * apply Hpast.
      - discriminate.
    * unfold ineq_coeffs in Hlb; simpl in Hlb.
      destruct (value <= _) eqn:Hval; discriminate.    
Qed.

Lemma compute_lb_exists_inclusive:
  forall n (sys: LinearSystem (S (S n))) sol lb,
    InclusiveBound lb = compute_lb (insert_solution sys sol) ->
    exists coeffs, 
      In (Inclusive _ coeffs) sys /\ 
      lb = - (ineq_coeffs (ineq_insert_solution (Inclusive _ coeffs) sol) 0%nat / 
              ineq_coeffs (ineq_insert_solution (Inclusive _ coeffs) sol) 1%nat).
Proof.
  intros n sys.
  induction sys; intros sol lb Hlb.
  * unfold insert_solution, compute_lb, map in Hlb.
    discriminate.
  * rewrite insert_solution_cons in Hlb.
    rewrite insert_solution_single in Hlb.
    unfold app in Hlb.
    unfold compute_lb in Hlb; fold (compute_lb (insert_solution sys sol)) in Hlb.
    destruct a eqn:Ha; destruct (compute_lb (insert_solution sys sol)) eqn:Hlbval; unfold ineq_insert_solution in Hlb.
      * discriminate. 
      * unfold ineq_coeffs in Hlb; simpl in Hlb.
        destruct (value <= _) eqn:Hval; discriminate.
      * unfold ineq_coeffs in Hlb; simpl in Hlb.
        destruct (value <= _) eqn:Hval; first discriminate.
        specialize (IHsys sol lb).
        rewrite <- Hlb in Hlbval.
        symmetry in Hlbval.
        specialize (IHsys Hlbval).
        destruct IHsys as [coeff_past Hpast].
        exists coeff_past; split.
        - apply in_cons; apply Hpast.
        - apply Hpast.
      * unfold ineq_coeffs in Hlb; simpl in Hlb.  
        exists coeffs; split.
        - apply in_eq.
        - injection Hlb; intros Hlb_def.
          rewrite Hlb_def.
          unfold ineq_coeffs, ineq_insert_solution; simpl.
          reflexivity.
      * unfold ineq_coeffs in Hlb; simpl in Hlb.
        destruct (_ <= value) eqn:Hval; first discriminate.
        exists coeffs; split.
        - apply in_eq.
        - injection Hlb; intros Hlb_def.
          rewrite Hlb_def.
          unfold ineq_coeffs, ineq_insert_solution; simpl.
          reflexivity.
      * unfold ineq_coeffs in Hlb; simpl in Hlb.
        destruct (value <= _) eqn:Hval.
        - exists coeffs; split.
          * apply in_eq.
          * injection Hlb; intros Hlb_def.
            rewrite Hlb_def.
            unfold ineq_coeffs, ineq_insert_solution; simpl.
            reflexivity.
        - specialize (IHsys sol lb).
          rewrite <- Hlb in Hlbval.
          symmetry in Hlbval.
          specialize (IHsys Hlbval).
          destruct IHsys as [coeff_past Hpast].
          exists coeff_past; split.
          - apply in_cons; apply Hpast.
          - apply Hpast.
Qed.

Lemma compute_ub_exists_strict:
  forall n (sys: LinearSystem (S (S n))) sol ub,
    StrictBound ub = compute_ub (insert_solution sys sol) ->
    exists coeffs, 
      In (Strict _ coeffs) sys /\ 
      ub = - (ineq_coeffs (ineq_insert_solution (Strict _ coeffs) sol) 0%nat / 
                ineq_coeffs (ineq_insert_solution (Strict _ coeffs) sol) 1%nat).
Proof.
  intros n sys.
  induction sys; intros sol ub Hub.
  * unfold insert_solution, compute_lb, map in Hub; discriminate.
  * rewrite insert_solution_cons in Hub.
    rewrite insert_solution_single in Hub.
    unfold app in Hub.
    unfold compute_ub in Hub; fold (compute_ub (insert_solution sys sol)) in Hub.
    destruct a eqn:Ha; destruct (compute_ub (insert_solution sys sol)) eqn:Hubval; unfold ineq_insert_solution in Hub.
    * exists coeffs; split.
      - apply in_eq.
      - injection Hub; intros Hub_def.
        rewrite Hub_def.
        unfold ineq_coeffs, ineq_insert_solution; simpl.
        reflexivity.
    * unfold ineq_coeffs in Hub; simpl in Hub.
      destruct (value <= _) eqn:Hval.
      - specialize (IHsys sol ub).
        rewrite <- Hub in Hubval.
        symmetry in Hubval.
        specialize (IHsys Hubval).
        destruct IHsys as [coeffs_past Hpast].
        exists coeffs_past; split.
        * apply in_cons; apply Hpast.
        * apply Hpast.
      - exists coeffs; split.
        * apply in_eq.
        * injection Hub; intros Hub_def.
          rewrite Hub_def.
          unfold ineq_coeffs, ineq_insert_solution; simpl.
          reflexivity.
    * unfold ineq_coeffs in Hub; simpl in Hub.
      destruct (_ <= value) eqn:Hval.
      - exists coeffs; split.
        * apply in_eq.
        * injection Hub; intros Hub_def.
          rewrite Hub_def.
          unfold ineq_coeffs, ineq_insert_solution; simpl.
          reflexivity.
      - discriminate.
    * discriminate.
    * unfold ineq_coeffs in Hub; simpl in Hub.
      destruct (value <= _) eqn:Hval.
      - specialize (IHsys sol ub).
        rewrite <- Hub in Hubval.
        symmetry in Hubval.
        specialize (IHsys Hubval).
        destruct IHsys as [coeffs_past Hpast].
        exists coeffs_past; split.
        * apply in_cons; apply Hpast.
        * apply Hpast.
      - discriminate.
    * unfold ineq_coeffs in Hub; simpl in Hub.
      destruct (value <= _) eqn:Hval; discriminate.
Qed.

Lemma compute_ub_exists_inclusive:
  forall n (sys: LinearSystem (S (S n))) sol ub,
    InclusiveBound ub = compute_ub (insert_solution sys sol) ->
    exists coeffs, 
      In (Inclusive _ coeffs) sys /\ 
      ub = - (ineq_coeffs (ineq_insert_solution (Inclusive _ coeffs) sol) 0%nat / 
              ineq_coeffs (ineq_insert_solution (Inclusive _ coeffs) sol) 1%nat).
Proof.
  intros n sys.
  induction sys; intros sol ub Hub.
  * unfold insert_solution, compute_lb, map in Hub; discriminate.
  * rewrite insert_solution_cons in Hub.
    rewrite insert_solution_single in Hub.
    unfold app in Hub.
    unfold compute_ub in Hub; fold (compute_ub (insert_solution sys sol)) in Hub.
    destruct a eqn:Ha; destruct (compute_ub (insert_solution sys sol)) eqn:Hubval; unfold ineq_insert_solution in Hub.
    * discriminate. 
    * unfold ineq_coeffs in Hub; simpl in Hub.
      destruct (value <= _) eqn:Hval; discriminate.
    * unfold ineq_coeffs in Hub; simpl in Hub.
      destruct (_ <= value) eqn:Hval; first discriminate.
      specialize (IHsys sol ub).
      rewrite <- Hub in Hubval.
      symmetry in Hubval.
      specialize (IHsys Hubval).
      destruct IHsys as [coeffs_past Hpast].
      exists coeffs_past; split.
      - apply in_cons; apply Hpast.
      - apply Hpast.
    * unfold ineq_coeffs in Hub; simpl in Hub.  
      exists coeffs; split.
      - apply in_eq.
      - injection Hub; intros Hub_def.
        rewrite Hub_def.
        unfold ineq_coeffs, ineq_insert_solution; simpl.
        reflexivity.
    * unfold ineq_coeffs in Hub; simpl in Hub.
      destruct (value <= _) eqn:Hval; first discriminate.
      exists coeffs; split.
      - apply in_eq.
      - injection Hub; intros Hub_def.
        rewrite Hub_def.
        unfold ineq_coeffs, ineq_insert_solution; simpl.
        reflexivity.
    * unfold ineq_coeffs in Hub; simpl in Hub.
      destruct (value <= _) eqn:Hval.
      - specialize (IHsys sol ub).
        rewrite <- Hub in Hubval.
        symmetry in Hubval.
        specialize (IHsys Hubval).
        destruct IHsys as [coeffs_past Hpast].
        exists coeffs_past; split.
        - apply in_cons; apply Hpast.
        - apply Hpast.
      - exists coeffs; split.
        * apply in_eq.
        * injection Hub; intros Hub_def.
          rewrite Hub_def.
          unfold ineq_coeffs, ineq_insert_solution; simpl.
          reflexivity.
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
    - interpret_inequality_helper n (fun i => (e1 i) / e2) sol =
    interpret_inequality_helper n (fun i => (e1 i) / - e2) sol.
Proof.
  intros n e1 e2 sol.
  induction n.
  * unfold interpret_inequality_helper.
    RSOPM_realize_eq; repeat rewrite ax_real_div; RSOPM_realize.
    rewrite Ropp_div_distr_r; reflexivity.
  * unfold interpret_inequality_helper; fold (interpret_inequality_helper n).
    specialize (IHn sol).
    rewrite <- IHn.
    RSOPM_realize_eq; repeat rewrite ax_real_div; RSOPM_realize.
    rewrite Ropp_div_distr_r.
    rewrite Ropp_mult_distr_l_reverse.
    rewrite <- Ropp_plus_distr.
    reflexivity.
Qed.

Lemma RSOPMD_leq_shift:
  forall (r1: T RSOPM) r2, ((0 <= r1 + r2) = false -> (- r2 <= r1) = false)%RS.
Proof.
    intros r1 r2.
    do 2 rewrite ax_real_leq_false.
    RSOPM_realize.
    lra.
Qed.

Lemma RSOPMD_leq_shift2:
  forall (r1: T RSOPM) r2, ((- r1 + r2 <= 0) = true -> (- r1 <= - r2) = true)%RS.
Proof.
    intros r1 r2.
    do 2 rewrite ax_real_leq_true.
    RSOPM_realize.
    lra.
Qed.

Lemma interpret_inequality_helper_fold:
  forall sol n (coeffs: nat -> T RSOPM),
    coeffs (S n) * sol (S n) + interpret_inequality_helper n coeffs sol = 
    interpret_inequality_helper (S n) coeffs sol.
Proof.
  intros; unfold interpret_inequality_helper; fold (interpret_inequality_helper n).
  reflexivity.
Qed.

Lemma reconstruction_bounds_strict_strict:
  forall n (sys: LinearSystem (S (S n))) sol sys_lt0 sys_eq0 sys_gt0 lb ub,
    (sys_lt0, sys_eq0, sys_gt0) = partition_inequalities sys ->
    is_linear_system_solution (compose_inequalities sys_lt0 sys_gt0) sol ->
    StrictBound lb = compute_lb (insert_solution sys_lt0 sol) ->
    StrictBound ub = compute_ub (insert_solution sys_gt0 sol) ->
    ub <= lb = false.
Proof.
  intros n sys sol sys_lt0 sys_eq0 sys_gt0 lb ub Hpart Hcompose Hlb Hub.
  pose proof (compute_lb_exists_strict _ sys_lt0 sol lb Hlb) as Hlb_coeffs.
  pose proof (compute_ub_exists_strict _ sys_gt0 sol ub Hub) as Hub_coeffs.
  destruct Hlb_coeffs as [lb_coeffs [Hlbin Hlb_coeffs]].
  destruct Hub_coeffs as [ub_coeffs [Hubin Hub_coeffs]].
  rewrite Hlb_coeffs, Hub_coeffs.
  pose proof (compose_inequalities_reduce _ _ _ _ Hcompose (Strict _ lb_coeffs) 
                                          (Strict _ ub_coeffs) Hlbin Hubin) as Hineqs.
  unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
      compose_inequalities, list_prod, map, app, ineq_compose in Hineqs.
  unfold ineq_coeffs, ineq_insert_solution; simpl.
  rewrite RSOPMD_leq_shift; first reflexivity.
  do 2 rewrite interpret_inequality_helper_fold.
  do 2 rewrite interpret_inequality_helper_div.
  rewrite interpret_inequality_helper_reconstruction.
  rewrite interpret_inequality_helper_plus.
  unfold ineq_rank_change, ineq_plus, ineq_constdiv, ineq_coeffs in Hineqs.
  apply Hineqs.
Qed.

Lemma reconstruction_bounds_strict_inclusive:
  forall n (sys: LinearSystem (S (S n))) sol sys_lt0 sys_eq0 sys_gt0 lb ub,
    (sys_lt0, sys_eq0, sys_gt0) = partition_inequalities sys ->
    is_linear_system_solution (compose_inequalities sys_lt0 sys_gt0) sol ->
    StrictBound lb = compute_lb (insert_solution sys_lt0 sol) ->
    InclusiveBound ub = compute_ub (insert_solution sys_gt0 sol) ->
    ub <= lb = false.
Proof.
  intros n sys sol sys_lt0 sys_eq0 sys_gt0 lb ub Hpart Hcompose Hlb Hub.
  pose proof (compute_lb_exists_strict _ sys_lt0 sol lb Hlb) as Hlb_coeffs.
  pose proof (compute_ub_exists_inclusive _ sys_gt0 sol ub Hub) as Hub_coeffs.
  destruct Hlb_coeffs as [lb_coeffs [Hlbin Hlb_coeffs]].
  destruct Hub_coeffs as [ub_coeffs [Hubin Hub_coeffs]].
  rewrite Hlb_coeffs, Hub_coeffs.
  pose proof (compose_inequalities_reduce _ _ _ _ Hcompose (Strict _ lb_coeffs) 
                                          (Inclusive _ ub_coeffs) Hlbin Hubin) as Hineqs.
  unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
      compose_inequalities, list_prod, map, app, ineq_compose in Hineqs.
  unfold ineq_coeffs, ineq_insert_solution; simpl.
  rewrite RSOPMD_leq_shift; first reflexivity.
  do 2 rewrite interpret_inequality_helper_fold.
  do 2 rewrite interpret_inequality_helper_div.
  rewrite interpret_inequality_helper_reconstruction.
  rewrite interpret_inequality_helper_plus.
  unfold ineq_rank_change, ineq_plus, ineq_constdiv, ineq_coeffs in Hineqs.
  apply Hineqs.
Qed.

Lemma reconstruction_bounds_inclusive_strict:
  forall n (sys: LinearSystem (S (S n))) sol sys_lt0 sys_eq0 sys_gt0 lb ub,
    (sys_lt0, sys_eq0, sys_gt0) = partition_inequalities sys ->
    is_linear_system_solution (compose_inequalities sys_lt0 sys_gt0) sol ->
    InclusiveBound lb = compute_lb (insert_solution sys_lt0 sol) ->
    StrictBound ub = compute_ub (insert_solution sys_gt0 sol) ->
    ub <= lb = false.
Proof.
  intros n sys sol sys_lt0 sys_eq0 sys_gt0 lb ub Hpart Hcompose Hlb Hub.
  pose proof (compute_lb_exists_inclusive _ sys_lt0 sol lb Hlb) as Hlb_coeffs.
  pose proof (compute_ub_exists_strict _ sys_gt0 sol ub Hub) as Hub_coeffs.
  destruct Hlb_coeffs as [lb_coeffs [Hlbin Hlb_coeffs]].
  destruct Hub_coeffs as [ub_coeffs [Hubin Hub_coeffs]].
  rewrite Hlb_coeffs, Hub_coeffs.
  pose proof (compose_inequalities_reduce _ _ _ _ Hcompose (Inclusive _ lb_coeffs) 
                                          (Strict _ ub_coeffs) Hlbin Hubin) as Hineqs.
  unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
      compose_inequalities, list_prod, map, app, ineq_compose in Hineqs.
  unfold ineq_coeffs, ineq_insert_solution; simpl.
  rewrite RSOPMD_leq_shift; first reflexivity.
  do 2 rewrite interpret_inequality_helper_fold.
  do 2 rewrite interpret_inequality_helper_div.
  rewrite interpret_inequality_helper_reconstruction.
  rewrite interpret_inequality_helper_plus.
  unfold ineq_rank_change, ineq_plus, ineq_constdiv, ineq_coeffs in Hineqs.
  apply Hineqs.
Qed.

Lemma reconstruction_bounds_inclusive_inclusive:
  forall n (sys: LinearSystem (S (S n))) sol sys_lt0 sys_eq0 sys_gt0 lb ub,
    (sys_lt0, sys_eq0, sys_gt0) = partition_inequalities sys ->
    is_linear_system_solution (compose_inequalities sys_lt0 sys_gt0) sol ->
    InclusiveBound lb = compute_lb (insert_solution sys_lt0 sol) ->
    InclusiveBound ub = compute_ub (insert_solution sys_gt0 sol) ->
    lb <= ub = true.
Proof.
  intros n sys sol sys_lt0 sys_eq0 sys_gt0 lb ub Hpart Hcompose Hlb Hub.
  pose proof (compute_lb_exists_inclusive _ sys_lt0 sol lb Hlb) as Hlb_coeffs.
  pose proof (compute_ub_exists_inclusive _ sys_gt0 sol ub Hub) as Hub_coeffs.
  destruct Hlb_coeffs as [lb_coeffs [Hlbin Hlb_coeffs]].
  destruct Hub_coeffs as [ub_coeffs [Hubin Hub_coeffs]].
  rewrite Hlb_coeffs, Hub_coeffs.
  pose proof (compose_inequalities_reduce _ _ _ _ Hcompose (Inclusive _ lb_coeffs) 
                                          (Inclusive _ ub_coeffs) Hlbin Hubin) as Hineqs.
  unfold is_linear_system_solution, interpret_inequalities, interpret_inequality,
      compose_inequalities, list_prod, map, app, ineq_compose in Hineqs.
  unfold ineq_coeffs, ineq_insert_solution; simpl.
  rewrite RSOPMD_leq_shift2; first reflexivity.
  do 2 rewrite interpret_inequality_helper_fold.
  do 2 rewrite interpret_inequality_helper_div.
  rewrite interpret_inequality_helper_reconstruction.
  rewrite interpret_inequality_helper_plus.
  unfold ineq_rank_change, ineq_plus, ineq_constdiv, ineq_coeffs in Hineqs.
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
  * rewrite Heqext_res.
    rewrite Heqext_res in H.
    specialize (H (fun _ => 0) eq_refl).
    apply H.
  * rewrite Heqext_res.
    rewrite Heqext_res in H.
    specialize (H (fun _ => value + - (1)) eq_refl).
    apply H.
  * rewrite Heqext_res.
    rewrite Heqext_res in H.
    specialize (H (fun _ => value) eq_refl).
    apply H.
  * rewrite Heqext_res.
    rewrite Heqext_res in H.
    specialize (H (fun _ => value + 1) eq_refl).
    apply H.
  * destruct (value0 <= value) eqn:Hbounds.
    - rewrite (reconstruction_bounds_strict_strict n sys sol sys_lt0 sys_eq0 sys_gt0) in Hbounds; first discriminate.
      * apply Heqsys_p.
      * apply Hcompose.
      * rewrite Hsys1_lt0 in Heqsys1_lbo.
        apply Heqsys1_lbo.
      * rewrite Hsys1_gt0 in Heqsys1_ubo.
        apply Heqsys1_ubo.
    - rewrite Heqext_res.
      rewrite Heqext_res in H.
      specialize (H (fun _ => (value + value0) / (1 + 1)) eq_refl).
      apply H.
  * destruct (value0 <= value) eqn:Hbounds.
    - rewrite (reconstruction_bounds_strict_inclusive n sys sol sys_lt0 sys_eq0 sys_gt0) in Hbounds; first discriminate.
      * apply Heqsys_p.
      * apply Hcompose.
      * rewrite Hsys1_lt0 in Heqsys1_lbo.
        apply Heqsys1_lbo.
      * rewrite Hsys1_gt0 in Heqsys1_ubo.
        apply Heqsys1_ubo.
    - rewrite Heqext_res.
      rewrite Heqext_res in H.
      specialize (H (fun _ => value0) eq_refl).
      apply H.
  * rewrite Heqext_res.
    rewrite Heqext_res in H.
    specialize (H (fun _ => value) eq_refl).
    apply H.  
  * destruct (value0 <= value) eqn:Hbounds.
    - rewrite (reconstruction_bounds_inclusive_strict n sys sol sys_lt0 sys_eq0 sys_gt0) in Hbounds; first discriminate.
      * apply Heqsys_p.
      * apply Hcompose.
      * rewrite Hsys1_lt0 in Heqsys1_lbo.
        apply Heqsys1_lbo.
      * rewrite Hsys1_gt0 in Heqsys1_ubo.
        apply Heqsys1_ubo.
    - rewrite Heqext_res.
      rewrite Heqext_res in H.
      specialize (H (fun _ => value) eq_refl).
      apply H.
  * destruct (value <= value0) eqn:Hbounds.
    - rewrite Heqext_res.
      rewrite Heqext_res in H.
      specialize (H (fun _ => value) eq_refl).
      apply H.
    - rewrite (reconstruction_bounds_inclusive_inclusive n sys sol sys_lt0 sys_eq0 sys_gt0) in Hbounds; first discriminate.
      * apply Heqsys_p.
      * apply Hcompose.
      * rewrite Hsys1_lt0 in Heqsys1_lbo.
        apply Heqsys1_lbo.
      * rewrite Hsys1_gt0 in Heqsys1_ubo.
        apply Heqsys1_ubo.
Qed.

Fixpoint fme_solve {n: nat} (sys: LinearSystem n)
    : option (LinearSystemSolution n) :=
    match n with
    | 0 => if trivial_consistency (system_rank_change sys 0) then Some (fun _ => 0) else None
    | 1 => match trivial_extract (system_rank_change sys 1) with
           | Some s => Some (fun _ => s)
           | None => None
           end
    | S i => 
        match fme_solve (n:=i) (remove_var (system_rank_change sys (S i))) with
        | Some subsol => 
            match trivial_extract (insert_solution (system_rank_change sys (S i)) subsol) with
            | Some s => Some (prepend_to_solution s subsol) 
            | None => None
            end
        | None => None
        end
    end.

Lemma fme_solve_SSn:
    forall n (sys: LinearSystem (S (S n))),
      fme_solve sys = 
        match fme_solve (n:=S n) (remove_var (system_rank_change sys (S (S n)))) with
        | Some subsol => 
            match trivial_extract (insert_solution (system_rank_change sys (S (S n))) subsol) with
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
      rewrite system_rank_change_id.
      pose proof (trivial_consistency_correct sys) as Htrivial.
      destruct (trivial_consistency sys) eqn:Hresult; apply Htrivial.
    * unfold fme_solve.
      rewrite system_rank_change_id.
      destruct (trivial_extract sys) as [s |] eqn:Htrivial.
      - pose proof (trivial_extract_correct sys) as Hcorrect.
        rewrite Htrivial in Hcorrect.
        apply Hcorrect.
        reflexivity.
      - pose proof (trivial_extract_correct sys) as Hcorrect.
        rewrite Htrivial in Hcorrect.
        apply Hcorrect.
    * rewrite fme_solve_SSn.
      rewrite system_rank_change_id.
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