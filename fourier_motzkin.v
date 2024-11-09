From Coq Require Import List Reals Lra.
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

Definition interpret_inequality {n: nat} 
    (ineq: LinearInequality n) 
    (sol: LinearSystemSolution n)
    : Prop :=
    ((interpret_inequality_helper (n:=n) ineq sol <= 0) = true).

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

Lemma partition_inequalities_solutions: 
    forall (sys: LinearSystem 1) lt0 eq0 gt0 sol,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        is_linear_system_solution lt0 sol ->
        is_linear_system_solution eq0 sol ->
        is_linear_system_solution gt0 sol ->
        is_linear_system_solution sys sol.
Proof.
   intros sys. induction sys.
   * unfold is_linear_system_solution, interpret_inequalities; easy.
   * pose proof (partition_inequalities_cons 1 a sys) as Hsplit.
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

Fixpoint RSOPM_list_max (l: list (T RSOPM)): option (T RSOPM) :=
match l with
| nil => None
| head :: tail => 
    match RSOPM_list_max tail with
    | None => Some head
    | Some previous_min => 
        if head <= previous_min then Some previous_min else Some head
    end
end. 

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

Definition compute_lb (lt0_partition: LinearSystem 1): option (T RSOPM) :=
    RSOPM_list_max (map (fun ineq => - (ineq 0%nat / ineq 1%nat)) lt0_partition).

Lemma compute_lb_correct:
  forall sys lt0 eq0 gt0 sol,
      (lt0, eq0, gt0) = partition_inequalities sys ->
      match (compute_lb lt0) with
      | Some lb => lb <= sol 1%nat = true
      | None => True 
      end ->
      is_linear_system_solution lt0 sol.
Proof.
  intros sys lt0 eq0 gt0 sol Hpart H.
  induction sys.
  * unfold partition_inequalities in Hpart.
    unfold partition in Hpart.
    apply pair_equal_spec in Hpart; destruct Hpart as [Hpart1 Hpart2].
    apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
    rewrite Hpart1.
    unfold is_linear_system_solution,interpret_inequalities. easy.
  * pose proof partition_inequalities_cons as Hcons.
    specialize (Hcons 1%nat a sys).
Admitted.

Lemma compute_lb_monotone:
  forall head tail lb1,
      compute_lb tail = Some lb1 ->
      (exists lb2, 
          compute_lb (head :: tail) = Some lb2 /\
          lb1 <= lb2 = true).
Proof.
Admitted.

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

Lemma compute_ub_correct:
    forall sys lt0 eq0 gt0 sol,
        (lt0, eq0, gt0) = partition_inequalities sys ->
        match (compute_ub gt0) with
        | Some ub => sol 1%nat <= ub = true
        | None => True 
        end ->
        is_linear_system_solution gt0 sol.
Admitted.

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

Lemma trivial_extract_correct:
    forall (sys: LinearSystem 1),
        match trivial_extract sys with
        | Some r => (forall sol, 
            sol 1%nat = r -> is_linear_system_solution sys sol)
        | None => ~ (exists sol, is_linear_system_solution sys sol)
        end. 
Proof.
    intro sys.
    destruct (trivial_extract sys) eqn:Hextract; 
    unfold trivial_extract in Hextract;
    destruct (partition_inequalities sys) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
   * intros sol Hsol.
     destruct (trivial_consistency eq0_sys) eqn:Htriv_cons; try discriminate.
     apply (partition_inequalities_solutions _ lt0_sys eq0_sys gt0_sys). 
     - symmetry; apply Hpart_sys.
     - apply (compute_lb_correct sys lt0_sys eq0_sys gt0_sys).
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
     - apply (compute_ub_correct sys lt0_sys eq0_sys gt0_sys).
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
   * (* Requires some more work *)
Admitted.

(* Old proof attempt 
   unfold trivial_extract.
   pose proof (partition_inequalities_cons _ a sys) as Hsplit.
   destruct (partition_inequalities sys) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
   destruct (partition_inequalities (a :: sys))
      as [[lt0_is eq0_is] gt0_is] eqn:Hpart_is.
   destruct Hsplit as [Hsplit|[Hsplit|Hsplit]];
   destruct Hsplit as [Ha_le0 [Ha_ge0 [Hlt0 [Hgt0 Heq0]]]].   




   induction sys.
   * unfold trivial_extract,compute_lb,compute_ub; simpl; easy.
   * unfold trivial_extract.
     unfold trivial_extract in IHsys.
     pose proof (partition_inequalities_cons _ a sys) as Hsplit.
     destruct (partition_inequalities sys) 
        as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
     destruct (partition_inequalities (a :: sys))
        as [[lt0_is eq0_is] gt0_is] eqn:Hpart_is.
     destruct Hsplit as [Hsplit|[Hsplit|Hsplit]];
     destruct Hsplit as [Ha_le0 [Ha_ge0 [Hlt0 [Hgt0 Heq0]]]].
     - rewrite Heq0.
       destruct (trivial_consistency (a :: eq0_sys)) eqn:Hconsis.
       * apply trivial_consistency_cons in Hconsis. 
         destruct Hconsis as [Ha_cons Heq0_cons].
         rewrite Heq0_cons in IHsys.
         rewrite Hlt0; rewrite Hgt0.
         destruct satisfy_bounds.
         - intros sol Hsol.
           specialize (IHsys sol Hsol).
           apply is_linear_system_solution_cons.
           split.
           * unfold is_linear_system_solution, interpret_inequalities,
             interpret_inequality, interpret_inequality_helper; split; last easy.
             apply (trivial_consistency_single_ineq a sol) in Ha_cons.
             unfold is_linear_system_solution, interpret_inequalities,
             interpret_inequality, interpret_inequality_helper in Ha_cons.
             destruct Ha_cons as [Ha_cons Htrivial].
             apply ax_real_leq_true in Ha_le0, Ha_ge0, Ha_cons.
             apply ax_real_leq_true; RSOPM_realize.
             rewrite ax_zero_is_zero in Ha_le0, Ha_ge0, Ha_cons.
             assert (INJ_RSOPM RSOPM (a 1%nat) = 0%R) as Hhelp. lra.
             rewrite Hhelp. lra.
           * apply IHsys.
         - apply no_linear_system_solution_cons.
           apply IHsys. 
       * rewrite trivial_consistency_andb in Hconsis.
         destruct (trivial_consistency eq0_sys) eqn:Heq0_cons.
         - rewrite Bool.andb_true_r in Hconsis.
           intro Hsol.
           destruct Hsol as [not_sol Hnot_sol].
           apply is_linear_system_solution_cons in Hnot_sol.
           destruct Hnot_sol as [Hnot_a Hnot_sys].
           unfold trivial_consistency in Hconsis.
           rewrite Bool.andb_true_r in Hconsis.
           unfold is_linear_system_solution, interpret_inequalities,
           interpret_inequality, interpret_inequality_helper in Hnot_a.
           destruct Hnot_a as [Hnot_a Htrivial].
           apply ax_real_leq_true in Ha_le0, Ha_ge0, Hnot_a.
           rewrite ax_real_plus, ax_real_mult in Hnot_a.
           apply ax_real_leq_false in Hconsis.
           rewrite ax_zero_is_zero in Ha_le0,Ha_ge0, Hnot_a, Hconsis.
           assert (INJ_RSOPM RSOPM (a 1%nat) = 0%R) as Hhelp. lra.
           rewrite Hhelp in Hnot_a. lra.
         - apply no_linear_system_solution_cons.
           apply IHsys.  
     - rewrite Heq0.
       destruct (trivial_consistency eq0_sys).
       * rewrite Hlt0; rewrite Hgt0.
         destruct (satisfy_bounds (compute_lb lt0_sys) _) eqn:Hbounds_sys.
         - destruct (satisfy_bounds (compute_lb (a :: _)) _) eqn:Hbounds_is.
           * intros sol Hsol.
             apply is_linear_system_solution_cons; split.
             - admit.
             - admit.
           *         
         - rewrite satisfy_bounds_none_preservation; last apply Hbounds_sys.
           apply no_linear_system_solution_cons.
           apply IHsys.
       * apply no_linear_system_solution_cons.
         apply IHsys.     
     -*)

Definition guaranteed_extract (sys: LinearSystem 1): T RSOPM :=
    match trivial_extract sys with
    | Some s => s
    | None => 0
    end.
 
Definition compose_inequalities {n: nat} (sys1 sys2: LinearSystem n): LinearSystem n :=
    map
    (fun prod_el: LinearInequality n * LinearInequality n =>
         let (ineq1, ineq2) := prod_el in 
        (fun i => (ineq1 i/ineq1 n) + (ineq2 i/ineq2 n)))
    (list_prod sys1 sys2).

Definition remove_var {n: nat} (sys: LinearSystem (S n)): LinearSystem n :=
    let (p, gt0) := partition_inequalities sys in
    let (lt0, eq0) := p in
    (compose_inequalities lt0 gt0) ++ eq0.

Fixpoint insert_solution_helper {n: nat} 
    (ineq: LinearInequality n)
    (sol: LinearSystemSolution n)
    : T RSOPM :=
    match n with
    | 0 => ineq 0%nat * sol 0%nat
    | S i => ineq i * sol i + insert_solution_helper (n:=i) ineq sol 
    end.

Definition insert_solution {n: nat} 
    (sys: LinearSystem (S n))
    (sol: LinearSystemSolution n)
    : LinearSystem 1 :=
    map
    (fun ineq => 
        fun i =>
        match i with
        | 1 => ineq (S n)
        | _ => insert_solution_helper ineq sol
        end)
    sys.

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
        | Some subsol => Some
            (fun sol_arg =>
            match sol_arg with
            | S i => guaranteed_extract (insert_solution sys subsol)
            | _ => subsol sol_arg 
            end)
        | None => None
        end
    end.

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
Admitted.     

End FourierMotzkinImplementation.