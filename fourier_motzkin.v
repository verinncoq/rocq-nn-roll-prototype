From Coq Require Import List Reals Lra Bool Logic Classical_Prop Classical_Pred_Type.
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

Print andb.

Fixpoint trivial_consistency (sys: LinearSystem 0): bool :=
match sys with
| nil => true
| ineq :: tail => andb (ineq 0%nat <= 0) (trivial_consistency tail) 
end.

Lemma plus2 : plus 2 2 = 4.
Proof.
simpl.
reflexivity.
Qed.

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



Definition bool_to_Prop (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
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

Coercion bool_to_Prop : bool >-> Sortclass.

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

Print map.

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
  (* Notiz für Malte von Andrei:  
        es war ein Problem mit Quantoren und zu frühem intros
          intros lt0 eq0 gt0 macht die drei zu festen Variablen in IHsys,
        man muss zuerst induction und dann intros
          dann entsteht ein IHsys mit forall lt0 eq0 gt0, ...
  *)
Qed.

Check Rle.

Lemma RSOPM_le_refl : forall x : T RSOPM, x <= x = true.
Proof.
  intro x.
  unfold "<=".
  apply ax_real_leq_true.
  apply Rle_refl.
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

Lemma RSOPM_mult_0_r : forall x : T RSOPM, 0* x = 0.
Proof.
intro.
apply ax_equality.
RSOPM_realize.
Admitted.

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

Lemma RSOPM_le_and_le_eq : forall x y : T RSOPM, (x <= y) /\ (y <= x) <-> (x=y).
Proof.
intros.
repeat rewrite <- RSOPM_bool_prop.
split.
intro.
apply ax_equality.
rewrite <- Rle_le_eq.
repeat rewrite ax_real_leq_true in H.
exact H.
intro.
rewrite H.
split.
apply RSOPM_le_refl.
apply RSOPM_le_refl.
Qed.

Lemma RSOPM_le_trans : forall x y z : T RSOPM, (x <= y) = true  -> (y <= z) = true -> (x <= z) = true .
Proof.
intros x y z.
repeat rewrite ax_real_leq_true.
Admitted.

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

Lemma partition_head_eq0 {n:nat} (sys: LinearSystem n) : forall a lt0 eq0 gt0 lt02 eq02 gt02, (lt0,eq0,gt0) = partition_inequalities sys  -> 
      (a n = 0) -> (partition_inequalities (n:= n) (a :: sys) = (lt02, eq02, gt02)) ->
(lt02,eq02,gt02)=(lt0,a::eq0, gt0).
Proof.
intros.
unfold partition_inequalities in H1.
unfold partition_inequalities in H.
destruct (partition (fun ineq : nat -> T RSOPM => ineq n <= 0) (a :: sys)) as [le0_a gt0_a] eqn:Hpartition1.
destruct (partition (fun ineq : nat -> T RSOPM => 0 <= ineq n) le0_a) as [eq0_a lt0_a] eqn:Hpartition2.
unfold partition in Hpartition1.
destruct ((fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list
(nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl =>
let (g, d) := partition tl in
if x n <= 0 then (x :: g, d)
else (g, x :: d)
end) sys) eqn:H3.
destruct (a n <= 0) eqn:H2.
injection Hpartition1 as Hpartition1_a Hpartition1_b.
rewrite <- Hpartition1_a in Hpartition2.
unfold partition in Hpartition2.
destruct (
(fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl => let (g, d) := partition tl in if 0 <= x n then (x :: g, d)
else (g, x :: d)
end) l) eqn:H5.
destruct (0 <= a n) eqn:H4.
unfold partition in H.
rewrite H3 in H.
destruct ((fix partition (l : list (nat -> T RSOPM)) : list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl => let (g, d) := partition tl in if 0 <= x n then (x :: g, d) else (g, x :: d)
end) l) eqn:H6.
injection H as HH1 HH2.
injection H5 as HH5.
injection Hpartition2 as Hpartition2_a Hpartition2_b.
subst. rewrite <-  H1. 
reflexivity.
rewrite H0 in H4.
rewrite RSOPM_le_refl in H4.
discriminate.
rewrite H0 in H2.
rewrite RSOPM_le_refl in H2.
discriminate.
(*Yes there should be some automation for this*)
Qed.

Lemma partition_head_lt0 {n:nat} (sys: LinearSystem n) : forall a lt0 eq0 gt0 lt02 eq02 gt02, (lt0,eq0,gt0) = partition_inequalities sys  -> 
      ((a n <= 0) /\ ~ (0 <= a n)) -> (partition_inequalities (n:= n) (a :: sys) = (lt02, eq02, gt02)) ->
(lt02,eq02,gt02)=(a::lt0,eq0, gt0).
Proof.
intros.
unfold partition_inequalities in H1.
unfold partition_inequalities in H.
destruct (partition (fun ineq : nat -> T RSOPM => ineq n <= 0) (a :: sys)) as [le0_a gt0_a] eqn:Hpartition1.
destruct (partition (fun ineq : nat -> T RSOPM => 0 <= ineq n) le0_a) as [eq0_a lt0_a] eqn:Hpartition2.
unfold partition in Hpartition1.
destruct ((fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list
(nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl =>
let (g, d) := partition tl in
if x n <= 0 then (x :: g, d)
else (g, x :: d)
end) sys) eqn:H3.
destruct (a n <= 0) eqn:H2.
injection Hpartition1 as Hpartition1_a Hpartition1_b.
rewrite <- Hpartition1_a in Hpartition2.
unfold partition in Hpartition2.
destruct (
(fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl => let (g, d) := partition tl in if 0 <= x n then (x :: g, d)
else (g, x :: d)
end) l) eqn:H5.
destruct (0 <= a n) eqn:H4.
destruct H0 as [H01 H02].
contradiction.
unfold partition in H.
rewrite H3 in H.
destruct ((fix partition (l : list (nat -> T RSOPM)) : list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl => let (g, d) := partition tl in if 0 <= x n then (x :: g, d) else (g, x :: d)
end) l) eqn:H6.
injection H as HH1 HH2.
injection H5 as HH5.
injection Hpartition2 as Hpartition2_a Hpartition2_b.
subst. rewrite <-  H1. 
reflexivity.
rewrite <- H2 in H0.
injection Hpartition1 as Hpartition1_a Hpartition1_b.
rewrite <- Hpartition1_a in Hpartition2.
unfold partition in Hpartition2.
destruct (
(fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl => let (g, d) := partition tl in if 0 <= x n then (x :: g, d)
else (g, x :: d)
end) l) eqn:H5.
destruct (0 <= a n) eqn:H4.
destruct H0 as [H01 H02].
exfalso. apply H02. exact I.
assert (0 <= a n \/ a n <= 0) as H6.
apply RSOPM_total_order_prop.
- destruct H6.
  + rewrite H4 in H6. contradiction.
  + rewrite H2 in H6. contradiction.
Qed.

Lemma partition_head_gt0 {n:nat} (sys: LinearSystem n) : forall a lt0 eq0 gt0 lt02 eq02 gt02, (lt0,eq0,gt0) = partition_inequalities sys  -> 
      (~ (a n <= 0) /\ (0 <= a n)) -> (partition_inequalities (n:= n) (a :: sys) = (lt02, eq02, gt02)) ->
(lt02,eq02,gt02)=(lt0,eq0, a::gt0).
Proof.
intros.
unfold partition_inequalities in H1.
unfold partition_inequalities in H.
destruct (partition (fun ineq : nat -> T RSOPM => ineq n <= 0) (a :: sys)) as [le0_a gt0_a] eqn:Hpartition1.
destruct (partition (fun ineq : nat -> T RSOPM => 0 <= ineq n) le0_a) as [eq0_a lt0_a] eqn:Hpartition2.
unfold partition in Hpartition1.
destruct ((fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list
(nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl =>
let (g, d) := partition tl in
if x n <= 0 then (x :: g, d)
else (g, x :: d)
end) sys) eqn:H3.
destruct (a n <= 0) eqn:H2.
destruct H0 as [f t].
unfold "~" in f. exfalso. apply f. exact I.
injection Hpartition1 as Hpartition1_a Hpartition1_b.
rewrite <- Hpartition1_a in Hpartition2.
unfold partition in Hpartition2.
destruct (
(fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl => let (g, d) := partition tl in if 0 <= x n then (x :: g, d)
else (g, x :: d)
end) l) eqn:H5.
destruct (0 <= a n) eqn:H4.
unfold partition in H.
rewrite H3 in H.
destruct ((fix partition (l : list (nat -> T RSOPM)) : list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl => let (g, d) := partition tl in if 0 <= x n then (x :: g, d) else (g, x :: d)
end) l) eqn:H6.
injection H as HH1 HH2.
injection H5 as HH5.
injection Hpartition2 as Hpartition2_a Hpartition2_b.
subst. rewrite <-  H1. 
reflexivity.
destruct H0 as [H01 H02].
contradiction.
Qed.
    
Lemma partition_head {n:nat} (sys: LinearSystem n) (a: LinearInequality n) : forall lt0 eq0 gt0 lt02 eq02 gt02, (lt0,eq0,gt0) = partition_inequalities sys  -> 
      (partition_inequalities (n:= n) (a :: sys) = (lt02, eq02, gt02) ->
      ((lt02,eq02,gt02)=(a::lt0, eq0, gt0) \/ (lt02,eq02,gt02)=(lt0,a::eq0, gt0) \/ (lt02,eq02,gt02)=(lt0,eq0, a::gt0))).
Proof.
intros.
assert (H0' := H0).
unfold partition_inequalities in H0.
destruct (partition (fun ineq : nat -> T RSOPM => ineq n <= 0) (a :: sys)) as [le0_a gt0_a] eqn:Hpartition1.
destruct (partition (fun ineq : nat -> T RSOPM => 0 <= ineq n) le0_a) as [eq0_a lt0_a] eqn:Hpartition2.
unfold partition in Hpartition1. 
destruct  ((fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl =>
let (g, d) := partition tl in
if x n <= 0 then (x :: g, d) else (g, x :: d)
end) sys) eqn:H1.
destruct (a n <= 0) eqn:Hpartition1_a.
apply pair_equal_spec in Hpartition1.
destruct Hpartition1 as [Hle0_a Hgt0_a].
rewrite <- Hle0_a in Hpartition2.
unfold partition in Hpartition2.
destruct ((fix partition (l : list (nat -> T RSOPM)) :
list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
match l with
| [] => ([], [])
| x :: tl =>
let (g, d) := partition tl in
if 0 <= x n then (x :: g, d) else (g, x :: d)
end) l) eqn:H2.
destruct (0 <= a n) eqn:Hpartition2_a.
right. left.
apply (partition_head_eq0 sys).
exact H.
apply RSOPM_le_and_le_eq.
split. 
rewrite Hpartition1_a. exact I.
rewrite Hpartition2_a. exact I.
exact H0'.
left. 
apply (partition_head_lt0 sys).
exact H.
split.
rewrite Hpartition1_a. exact I.
rewrite Hpartition2_a. unfold "~". intro. exact H3.
exact H0'.
destruct (0 <= a n) eqn:Hpartition2_a.
right. right.
apply (partition_head_gt0 sys).
exact H. 
split. rewrite Hpartition1_a.
unfold "~". intro. exact H2.
rewrite Hpartition2_a. exact I.
exact H0'.
(*irgendwas ist hier nicht ganz in richtiger reinfogle*)
Admitted.

Lemma trivial_extract_correct:
    forall (sys: LinearSystem 1),
        match trivial_extract sys with
        | Some r => (forall sol, 
            sol 1%nat = r -> is_linear_system_solution sys sol)
        | None => ~ (exists sol, is_linear_system_solution sys sol)
        end. 
Proof.
    intro sys.
    induction sys.
    destruct (trivial_extract []) eqn: Hextract.
    intros.
    unfold is_linear_system_solution.
    unfold interpret_inequalities.
    exact I.
    unfold trivial_extract in Hextract.
          destruct (partition_inequalities []) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
           unfold satisfy_bounds in Hextract.
           destruct (trivial_consistency eq0_sys) eqn:Htrivial.
          - destruct (compute_lb lt0_sys) eqn:Hlb.
          + destruct (compute_ub gt0_sys) eqn:Hub.
            * destruct (t <= t0) eqn:Hle.
            * discriminate.
            unfold partition_inequalities in Hpart_sys.
            unfold partition in Hpart_sys.
            apply pair_equal_spec in Hpart_sys; destruct Hpart_sys as [Hpart1 Hpart2].
            apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
            unfold compute_lb in Hlb. 
            rewrite <- Hpart1 in Hlb.
            simpl in Hlb.
            discriminate. discriminate.
            unfold is_linear_system_solution.
            destruct (compute_ub gt0_sys) eqn:H1; discriminate.
            unfold "~". intro H.
            unfold partition_inequalities in Hpart_sys.
            unfold partition in Hpart_sys.
            apply pair_equal_spec in Hpart_sys; destruct Hpart_sys as [Hpart1 Hpart2].
            apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
            rewrite <- Hpart3 in Htrivial.
            unfold trivial_consistency in Htrivial. discriminate.
    destruct (a 1%nat <= 0) eqn:Hlt0.
    destruct (0 <= a 1%nat) eqn:Hgt0.
    
    destruct (trivial_extract (a::sys)) eqn: Hextract.
    intros.
    unfold is_linear_system_solution.
    unfold interpret_inequalities.
    split.
    unfold trivial_extract in Hextract.

    destruct (trivial_extract sys) eqn:Hextract.
    unfold trivial_extract in Hextract.
    destruct (partition_inequalities sys) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
   * intros sol Hsol.
     destruct (trivial_consistency eq0_sys) eqn:Htriv_cons; try discriminate.
     apply (partition_inequalities_solutions _ lt0_sys eq0_sys gt0_sys). 
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
           induction sys.
           unfold trivial_extract in Hextract.
          destruct (partition_inequalities []) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
           unfold satisfy_bounds in Hextract.
           destruct (trivial_consistency eq0_sys) eqn:Htrivial.
          - destruct (compute_lb lt0_sys) eqn:Hlb.
          + destruct (compute_ub gt0_sys) eqn:Hub.
            * destruct (t <= t0) eqn:Hle.
            * discriminate.
            unfold partition_inequalities in Hpart_sys.
            unfold partition in Hpart_sys.
            apply pair_equal_spec in Hpart_sys; destruct Hpart_sys as [Hpart1 Hpart2].
            apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
            unfold compute_lb in Hlb. 
            rewrite <- Hpart1 in Hlb.
            simpl in Hlb.
            discriminate. discriminate.
            unfold is_linear_system_solution.
            destruct (compute_ub gt0_sys) eqn:H1; discriminate.
            unfold "~". intro H.
            unfold partition_inequalities in Hpart_sys.
            unfold partition in Hpart_sys.
            apply pair_equal_spec in Hpart_sys; destruct Hpart_sys as [Hpart1 Hpart2].
            apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
            rewrite <- Hpart3 in Htrivial.
            unfold trivial_consistency in Htrivial. discriminate.
            (*ab hier induktionsschluss*)
            unfold is_linear_system_solution.
            unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
            unfold trivial_extract in Hextract.
            destruct (partition_inequalities (a::sys)) 
      as [[lt0_sys_a eq0_sys_a] gt0_sys_a] eqn:Hpart_sys_a.
            unfold trivial_extract in IHsys.
            destruct (partition_inequalities (sys)) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
            assert (Hpart_sys_a' := Hpart_sys_a).
            assert (Hpart_sys' := Hpart_sys).
            destruct (a 1%nat <= 0) eqn : Hcomp.
            destruct (0 <= a 1%nat) eqn : Hcomp2.
            assert ((lt0_sys_a, eq0_sys_a, gt0_sys_a) = (lt0_sys, a::eq0_sys, gt0_sys)).
            apply (partition_head_eq0 sys a lt0_sys eq0_sys gt0_sys lt0_sys_a eq0_sys_a gt0_sys_a).
            rewrite Hpart_sys. reflexivity.
            apply RSOPM_le_and_le_eq. split.
            rewrite Hcomp. exact I.
            rewrite Hcomp2. exact I.
            exact Hpart_sys_a.
            assert ((lt0_sys_a, eq0_sys_a, gt0_sys_a) = (lt0_sys, a::eq0_sys, gt0_sys)).
            apply (partition_head_eq0 sys a lt0_sys eq0_sys gt0_sys lt0_sys_a eq0_sys_a gt0_sys_a).
            rewrite Hpart_sys. reflexivity.
            apply RSOPM_le_and_le_eq.
            rewrite Hcomp. rewrite Hcomp2.
            split; exact I.
            exact Hpart_sys_a.
            apply or_not_and.
            unfold interpret_inequality.
            unfold interpret_inequality_helper.
            destruct (a 0%nat <= 0) eqn:Ha.
            (*eigentlich müsst hier beweis dass linke seite falsch?*)
            right.
            apply IHsys.
            injection H as H1 H2.
            subst.
            destruct (trivial_consistency eq0_sys) eqn:Htrivial.
            destruct (trivial_consistency (a::eq0_sys)) eqn:Htriviala.
            (*Case 1*)
            exact Hextract.
            (*Case 2*)
            unfold trivial_consistency in Htriviala.
            rewrite Ha in Htriviala.
            simpl in Htriviala.
            fold trivial_consistency in Htriviala.
            rewrite Htriviala in Htrivial.
            discriminate.
            reflexivity.
            left.
            assert (a 1%nat = 0).
            apply RSOPM_le_and_le_eq.
            rewrite Hcomp. rewrite Hcomp2. 
            split; exact I.
            rewrite H1.
            rewrite RSOPM_mult_0_r.
            rewrite RSOPM_plus_comm.
            rewrite RSOPM_plus_0_r.
            unfold "<>". rewrite Ha.
            discriminate.
            (*schwierteil startet jetzt:*)
            assert ((lt0_sys_a, eq0_sys_a, gt0_sys_a) = (a::lt0_sys, eq0_sys, gt0_sys)).
            apply (partition_head_lt0 sys a lt0_sys eq0_sys gt0_sys lt0_sys_a eq0_sys_a gt0_sys_a).
            rewrite Hpart_sys. reflexivity.
            rewrite Hcomp. 
            rewrite Hcomp2.
            unfold "~". split.
            exact I. intro. exact H.
            exact Hpart_sys_a.
            injection H as H1 H2.
            subst.
            destruct (trivial_consistency eq0_sys) eqn:Htrivial.
            apply or_not_and.
            unfold interpret_inequality.
            unfold interpret_inequality_helper.
            destruct ((a 1%nat) * (sol 1%nat) + (a 0%nat) <= 0) eqn: Hsol.
            assert ((true <> true) <-> false).
            split.
            - intros H. apply H. reflexivity. (* Contradiction *)
            - intros H. exfalso. apply H. (* False case *)
            rewrite H.
            assert (forall P: Prop, (false \/ P) <-> P).
            intro P.
            tauto.
            rewrite H0.
            unfold is_linear_system_solution in IHsys.
            apply IHsys.
            unfold satisfy_bounds.
            destruct (compute_lb lt0_sys) as [lb |] eqn:Hlb;
            destruct (compute_ub gt0_sys) as [ub |] eqn:Hub;
            try discriminate.
            (* Now, we only have the case where lb > ub *)
            destruct (lb <= ub) eqn:Hleb.
            - rewrite <- Hextract.
              unfold compute_lb.
              unfold map.
              unfold RSOPM_list_max. fold RSOPM_list_max.
              unfold compute_lb in Hlb. 
              unfold map in Hlb. 
              rewrite Hlb.
            (* Now show, that sol is smaller then lowerbound*)
            destruct (- (a 0%nat / a 1%nat) <= lb ) eqn:Hlb3.
            unfold satisfy_bounds.
            rewrite Hleb.
            reflexivity.
            unfold satisfy_bounds.
            destruct (- (a 0%nat / a 1%nat) <= ub ) eqn:Hub3.
            assert ((- (a 0%nat / a 1%nat) <= ub) = false).
            (*Hier Hleb und Hleb kombinieren mit RSOPM transitivity*)
            admit.
            rewrite H1 in Hub3.
            discriminate.
            fold map in Hlb.
            destruct lt0_sys eqn:Hlt0_sys.
            unfold RSOPM_list_max in Hlb.
            rewrite Hlb. reflexivity.

            (* Hier ist endstation: Da sys consistent is entspricht es nicht der vorraussetzung. 
            Eigentlich müsste die induktion also früher beginnen*)
            - (* Here, we need to show `lb > ub` *)
            apply leb_complete_conv in Hleb. (* Converts `leb lb ub = false` into `lb > ub` *)
            assumption. (* Use existing hypothesis if available *)

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
     apply (partition_inequalities_solutions _ lt0_sys eq0_sys gt0_sys). 
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
           induction sys.
           unfold trivial_extract in Hextract.
          destruct (partition_inequalities []) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
           unfold satisfy_bounds in Hextract.
           destruct (trivial_consistency eq0_sys) eqn:Htrivial.
          - destruct (compute_lb lt0_sys) eqn:Hlb.
          + destruct (compute_ub gt0_sys) eqn:Hub.
            * destruct (t <= t0) eqn:Hle.
            * discriminate.
            unfold partition_inequalities in Hpart_sys.
            unfold partition in Hpart_sys.
            apply pair_equal_spec in Hpart_sys; destruct Hpart_sys as [Hpart1 Hpart2].
            apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
            unfold compute_lb in Hlb. 
            rewrite <- Hpart1 in Hlb.
            simpl in Hlb.
            discriminate. discriminate.
            unfold is_linear_system_solution.
            destruct (compute_ub gt0_sys) eqn:H1; discriminate.
            unfold "~". intro H.
            unfold partition_inequalities in Hpart_sys.
            unfold partition in Hpart_sys.
            apply pair_equal_spec in Hpart_sys; destruct Hpart_sys as [Hpart1 Hpart2].
            apply pair_equal_spec in Hpart1; destruct Hpart1 as [Hpart1 Hpart3].
            rewrite <- Hpart3 in Htrivial.
            unfold trivial_consistency in Htrivial. discriminate.
            (*ab hier induktionsschluss*)
            unfold is_linear_system_solution.
            unfold interpret_inequalities. fold (interpret_inequalities (n:=1)).
            unfold trivial_extract in Hextract.
            destruct (partition_inequalities (a::sys)) 
      as [[lt0_sys_a eq0_sys_a] gt0_sys_a] eqn:Hpart_sys_a.
            unfold trivial_extract in IHsys.
            destruct (partition_inequalities (sys)) 
      as [[lt0_sys eq0_sys] gt0_sys] eqn:Hpart_sys.
            assert (Hpart_sys_a' := Hpart_sys_a).
            assert (Hpart_sys' := Hpart_sys).
            destruct (a 1%nat <= 0) eqn : Hcomp.
            destruct (0 <= a 1%nat) eqn : Hcomp2.
            assert ((lt0_sys_a, eq0_sys_a, gt0_sys_a) = (lt0_sys, a::eq0_sys, gt0_sys)).
            apply (partition_head_eq0 sys a lt0_sys eq0_sys gt0_sys lt0_sys_a eq0_sys_a gt0_sys_a).
            rewrite Hpart_sys. reflexivity.
            apply RSOPM_le_and_le_eq. split.
            rewrite Hcomp. exact I.
            rewrite Hcomp2. exact I.
            exact Hpart_sys_a.
            assert ((lt0_sys_a, eq0_sys_a, gt0_sys_a) = (lt0_sys, a::eq0_sys, gt0_sys)).
            apply (partition_head_eq0 sys a lt0_sys eq0_sys gt0_sys lt0_sys_a eq0_sys_a gt0_sys_a).
            rewrite Hpart_sys. reflexivity.
            apply RSOPM_le_and_le_eq.
            rewrite Hcomp. rewrite Hcomp2.
            split; exact I.
            exact Hpart_sys_a.
            apply or_not_and.
            unfold interpret_inequality.
            unfold interpret_inequality_helper.
            destruct (a 0%nat <= 0) eqn:Ha.
            (*eigentlich müsst hier beweis dass linke seite falsch?*)
            right.
            apply IHsys.
            injection H as H1 H2.
            subst.
            destruct (trivial_consistency eq0_sys) eqn:Htrivial.
            destruct (trivial_consistency (a::eq0_sys)) eqn:Htriviala.
            (*Case 1*)
            exact Hextract.
            (*Case 2*)
            unfold trivial_consistency in Htriviala.
            rewrite Ha in Htriviala.
            simpl in Htriviala.
            fold trivial_consistency in Htriviala.
            rewrite Htriviala in Htrivial.
            discriminate.
            reflexivity.
            left.
            assert (a 1%nat = 0).
            apply RSOPM_le_and_le_eq.
            rewrite Hcomp. rewrite Hcomp2. 
            split; exact I.
            rewrite H1.
            rewrite RSOPM_mult_0_r.
            rewrite RSOPM_plus_comm.
            rewrite RSOPM_plus_0_r.
            unfold "<>". rewrite Ha.
            discriminate.
            (*schwierteil startet jetzt:*)
            assert ((lt0_sys_a, eq0_sys_a, gt0_sys_a) = (a::lt0_sys, eq0_sys, gt0_sys)).
            apply (partition_head_lt0 sys a lt0_sys eq0_sys gt0_sys lt0_sys_a eq0_sys_a gt0_sys_a).
            rewrite Hpart_sys. reflexivity.
            rewrite Hcomp. 
            rewrite Hcomp2.
            unfold "~". split.
            exact I. intro. exact H.
            exact Hpart_sys_a.
            injection H as H1 H2.
            subst.
            destruct (trivial_consistency eq0_sys) eqn:Htrivial.
            apply or_not_and.
            unfold interpret_inequality.
            unfold interpret_inequality_helper.
            destruct ((a 1%nat) * (sol 1%nat) + (a 0%nat) <= 0) eqn: Hsol.
            assert ((true <> true) <-> false).
            split.
            - intros H. apply H. reflexivity. (* Contradiction *)
            - intros H. exfalso. apply H. (* False case *)
            rewrite H.
            assert (forall P: Prop, (false \/ P) <-> P).
            intro P.
            tauto.
            rewrite H0.
            unfold is_linear_system_solution in IHsys.
            apply IHsys.
            unfold satisfy_bounds.
            destruct (compute_lb lt0_sys) as [lb |] eqn:Hlb;
            destruct (compute_ub gt0_sys) as [ub |] eqn:Hub;
            try discriminate.
            (* Now, we only have the case where lb > ub *)
            destruct (lb <= ub) eqn:Hleb.
            - rewrite <- Hextract.
              unfold compute_lb.
              unfold map.
              unfold RSOPM_list_max. fold RSOPM_list_max.
              unfold compute_lb in Hlb. 
              unfold map in Hlb. 
              rewrite Hlb.
            (* Now show, that sol is smaller then lowerbound*)
            destruct (- (a 0%nat / a 1%nat) <= lb ) eqn:Hlb3.
            unfold satisfy_bounds.
            rewrite Hleb.
            reflexivity.
            unfold satisfy_bounds.
            destruct (- (a 0%nat / a 1%nat) <= ub ) eqn:Hub3.
            assert ((- (a 0%nat / a 1%nat) <= ub) = false).
            (*Hier Hleb und Hleb kombinieren mit RSOPM transitivity*)
            admit.
            rewrite H1 in Hub3.
            discriminate.
            fold map in Hlb.
            destruct lt0_sys eqn:Hlt0_sys.
            unfold RSOPM_list_max in Hlb.
            rewrite Hlb. reflexivity.

            (* Hier ist endstation: Da sys consistent is entspricht es nicht der vorraussetzung. 
            Eigentlich müsste die induktion also früher beginnen*)
            - (* Here, we need to show `lb > ub` *)
            apply leb_complete_conv in Hleb. (* Converts `leb lb ub = false` into `lb > ub` *)
            assumption. (* Use existing hypothesis if available *)

            
            

            (*ab hier alter versuch*)
            unfold partition_inequalities in Hpart_sys.
            destruct (partition (fun ineq : nat -> T RSOPM => ineq 1%nat <= 0) (a :: sys)) as [le0 gt0] eqn:Hpartition1.
            destruct (partition (fun ineq : nat -> T RSOPM => 0 <= ineq 1%nat) le0) as [eq0 lt0] eqn:Hpartition2.
            inversion Hpart_sys; subst.
            unfold partition in Hpartition1.  
            destruct
              ((fix partition (l : list (nat -> T RSOPM)) :
              list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
              match l with
              | [] => ([], [])
              | x :: tl =>
              let (g, d) := partition tl in
              if x 1%nat <= 0 then (x :: g, d) else (g, x :: d)
              end) sys).
            destruct (a 1%nat <= 0) eqn:Hpartition_sys.
            injection Hpartition1 as Hle0 Hgt0.
            rewrite <- Hle0 in Hpartition2.
            unfold partition in Hpartition2.
            destruct
              ((fix partition (l : list (nat -> T RSOPM)) :
              list (nat -> T RSOPM) * list (nat -> T RSOPM) :=
              match l with
              | [] => ([], [])
              | x :: tl =>
              let (g, d) := partition tl in
              if 0 <= x 1%nat then (x :: g, d) else (g, x :: d)
              end) l).
            destruct (0 <=  a 1%nat) eqn:Hpartition2_sys.
            injection Hpartition2 as H2eq0 H2lt0.
            rewrite <- H2eq0 in Hextract.
            unfold satisfy_bounds in Hextract.
                 - destruct (compute_lb lt0_sys) eqn:Hlb.
          + destruct (compute_ub gt0_sys) eqn:Hub.
            * destruct (t <= t0) eqn:Hle.
            destruct (trivial_consistency (a :: l1)) eqn:Htrivial.
            setoid_rewrite Htrivial in Hextract.
            discriminate.
            setoid_rewrite Htrivial in Hextract.
            unfold trivial_consistency in Htrivial.
            pose proof ((negb_andb (a 0%nat <= 0) ((fix trivial_consistency (sys : LinearSystem 0) : bool :=
              match sys with
                | [] => true
                | ineq :: tail => (ineq 0%nat <= 0) &&
                  trivial_consistency tail
              end) l1))) as Hdemorgan.
            rewrite Htrivial in Hdemorgan.
            unfold negb in Hdemorgan.
            destruct (a 0%nat <= 0) eqn:H2le0.
            rewrite orb_false_l in Hdemorgan.
            destruct (
            (fix trivial_consistency (sys : LinearSystem 0) : bool :=
            match sys with
              | [] => true
              | ineq :: tail =>
              (ineq 0%nat <= 0) && trivial_consistency tail
            end) l1) eqn: Hcons.
            discriminate.
            assert (forall lt0 eq0 gt0, partition_inequalities sys = (lt0,eq0,gt0) -> l1 = eq0). 
            intros.
            destruct l1 as [| ineq tail].
            discriminate.





            (*Note: Fallunterscheidung für a: in welcher partition ist es? 
            Wenn es nicht in der partition eq0 ist, dann ist trivial_extract sys = trivial_extract a :: sys
            also kann man IHsys benutzen.
            Falls a in eq0 ist, dann muss man anders ran.
            *)
            admit.
            admit.
            admit.
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
    destruct (trivial_extract sys) as [s |] eqn:Htrivial.

end
Admitted.     

End FourierMotzkinImplementation.