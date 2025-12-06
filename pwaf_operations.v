From Coq Require Import Nat List Reals Lia Lra Arith.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import real_subsets matrix_extensions piecewise_affine.

Import MatrixNotations.
Import RealSubsetNotations.
Open Scope list_scope.
Open Scope matrix_scope.
Open Scope colvec_scope.

Section PWAFConcatenation.

Context { RSOPM : RealSubsetOPM }.
Open Scope RSOPM_scope.

Fixpoint extend_lincons_at_bottom
    {in_dim: nat} 
    (lcs: list (LinearConstraint (RSOPM:=RSOPM) in_dim)) 
    (new_dim: nat): list (LinearConstraint new_dim) :=
    match lcs with 
    | nil => nil
    | (Constraint c b2) :: tail =>
        Constraint new_dim (extend_colvec_at_bottom c new_dim) b2 ::
            extend_lincons_at_bottom tail new_dim
    end.

Lemma extend_lincons_at_bottom_inv:
  forall d1 d2 (c1: colvec d1) b1 lc,
    In (Constraint d1 c1 b1) lc <->
      In (Constraint (d1 + d2) (extend_colvec_at_bottom c1 (d1 + d2)) b1)
        (extend_lincons_at_bottom lc (d1 + d2)).
Proof.
    intros d1 d2 c1 b1 lc.
    induction lc.
    * simpl. reflexivity.
    * split.
      {
        intros HIn.
        unfold extend_lincons_at_bottom.
        apply in_inv in HIn.
        destruct HIn.
        - rewrite H. apply in_eq. 
        - induction a as [c_a b_a]. 
          apply in_cons.
          apply IHlc.
          apply H.
      }
      {
        intros HIn.
        unfold extend_lincons_at_bottom in HIn.
        induction a as [c_a b_a].
        apply in_inv in HIn.
        destruct HIn.
        - inversion H.
          rewrite <- H2.
          apply extend_colvec_at_bottom_preserves_equality in H1.
          rewrite <- H1.
          apply in_eq.
        - apply in_cons.
          apply IHlc.
          apply H.
      }
Qed.

Fixpoint extend_lincons_on_top
    {in_dim: nat} 
    (lcs: list (LinearConstraint (RSOPM:=RSOPM) in_dim))
    (new_dim: nat): list (LinearConstraint new_dim) :=
    match lcs with 
    | nil => nil
    | (Constraint c b2) :: tail =>
        Constraint new_dim (extend_colvec_on_top c new_dim) b2 ::
            extend_lincons_on_top tail new_dim
    end.   
    
Lemma extend_lincons_on_top_inv:
    forall d1 d2 (c2: colvec d2) b2 lc,
      In (Constraint d2 c2 b2) lc <->
        In (Constraint (d1 + d2) (extend_colvec_on_top c2 (d1 + d2)) b2)
          (extend_lincons_on_top lc (d1 + d2)).
Proof.
  intros d1 d2 c2 b2 lc.
  induction lc.
  * simpl. reflexivity.
  * split.
    {
      intros HIn.
      unfold extend_lincons_on_top.
      apply in_inv in HIn.
      destruct HIn.
      - rewrite H. apply in_eq. 
      - induction a as [c_a b_a]. 
        apply in_cons.
        apply IHlc.
        apply H.
    }
    {
      intros HIn.
      unfold extend_lincons_on_top in HIn.
      induction a as [c_a b_a].
      apply in_inv in HIn.
      destruct HIn.
      - inversion H.
        rewrite <- H2.
        apply extend_colvec_on_top_preserves_equality in H1.
        rewrite <- H1.
        apply in_eq.
      - apply in_cons.
        apply IHlc.
        apply H.
    }
Qed.

Lemma extend_lincons_at_bottom_split:
  forall d1 d2 (v1: colvec d1) (v2: colvec d2) b 
    (constraints: list (LinearConstraint d1)),
      In (Constraint (d1 + d2) (colvec_concat v1 v2) b) 
        (extend_lincons_at_bottom constraints (d1 + d2)) ->
      v2 = null_vector d2 /\ 
      colvec_concat v1 v2 = extend_colvec_at_bottom v1 (d1 + d2).
Proof.
  intros d1 d2 v1 v2 b constraints HIn.
  induction constraints.
  * simpl in HIn. contradiction.
  * unfold extend_lincons_at_bottom in HIn.
    induction a as [c_a b_a].
    apply in_inv in HIn. 
    destruct HIn.
    - injection H.
      intros Hb Hcolvec.
      assert (Hgoal1: v2 = null_vector d2).
      {
        unfold colvec_concat in Hcolvec.
        unfold Mplus in Hcolvec.
        unfold extend_colvec_at_bottom in Hcolvec at 1.
        unfold mk_colvec in Hcolvec.
        pose proof (mk_matrix_ext (T:=T RSOPM)) as Hmatrix_ext.
        specialize (Hmatrix_ext (d1 + d2)%nat 1%nat).
        specialize (Hmatrix_ext (fun i _: nat => 
                                    if i <? d1 then
                                      coeff_colvec 0 c_a i
                                    else 
                                      0)).
        specialize (Hmatrix_ext (fun i j : nat =>
                            RSplus
                              (coeff_mat 0
                                (extend_colvec_at_bottom v1 (d1 + d2)) i j)
                              (coeff_mat 0 
                                (extend_colvec_on_top v2 (d1 + d2)) i j))).
        destruct Hmatrix_ext as [Hext1 Hext2].
        unfold null_vector. unfold mk_colvec.
        unfold colvec in v2.
        rewrite (coeff_mat_ext_aux 0 0 v2 _).
        intros i j Hi Hj.
        specialize (Hext2 Hcolvec (i + d1)%nat j).
        assert (Hi1: (i + d1 < d1 + d2)%nat). lia.
        specialize (Hext2 Hi1 Hj).
        assert (Hi2: (d1 <= i + d1)%nat). lia.
        rewrite <- Nat.ltb_ge in Hi2.
        rewrite Hi2 in Hext2.
        unfold extend_colvec_at_bottom in Hext2.
        unfold extend_colvec_on_top in Hext2.
        unfold mk_colvec in Hext2.
        repeat (rewrite coeff_mat_bij in Hext2; try lia).
        rewrite Nat.add_sub in Hext2.
        rewrite Hi2 in Hext2.
        rewrite RSOPM_plus_comm in Hext2.
        rewrite RSOPM_plus_0_r in Hext2.
        rewrite Nat.add_sub in Hext2.
        rewrite coeff_mat_bij; try lia.
        symmetry. induction j. apply Hext2. lia.
      }
      split.
      * apply Hgoal1.
      * unfold colvec_concat.
        unfold Mplus.
        unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec.
        apply mk_matrix_ext.
        intros i j Hi Hj.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub.
        remember (i <? d1) as i_d1.
        destruct i_d1.
        - rewrite (plus_zero_r (G:=RSOPM)). reflexivity.
        - rewrite (plus_zero_l (G:=RSOPM)).
          rewrite Hgoal1.
          unfold null_vector.
          unfold mk_colvec. unfold coeff_colvec.
          symmetry in Heqi_d1. rewrite Nat.ltb_ge in Heqi_d1.
          rewrite coeff_mat_bij; try lia.
          reflexivity.
    - apply IHconstraints.
      apply H.
Qed.

Lemma extend_lincons_on_top_split:
  forall d1 d2 (v1: colvec d1) (v2: colvec d2) b 
    (constraints: list (LinearConstraint d2)),
      In (Constraint (d1 + d2) (colvec_concat v1 v2) b) 
        (extend_lincons_on_top constraints (d1 + d2)) ->
      v1 = null_vector d1 /\ 
      colvec_concat v1 v2 = extend_colvec_on_top v2 (d1 + d2).
Proof.
  intros d1 d2 v1 v2 b constraints HIn.
  induction constraints.
  * simpl in HIn. contradiction.
  * unfold extend_lincons_on_top in HIn.
    induction a as [c_a b_a].
    apply in_inv in HIn. 
    destruct HIn.
    - injection H.
      intros Hb Hcolvec.
      assert (Hgoal1: v1 = null_vector d1).
      {
        unfold colvec_concat in Hcolvec.
        unfold Mplus in Hcolvec.
        unfold extend_colvec_on_top in Hcolvec at 1.
        rewrite Nat.add_sub in Hcolvec.
        unfold mk_colvec in Hcolvec.
        pose proof (mk_matrix_ext (T:=RSOPM)) as Hmatrix_ext.
        specialize (Hmatrix_ext (d1 + d2)%nat 1%nat).
        specialize (Hmatrix_ext (fun i _: nat => 
                                    if i <? d1 then
                                      0
                                    else 
                                      coeff_colvec 0 c_a (i - d1))).
        specialize (Hmatrix_ext (fun i j : nat =>
                                    RSplus
                                      (coeff_mat RSzero
                                        (extend_colvec_at_bottom v1 (d1 + d2)) i j)
                                      (coeff_mat RSzero
                                        (extend_colvec_on_top v2 (d1 + d2)) i j))).
        destruct Hmatrix_ext as [Hext1 Hext2].
        unfold null_vector. unfold mk_colvec.
        unfold colvec in v1.
        rewrite (coeff_mat_ext_aux 0 0 v1 _).
        intros i j Hi Hj.
        specialize (Hext2 Hcolvec i j).
        assert (Hi1: (i < d1 + d2)%nat). lia.
        specialize (Hext2 Hi1 Hj).
        pose proof Hi as Hi_cp.
        rewrite <- Nat.ltb_lt in Hi_cp.
        rewrite Hi_cp in Hext2.
        unfold extend_colvec_at_bottom in Hext2.
        unfold extend_colvec_on_top in Hext2.
        unfold mk_colvec in Hext2.
        repeat (rewrite coeff_mat_bij in Hext2; try lia).
        rewrite Nat.add_sub in Hext2.
        rewrite Hi_cp in Hext2.
        rewrite RSOPM_plus_0_r in Hext2.
        rewrite coeff_mat_bij; try lia.
        symmetry. induction j. apply Hext2. lia.
      }
      split.
      * apply Hgoal1.
      * unfold colvec_concat.
        unfold Mplus.
        unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec.
        apply mk_matrix_ext.
        intros i j Hi Hj.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub.
        remember (i <? d1) as i_d1.
        destruct i_d1.
        - rewrite (plus_zero_r (G:=RSOPM)).
          rewrite Hgoal1.
          unfold null_vector.
          unfold mk_colvec. unfold coeff_colvec.
          symmetry in Heqi_d1. rewrite Nat.ltb_lt in Heqi_d1.
          rewrite coeff_mat_bij; try lia.
          reflexivity.
        - rewrite (plus_zero_l (G:=RSOPM)). reflexivity.
    - apply IHconstraints.
      apply H.
Qed.

Definition concat_polyhedra
    {in_dim1 in_dim2: nat}
    (p_f: ConvexPolyhedron in_dim1) 
    (p_g: ConvexPolyhedron in_dim2): ConvexPolyhedron (in_dim1 + in_dim2) :=
    match p_f with
    | Polyhedron l1 =>
        match p_g with
        | Polyhedron l2 => 
            Polyhedron (in_dim1 + in_dim2) 
                (extend_lincons_at_bottom l1 (in_dim1 + in_dim2) ++ 
                extend_lincons_on_top l2 (in_dim1 + in_dim2))
        end
    end.

Lemma in_concat_polyhedra_inv:
    forall d1 d2 (x1: colvec d1) (x2: colvec d2) p1 p2,
        in_convex_polyhedron (colvec_concat x1 x2) (concat_polyhedra p1 p2) <->
        in_convex_polyhedron x1 p1 /\ in_convex_polyhedron x2 p2.
Proof.
    intros d1 d2 x1 x2 p1 p2.
    destruct p1 as [constraints1].
    destruct p2 as [constraints2].
    split.
    {
      unfold in_convex_polyhedron. 
      intros HIn.
      unfold in_convex_polyhedron in HIn.
      unfold concat_polyhedra in HIn.
      split.
      - intros constraint1 HcIn.
        destruct constraint1 as [c1 b1].
        specialize (HIn (Constraint _ (extend_colvec_at_bottom c1 (d1 + d2)) b1)).
        unfold satisfies_lc in HIn.
        unfold satisfies_lc.
        rewrite <- (dot_extend_at_bottom d1 d2 _ x1 x2).
        apply HIn.
        apply in_or_app.
        left.
        apply extend_lincons_at_bottom_inv.
        apply HcIn.
      - intros constraint2 HcIn.
        destruct constraint2 as [c2 b2].
        specialize (HIn (Constraint _ (extend_colvec_on_top c2 (d1 + d2)) b2)).
        unfold satisfies_lc in HIn.
        unfold satisfies_lc.
        rewrite <- (dot_extend_on_top d1 d2 _ x1 x2).
        apply HIn.
        apply in_or_app.
        right.
        apply extend_lincons_on_top_inv.
        apply HcIn.
    }
    {
      unfold in_convex_polyhedron. 
      intros HIn.
      destruct HIn as[HInx1 HInx2].
      unfold in_convex_polyhedron.
      unfold concat_polyhedra.
      intros constraint HconstraintIn.
      destruct constraint as [c b].
      apply in_app_or in HconstraintIn.
      pose proof (colvec_split (RSOPM:=RSOPM)).
      specialize (H d1 d2 c).
      destruct H as [c_top H].
      destruct H as [c_bottom H].
      destruct H as [Hctop_def H].
      destruct H as [Hcbottom_def Hc].
      rewrite Hc.
      destruct HconstraintIn. 
      * pose proof extend_lincons_at_bottom_inv as Hinv.
        specialize (Hinv d1 d2 c_top).
        unfold satisfies_lc.
        rewrite dot_concat.
        rewrite Hc in H.
        pose proof extend_lincons_at_bottom_split as H_lin_bot_split.
        specialize (H_lin_bot_split d1 d2 c_top c_bottom b).
        specialize (H_lin_bot_split constraints1 H).
        destruct H_lin_bot_split as [H_c_bottom_def Hconcat_def].
        rewrite H_c_bottom_def.
        rewrite dot_null_vector.
        rewrite RSOPM_plus_0_r.
        rewrite Hconcat_def in H.
        specialize (Hinv b constraints1).
        apply Hinv in H.
        apply HInx1 in H.
        unfold satisfies_lc in H.
        apply H.
      * pose proof extend_lincons_on_top_inv as Hinv.
        specialize (Hinv d1 d2 c_bottom).
        unfold satisfies_lc.
        rewrite dot_concat.
        rewrite Hc in H.
        pose proof extend_lincons_on_top_split as H_lin_top_split.
        specialize (H_lin_top_split d1 d2 c_top c_bottom b).
        specialize (H_lin_top_split constraints2 H).
        destruct H_lin_top_split as [H_c_top_def Hconcat_def].
        rewrite H_c_top_def.
        rewrite dot_null_vector.
        rewrite RSOPM_plus_comm.
        rewrite RSOPM_plus_0_r.
        rewrite Hconcat_def in H.
        specialize (Hinv b constraints2).
        apply Hinv in H.
        apply HInx2 in H.
        unfold satisfies_lc in H.
        apply H.
    }
Qed.

Definition concat_affine_functions 
    {in_dim1 in_dim2 out_dim1 out_dim2: nat}  
    (af1: AffineFunction in_dim1 out_dim1)
    (af2: AffineFunction in_dim2 out_dim2)
    : AffineFunction (RSOPM:=RSOPM) (in_dim1 + in_dim2) (out_dim1 + out_dim2) 
    := 
    match af1, af2 with 
    | Affine M_f b_f, Affine M_g b_g =>
      Affine _ _ (block_diag_matrix M_f M_g) (colvec_concat b_f b_g)
    end.

Lemma concat_affine_functions_value:
  forall in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 af1_x1 af2_x2
    (af1: AffineFunction in_dim1 out_dim1)
    (af2: AffineFunction in_dim2 out_dim2),
    is_affine_f_value af1 x1 af1_x1 ->
    is_affine_f_value af2 x2 af2_x2 ->
    is_affine_f_value (concat_affine_functions af1 af2) (colvec_concat x1 x2) (colvec_concat af1_x1 af2_x2).
Proof.  
  intros in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 af1_x1 af2_x2 af1 af2 Haf1_value Haf2_value.
  destruct af1 as [A1 b1].
  destruct af2 as [A2 b2].
  unfold is_affine_f_value.
  unfold is_affine_f_value in Haf1_value.
  unfold is_affine_f_value in Haf2_value.
  unfold concat_affine_functions.
  rewrite MMmult_block_diag_matrix.
  rewrite Mplus_colvec_concat.
  apply colvec_concat_eq.
  - apply Haf1_value.
  - apply Haf2_value.
Qed.

Definition concat_affine_segments
  {in_dim1 in_dim2 out_dim1 out_dim2: nat}  
  (el1: AffineSegment in_dim1 out_dim1)
  (el2: AffineSegment in_dim2 out_dim2)
  : AffineSegment (RSOPM:=RSOPM) (in_dim1 + in_dim2) (out_dim1 + out_dim2) 
  := 
  match el1, el2 with 
  | Segment p1 af1, Segment p2 af2 =>
      Segment _ _ (concat_polyhedra p1 p2) (concat_affine_functions af1 af2)
  end.

Lemma concat_affine_segments_domain:
  forall in_dim1 in_dim2 out_dim1 out_dim2 x1 x2
    (el1: AffineSegment in_dim1 out_dim1)
    (el2: AffineSegment in_dim2 out_dim2),
    in_affine_segment_domain el1 x1 ->
    in_affine_segment_domain el2 x2 ->
    in_affine_segment_domain (concat_affine_segments el1 el2) (colvec_concat x1 x2).
Proof.
  intros in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 el1 el2 Hel1 Hel2.
  unfold in_affine_segment_domain.
  unfold concat_affine_segments.
  destruct el1 as [p1 af1].
  destruct el2 as [p2 af2].
  unfold in_affine_segment_domain in Hel1.
  unfold in_affine_segment_domain in Hel2.
  apply in_concat_polyhedra_inv.
  split; easy.
Qed.

Lemma concat_affine_segments_value:
  forall in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 el1_x1 el2_x2
    (el1: AffineSegment in_dim1 out_dim1)
    (el2: AffineSegment in_dim2 out_dim2),
    is_affine_segment_value el1 x1 el1_x1 ->
    is_affine_segment_value el2 x2 el2_x2 ->
    is_affine_segment_value (concat_affine_segments el1 el2) (colvec_concat x1 x2) (colvec_concat el1_x1 el2_x2).
Proof.
  intros in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 el1_x1 el2_x2 el1 el2 Hel1_value Hel2_value.
  unfold is_affine_segment_value.
  unfold is_affine_segment_value in Hel1_value.
  unfold is_affine_segment_value in Hel2_value.
  destruct Hel1_value as [Hel1_domain Hel1_value].
  destruct Hel2_value as [Hel2_domain Hel2_value].
  split.
  - apply concat_affine_segments_domain; easy.
  - destruct el1 as [p1 f_el1].
    destruct el2 as [p2 f_el2].
    unfold concat_affine_segments.
    unfold is_affine_f_value.
    apply concat_affine_functions_value.
    apply Hel1_value.
    apply Hel2_value.
Qed.

Definition pwaf_concat_body  
  {in_dim1 in_dim2 out_dim1 out_dim2: nat} 
  (f: PWAF (in_dim:=in_dim1) (out_dim:=out_dim1))
  (g: PWAF (in_dim:=in_dim2) (out_dim:=out_dim2)):  
    list (AffineSegment (in_dim1 + in_dim2) (out_dim1 + out_dim2))
  :=
  map (fun els => 
        match els with 
        | (seg_f, seg_g) => concat_affine_segments seg_f seg_g
        end)
    (list_prod (body f) (body g)).

Lemma pwaf_concat_body_inv:
    forall in_dim1 out_dim1 in_dim2 out_dim2 seg_f seg_g 
      (f: PWAF (in_dim:=in_dim1) (out_dim:=out_dim1)) 
      (g: PWAF (in_dim:=in_dim2) (out_dim:=out_dim2)),
        In seg_f (body f) -> In seg_g (body g) ->
        In (concat_affine_segments seg_f seg_g) (pwaf_concat_body f g).
Proof.
    intros in_dim1 out_dim1 in_dim2 out_dim2 seg_f seg_g f g.
    intros Hbody_f Hbody_g.
    unfold pwaf_concat_body.
    apply in_map_iff.
    exists (seg_f, seg_g).
    split. reflexivity.
    apply in_prod_iff.
    split. apply Hbody_f. apply Hbody_g.
Qed.

Lemma pwaf_concat_body_inverse:
    forall in_dim1 out_dim1 in_dim2 out_dim2 seg_fg
        (f: PWAF (in_dim:=in_dim1) (out_dim:=out_dim1)) 
        (g: PWAF (in_dim:=in_dim2) (out_dim:=out_dim2)),
        In seg_fg (pwaf_concat_body f g) ->
        exists seg_f seg_g,
            In seg_f (body f) /\
            In seg_g (body g) /\
            seg_fg = concat_affine_segments seg_f seg_g.
Proof.
    intros in_dim1 out_dim1 in_dim2 out_dim2 seg_fg f g HIn.
    unfold pwaf_concat_body in HIn.
    apply in_map_iff in HIn.
    destruct HIn as [x HIn].
    destruct HIn as [Hx HIn].
    induction x as [body_seg_f body_seg_g].
    apply in_prod_iff in HIn.
    destruct HIn as [HInf HIng].
    exists body_seg_f. exists body_seg_g.
    split. apply HInf.
    split. apply HIng.
    symmetry. apply Hx.
Qed.

Theorem pwaf_concat_univalence
    {in_dim1 in_dim2 out_dim1 out_dim2: nat} 
    (f: PWAF (in_dim:=in_dim1) (out_dim:=out_dim1))
    (g: PWAF (in_dim:=in_dim2) (out_dim:=out_dim2)):
    pwaf_univalence (pwaf_concat_body f g).
Proof.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b HaIn HbIn x HxIntersect.
    pose proof pwaf_concat_body_inverse as H1.
    pose proof pwaf_concat_body_inverse as H2.
    specialize (H1 in_dim1 out_dim1 in_dim2 out_dim2).
    specialize (H2 in_dim1 out_dim1 in_dim2 out_dim2).
    specialize (H1 a f g HaIn).
    specialize (H2 b f g HbIn).
    destruct H1 as [seg_f_1 H1].
    destruct H1 as [seg_g_1 H1].
    destruct H1 as [HIn_body_seg_f_1 H1].
    destruct H1 as [HIn_body_seg_g_1 H1].
    destruct H2 as [seg_f_2 H2].
    destruct H2 as [seg_g_2 H2].
    destruct H2 as [HIn_body_seg_f_2 H2].
    destruct H2 as [HIn_body_seg_g_2 H2].
    destruct a as [p_fg1 af_fg1].
    destruct b as [p_fg2 af_fg2].
    destruct af_fg1 as [M_fg1 b_fg1].
    destruct af_fg2 as [M_fg2 b_fg2].
    unfold affine_segment_eval.
    unfold affine_f_eval.
    pose proof (colvec_split (RSOPM:=RSOPM)) as Hx.
    specialize (Hx _ _ x).
    destruct Hx as [x1 Hx].
    destruct Hx as [x2 Hx].
    destruct Hx as [Hx1def Hx].
    destruct Hx as [Hx2def Hx].
    rewrite Hx.
    unfold concat_affine_segments in H1.
    destruct seg_f_1 as [p_f_1 af_f_1].
    destruct seg_g_1 as [p_g_1 af_g_1].
    inversion H1.
    unfold concat_affine_functions in H3.
    destruct af_f_1 as [M_f_1 b_f_1].
    destruct af_g_1 as [M_g_1 b_g_1].
    inversion H3.
    unfold concat_affine_segments in H2.
    destruct seg_f_2 as [p_f_2 af_f_2].
    destruct seg_g_2 as [p_g_2 af_g_2].
    inversion H2.
    unfold concat_affine_functions in H7.
    destruct af_f_2 as [M_f_2 b_f_2].
    destruct af_g_2 as [M_g_2 b_g_2].
    inversion H7.
    repeat rewrite MMmult_block_diag_matrix. 
    repeat rewrite Mplus_colvec_concat.
    unfold in_affine_segment_domain in HxIntersect.
    rewrite H0 in HxIntersect.
    rewrite H6 in HxIntersect.
    destruct HxIntersect as [HxIn1 HxIn2].
    rewrite Hx in HxIn1.
    rewrite Hx in HxIn2.
    apply polyhedron_eval_correct in HxIn1.
    rewrite HxIn1.
    apply polyhedron_eval_correct in HxIn2.
    rewrite HxIn2.
    apply polyhedron_eval_correct in HxIn1.
    apply polyhedron_eval_correct in HxIn2.
    f_equal.
    apply in_concat_polyhedra_inv in HxIn1.
    apply in_concat_polyhedra_inv in HxIn2.
    destruct HxIn1 as [Hx1_p_f_1 Hx2_p_g_1].
    destruct HxIn2 as [Hx1_p_f_2 Hx2_p_g_2].
    apply colvec_concat_eq.
    * induction f as [body_f Hpwaf_f].
      pose proof Hpwaf_f as Hpwaf_f_cp.
      unfold pwaf_univalence in Hpwaf_f_cp.
      unfold ForallPairs in Hpwaf_f_cp.
      specialize (Hpwaf_f_cp 
        (Segment _ _ p_f_1 (Affine _ _ M_f_1 b_f_1)) 
        (Segment _ _ p_f_2 (Affine _ _ M_f_2 b_f_2))).
      specialize (Hpwaf_f_cp HIn_body_seg_f_1 HIn_body_seg_f_2).
      specialize (Hpwaf_f_cp x1); simpl in Hpwaf_f_cp.
      assert (Hhelp: in_convex_polyhedron x1 p_f_1 /\ 
                     in_convex_polyhedron x1 p_f_2 ). auto.
      specialize (Hpwaf_f_cp Hhelp).
      apply polyhedron_eval_correct in Hx1_p_f_1.
      apply polyhedron_eval_correct in Hx1_p_f_2.
      rewrite Hx1_p_f_1 in Hpwaf_f_cp.
      rewrite Hx1_p_f_2 in Hpwaf_f_cp.
      inversion Hpwaf_f_cp.
      reflexivity.
    * induction g as [body_g Hpwaf_g].
      pose proof Hpwaf_g as Hpwaf_g_cp.
      unfold pwaf_univalence in Hpwaf_g_cp.
      unfold ForallPairs in Hpwaf_g_cp.
      specialize (Hpwaf_g_cp 
          (Segment _ _ p_g_1 (Affine _ _ M_g_1 b_g_1)) 
          (Segment _ _ p_g_2 (Affine _ _ M_g_2 b_g_2))).
      specialize (Hpwaf_g_cp HIn_body_seg_g_1 HIn_body_seg_g_2).
      specialize (Hpwaf_g_cp x2); simpl in Hpwaf_g_cp.
      assert (Hhelp: in_convex_polyhedron x2 p_g_1 /\ 
                     in_convex_polyhedron x2 p_g_2 ). auto.
      specialize (Hpwaf_g_cp Hhelp).
      apply polyhedron_eval_correct in Hx2_p_g_1.
      apply polyhedron_eval_correct in Hx2_p_g_2.
      rewrite Hx2_p_g_1 in Hpwaf_g_cp.
      rewrite Hx2_p_g_2 in Hpwaf_g_cp.
      inversion Hpwaf_g_cp.
      reflexivity.
Qed.

Definition pwaf_concat
    {in_dim1 in_dim2 out_dim1 out_dim2: nat} 
    (f: PWAF (in_dim:=in_dim1) (out_dim:=out_dim1))
    (g: PWAF (in_dim:=in_dim2) (out_dim:=out_dim2))
    : PWAF (in_dim:=in_dim1 + in_dim2) (out_dim := out_dim1 + out_dim2)
    :=
    mkPLF (in_dim1 + in_dim2) (out_dim1 + out_dim2) (pwaf_concat_body f g) 
        (pwaf_concat_univalence f g).

Theorem pwaf_concat_correct:
    forall in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 f_x1 g_x2 
      (f: PWAF (in_dim:=in_dim1) (out_dim:=out_dim1)) 
      (g: PWAF (in_dim:=in_dim2) (out_dim:=out_dim2)),
      is_pwaf_value f x1 f_x1 -> is_pwaf_value g x2 g_x2 ->
      let fg   := pwaf_concat f g in
      let x    := colvec_concat x1 x2 in
      let fg_x := colvec_concat f_x1 g_x2 in
      is_pwaf_value fg x fg_x.
Proof.
    intros in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 f_x1 g_x2 f g.
    intros Hvalue_f Hvalue_g fg x fg_x.
    unfold is_pwaf_value.
    unfold is_pwaf_value in Hvalue_f.
    unfold is_pwaf_value in Hvalue_g.
    destruct Hvalue_f as [body_seg_f Hbody_seg_f].
    destruct Hvalue_g as [body_seg_g Hbody_seg_g].
    exists (concat_affine_segments body_seg_f body_seg_g).
    split.
    - apply pwaf_concat_body_inv.
      apply Hbody_seg_f.
      apply Hbody_seg_g.
    - unfold fg_x.
      unfold x.
      apply concat_affine_segments_value.
      apply Hbody_seg_f.
      apply Hbody_seg_g.
Qed.

End PWAFConcatenation.

(*-----------------------------------------------------------------------------------------*)

Section PWAFComposition.

Context { RSOPM : RealSubsetOPM }.
Open Scope RSOPM_scope.

Definition affine_f_polyhedron_preimage
    {in_dim out_dim: nat}
    (af: AffineFunction in_dim out_dim)
    (p: ConvexPolyhedron out_dim)
    : ConvexPolyhedron in_dim :=
    match af, p with
    | Affine M_af b_af, Polyhedron lc => 
        let lc_new := 
          map (fun constraint => 
                match constraint with
                  Constraint c b => Constraint in_dim 
                    (transpose (Mmult (T:=RSOPM) (transpose c) M_af)) (b + (- (c * b_af)%v))
                end) lc
        in Polyhedron _ lc_new
    end. 

Lemma in_affine_f_polyhedron_preimage:
  forall in_dim out_dim x p (af: AffineFunction in_dim out_dim),
    in_convex_polyhedron x (affine_f_polyhedron_preimage af p) ->
    in_convex_polyhedron (affine_f_eval af x) p.
Proof.
  intros in_dim out_dim x p af Hp.
  unfold in_convex_polyhedron.
  destruct p as [lcs].
  intros lc Hinlc.
  unfold affine_f_polyhedron_preimage in Hp.
  destruct af as [M_af b_af].
  unfold in_convex_polyhedron in Hp.
  destruct lc as [c_lc b_lc].
  specialize (Hp (Constraint _ (transpose 
                                  (Mmult (T:=RSOPM) (transpose c_lc) M_af)%M) 
                                (b_lc + - (c_lc * b_af)%v))).
  unfold satisfies_lc in Hp.
  unfold affine_f_eval.
  unfold satisfies_lc.
  unfold dot in Hp.
  rewrite transpose_transpose in Hp.
  unfold dot.
  rewrite Mmult_distr_l.
  rewrite <- coeff_mat_00_Mplus.
  apply RSOPM_le_opp_plus_r.
  rewrite Mmult_assoc.
  apply Hp.
  apply in_map_iff.
  exists (Constraint _ c_lc b_lc).
  split.
  - reflexivity.
  - apply Hinlc. 
Qed.

Lemma in_affine_f_polyhedron_preimage_reverse:
  forall in_dim out_dim x p (af: AffineFunction in_dim out_dim),
    in_convex_polyhedron (affine_f_eval af x) p ->
    in_convex_polyhedron x (affine_f_polyhedron_preimage af p).
Proof.
  intros in_dim out_dim x p af Hp.
  unfold in_convex_polyhedron.
  unfold affine_f_polyhedron_preimage.
  destruct af as [M_af b_af].
  destruct p as [lc].
  intros constraint HConstraint.
  induction lc.
  * simpl in HConstraint. contradiction.
  * apply in_map_iff in HConstraint.
    destruct HConstraint as [constraint_x HConstraint].
    destruct HConstraint as [HConstraint HIn].
    apply in_inv in HIn.
    destruct HIn as [HIn|HIn].
    - rewrite <- HConstraint.
      unfold in_convex_polyhedron in Hp.
      specialize (Hp constraint_x).
      pose proof in_eq as Hin_eq_cx.
      specialize (Hin_eq_cx _ a lc).
      rewrite HIn in Hin_eq_cx at 1.
      specialize (Hp Hin_eq_cx).
      destruct constraint_x as [c_cx b_cx].
      unfold satisfies_lc.
      unfold satisfies_lc in Hp.
      unfold affine_f_eval in Hp.
      apply RSOPM_le_plus_opp_r.
      unfold dot in Hp.
      rewrite Mmult_distr_l in Hp.
      unfold dot. rewrite transpose_transpose.
      rewrite Mmult_assoc in Hp.
      rewrite coeff_mat_00_Mplus.
      apply Hp.
    - apply IHlc.
      * apply (in_convex_polyhedron_remove_constraint _ a).
        apply Hp. 
      * apply in_map_iff.
        exists constraint_x.
        split. apply HConstraint. apply HIn. 
Qed.

Definition compose_affine_functions 
    {in_dim hidden_dim out_dim: nat} 
    (af_f: AffineFunction hidden_dim out_dim)
    (af_g: AffineFunction in_dim hidden_dim)
    : AffineFunction in_dim out_dim
    :=
    match af_f, af_g with
    | Affine M_f b_f, Affine M_g b_g =>
        Affine (RSOPM:=RSOPM) in_dim out_dim (Mmult (T:=RSOPM) M_f M_g) ((Mmult (T:=RSOPM) M_f b_g) + b_f)%M
    end.

Lemma compose_affine_functions_correct:
    forall in_dim hidden_dim out_dim x
      (af_f: AffineFunction hidden_dim out_dim)
      (af_g: AffineFunction in_dim hidden_dim),
      is_affine_f_value (compose_affine_functions af_f af_g) x (affine_f_eval af_f (affine_f_eval af_g x)).
Proof.
    intros in_dim hidden_dim out_dim x af_f af_g.
    destruct af_f as [M_f b_f].
    destruct af_g as [M_g b_g].
    unfold is_affine_f_value.
    unfold compose_affine_functions.
    unfold affine_f_eval.
    rewrite Mmult_distr_l.
    rewrite <- Mplus_assoc.
    rewrite <- Mmult_assoc.
    reflexivity.
Qed.

Lemma compose_affine_functions_reverse_f:
  forall in_dim hid_dim out_dim x g_x fg_x
    (af_f: AffineFunction (RSOPM:=RSOPM) hid_dim out_dim)
    (af_g: AffineFunction (RSOPM:=RSOPM) in_dim hid_dim),
    is_affine_f_value (compose_affine_functions af_f af_g) x fg_x ->
    is_affine_f_value af_g x g_x ->
    is_affine_f_value af_f g_x fg_x.  
Proof.
  intros in_dim hid_dim out_dim x g_x fg_x af_f af_g Hfg Hg.
  destruct af_g as [M_g b_g].
  destruct af_f as [M_f b_f].
  unfold is_affine_f_value.
  unfold is_affine_f_value in Hg.
  unfold is_affine_f_value in Hfg.
  unfold compose_affine_functions in Hfg.
  rewrite <- Hfg.
  rewrite <- Hg.
  rewrite Mmult_distr_l.
  rewrite Mmult_assoc.
  rewrite Mplus_assoc.
  reflexivity.
Qed.
  
Definition compose_affine_segments
    {in_dim hidden_dim out_dim: nat} 
    (seg_f: AffineSegment hidden_dim out_dim)
    (seg_g: AffineSegment in_dim hidden_dim)
    : AffineSegment in_dim out_dim
    :=
    match seg_f, seg_g with
    | Segment p_f af_f, Segment p_g af_g =>
        Segment in_dim out_dim 
          (polyhedra_intersect p_g (affine_f_polyhedron_preimage af_g p_f)) 
          (compose_affine_functions af_f af_g)
    end.    

Lemma compose_affine_segments_in_domain_g:
  forall in_dim hidden_dim out_dim x
    (seg_f: AffineSegment hidden_dim out_dim)
    (seg_g: AffineSegment in_dim hidden_dim),  
    in_affine_segment_domain (compose_affine_segments seg_f seg_g) x ->
    in_affine_segment_domain seg_g x.
Proof.
  intros in_dim hidden_dim out_dim x seg_f seg_g H.
  unfold compose_affine_segments in H.
  destruct seg_f as [p_f af_f].
  destruct seg_g as [p_g af_g].
  unfold in_affine_segment_domain.
  unfold in_affine_segment_domain in H.
  apply in_polyhedra_intersect1 in H.
  apply H.
Qed.

Lemma compose_affine_segments_in_domain_f:
  forall in_dim hidden_dim out_dim x g_x
    (seg_f: AffineSegment hidden_dim out_dim)
    (seg_g: AffineSegment in_dim hidden_dim),  
    in_affine_segment_domain (compose_affine_segments seg_f seg_g) x ->
    is_affine_segment_value seg_g x g_x ->
    in_affine_segment_domain seg_f g_x.
Proof.
  intros in_dim hidden_dim out_dim x g_x seg_f seg_g Hdomain Heval.
  unfold compose_affine_segments in Hdomain.
  destruct seg_f as [p_f af_f].
  destruct seg_g as [p_g af_g].
  unfold in_affine_segment_domain in Hdomain.
  apply in_polyhedra_intersect2 in Hdomain.
  unfold is_affine_segment_value in Heval.
  destruct Heval as [Hxdom Hvalue].
  unfold in_affine_segment_domain.
  apply affine_f_eval_correct in Hvalue.
  rewrite <- Hvalue.
  apply in_affine_f_polyhedron_preimage.
  apply Hdomain.
Qed.

Lemma compose_affine_segments_in_domain:
  forall in_dim hidden_dim out_dim x g_x
    (seg_f: AffineSegment hidden_dim out_dim)
    (seg_g: AffineSegment in_dim hidden_dim),  
    is_affine_segment_value seg_g x g_x ->
    in_affine_segment_domain seg_f g_x ->
    in_affine_segment_domain (compose_affine_segments seg_f seg_g) x.
Proof.
  intros in_dim hidden_dim out_dim x g_x seg_f seg_g Hg_x Hf_x.
  destruct seg_g as [p_g af_g].
  destruct seg_f as [p_f af_f].
  unfold is_affine_segment_value in Hg_x.
  destruct Hg_x as [Hx_dom Hg_x].
  unfold is_affine_segment_value in Hf_x.
  unfold in_affine_segment_domain.
  unfold compose_affine_segments.
  unfold in_affine_segment_domain in Hx_dom.
  unfold in_affine_segment_domain in Hf_x.
  apply polyhedra_intersect_correct; split.
  - apply Hx_dom.
  - apply in_affine_f_polyhedron_preimage_reverse.
    apply affine_f_eval_correct in Hg_x.
    rewrite <- Hg_x in Hf_x.
    apply Hf_x.  
Qed.

Lemma is_compose_affine_segments_value:
  forall in_dim hidden_dim out_dim x g_x f_x
    (seg_f: AffineSegment hidden_dim out_dim)
    (seg_g: AffineSegment in_dim hidden_dim),
    is_affine_segment_value seg_g x g_x ->
    is_affine_segment_value seg_f g_x f_x ->
    is_affine_segment_value (compose_affine_segments seg_f seg_g) x f_x.
Proof.
  intros in_dim hidden_dim out_dim x g_x f_x seg_f seg_g Hg_x Hf_x.
  destruct seg_g as [p_g af_g].
  destruct seg_f as [p_f af_f].
  unfold is_affine_segment_value in Hg_x.
  destruct Hg_x as [Hx_dom Hg_x].
  unfold is_affine_segment_value in Hf_x.
  destruct Hf_x as [Hg_xdom Hf_x].
  unfold is_affine_segment_value.
  split.
  * unfold in_affine_segment_domain.
    unfold compose_affine_segments.
    unfold in_affine_segment_domain in Hx_dom.
    unfold in_affine_segment_domain in Hg_xdom.
    apply polyhedra_intersect_correct; split.
    - apply Hx_dom.
    - apply in_affine_f_polyhedron_preimage_reverse.
      apply affine_f_eval_correct in Hg_x.
      rewrite <- Hg_x in Hg_xdom.
      apply Hg_xdom.
  * unfold compose_affine_segments.
    apply affine_f_eval_correct in Hf_x.
    rewrite <- Hf_x.
    apply affine_f_eval_correct in Hg_x.
    rewrite <- Hg_x.
    apply compose_affine_functions_correct.
Qed.

Lemma compose_affine_segments_eval_in_domain:
  forall in_dim hidden_dim out_dim x
    (seg_f: AffineSegment hidden_dim out_dim)
    (seg_g: AffineSegment in_dim hidden_dim),
      in_affine_segment_domain (compose_affine_segments seg_f seg_g) x ->
      affine_segment_eval (compose_affine_segments seg_f seg_g) x =
      match affine_segment_eval seg_g x with
      | None => None
      | Some g_x => affine_segment_eval seg_f g_x
      end.
Proof.
  intros in_dim hidden_dim out_dim x seg_f seg_g Hdomain.
  remember (affine_segment_eval seg_g x) as g_x.
  destruct g_x as [g_x|].
  * remember (affine_segment_eval seg_f g_x) as f_x.
    destruct f_x as [f_x|].
    - symmetry in Heqg_x; apply affine_segment_eval_correct in Heqg_x.
      symmetry in Heqf_x; apply affine_segment_eval_correct in Heqf_x.
      apply affine_segment_eval_correct.
      apply (is_compose_affine_segments_value _ _ _ _ g_x); easy.
    - apply (compose_affine_segments_in_domain_f _ _ _ _ g_x) in Hdomain.
      apply affine_seg_in_domain_has_value in Hdomain.
      destruct Hdomain as [fg_x Hvalue].
      apply affine_segment_eval_correct in Hvalue.
      rewrite Hvalue in Heqf_x.
      discriminate.
      apply affine_segment_eval_correct; easy.
  * apply compose_affine_segments_in_domain_g in Hdomain.
    apply affine_seg_in_domain_has_value in Hdomain.
    destruct Hdomain as [g_x Hvalue].
    apply affine_segment_eval_correct in Hvalue.
    rewrite Hvalue in Heqg_x.
    discriminate.
Qed.

Lemma compose_affine_segments_value_reverse_f:
  forall in_dim hid_dim out_dim x g_x f_x
    (seg_f: AffineSegment (RSOPM:=RSOPM) hid_dim out_dim)
    (seg_g: AffineSegment (RSOPM:=RSOPM) in_dim hid_dim),
    is_affine_segment_value (compose_affine_segments seg_f seg_g) x f_x ->
    is_affine_segment_value seg_g x g_x ->
    is_affine_segment_value seg_f g_x f_x.
Proof.
  intros in_dim hid_dim out_dim x g_x f_x seg_f seg_g Hfg Hg.
  unfold compose_affine_segments in Hfg.
  destruct seg_f as [p_f af_f].
  destruct seg_g as [p_g af_g].
  unfold is_affine_segment_value in Hfg.
  unfold is_affine_segment_value in Hg.
  destruct Hfg as [Hdom_fg Hval_fg].
  destruct Hg as [Hdom_g Hval_g].
  unfold is_affine_segment_value; split.
  * apply (compose_affine_segments_in_domain_f in_dim hid_dim out_dim x g_x (Segment _ _ p_f af_f) (Segment _ _ p_g af_g)).
    - apply Hdom_fg.
    - unfold is_affine_segment_value; split.
      * apply Hdom_g.
      * apply Hval_g.
  * apply (compose_affine_functions_reverse_f in_dim hid_dim out_dim x _ _ _ af_g).
    - apply Hval_fg.
    - apply Hval_g.   
Qed.

Definition pwaf_compose_body  
    {in_dim hidden_dim out_dim: nat} 
    (f: PWAF (in_dim:=hidden_dim) (out_dim:=out_dim))
    (g: PWAF (in_dim:=in_dim) (out_dim:=hidden_dim)):  
    list (AffineSegment in_dim out_dim)
    :=
    map (
        fun pair =>
            match pair with 
            | (body_seg_f, body_seg_g) => 
                  compose_affine_segments body_seg_f body_seg_g
            end
    ) (list_prod (body f) (body g)).

Theorem pwaf_compose_univalence
    {in_dim hidden_dim out_dim: nat} 
    (f: PWAF (in_dim:=hidden_dim) (out_dim:=out_dim))
    (g: PWAF (in_dim:=in_dim) (out_dim:=hidden_dim)):
    pwaf_univalence (pwaf_compose_body f g).
Proof.
    destruct f as [body_f ax_f]. 
    destruct g as [body_g ax_g].
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros body_seg_13 body_seg_24.
    intros HIn_seg_13 HIn_seg_24 x HIndomain.
    unfold pwaf_compose_body in HIn_seg_13.
    unfold pwaf_compose_body in HIn_seg_24.
    apply in_map_iff in HIn_seg_13.
    apply in_map_iff in HIn_seg_24.
    destruct HIn_seg_13 as [pair13_exists HInp13].
    destruct HIn_seg_24 as [pair24_exists HInp24].
    destruct pair13_exists as [body_seg_f3 body_seg_g1].
    destruct pair24_exists as [body_seg_f4 body_seg_g2].
    destruct HInp13 as [H13_def H1and3In].
    destruct HInp24 as [H24_def H2and4In].
    apply in_prod_iff in H1and3In.
    apply in_prod_iff in H2and4In.                
    destruct H1and3In as [HIn_seg_3 HIn_seg_1].
    destruct H2and4In as [HIn_seg_4 HIn_seg_2].
    rewrite <- H13_def.
    rewrite <- H24_def.
    destruct HIndomain as [Hx_dom13 Hx_dom24].
    rewrite <- H13_def in Hx_dom13.
    rewrite <- H24_def in Hx_dom24.
    rewrite compose_affine_segments_eval_in_domain; try apply Hx_dom13.
    rewrite compose_affine_segments_eval_in_domain; try apply Hx_dom24.
    unfold pwaf_univalence in ax_g.
    unfold pwaf_univalence in ax_f.
    unfold ForallPairs in ax_g.
    unfold ForallPairs in ax_f.
    rewrite (ax_g body_seg_g1 body_seg_g2); try easy.
    remember (affine_segment_eval body_seg_g2 x) as g_x.
    destruct g_x as [g_x|]; try reflexivity.
    remember (affine_segment_eval body_seg_f4 g_x) as f_g_x.
    destruct f_g_x as [f_g_x|]; try reflexivity.
    rewrite (ax_f body_seg_f3 body_seg_f4); try easy.
    * split.
      - apply (compose_affine_segments_in_domain_f _ _ _ x g_x _ body_seg_g1).
        * apply Hx_dom13.
        * apply affine_segment_eval_correct.
          rewrite (ax_g body_seg_g1 body_seg_g2); try easy.
          - split.
            * apply compose_affine_segments_in_domain_g in Hx_dom13.
              apply Hx_dom13.
            * apply compose_affine_segments_in_domain_g in Hx_dom24.
              apply Hx_dom24.
      - symmetry in Heqf_g_x.
        apply affine_segment_eval_correct in Heqf_g_x.
        unfold is_affine_segment_value in Heqf_g_x.
        apply Heqf_g_x.
    * apply (compose_affine_segments_in_domain_f _ _ _ _ g_x) in Hx_dom24.
      apply affine_seg_in_domain_has_value in Hx_dom24.
      destruct Hx_dom24 as [f_x Hx_value].
      apply affine_segment_eval_correct in Hx_value.
      rewrite Hx_value in Heqf_g_x.
      discriminate Heqf_g_x.
      apply affine_segment_eval_correct.
      symmetry; apply Heqg_x.
    * split.
      - apply compose_affine_segments_in_domain_g in Hx_dom13.
        apply Hx_dom13.
      - apply compose_affine_segments_in_domain_g in Hx_dom24.
        apply Hx_dom24.
Qed.

Definition pwaf_compose
    {in_dim hidden_dim out_dim: nat} 
    (f: PWAF (in_dim:=hidden_dim) (out_dim:=out_dim))
    (g: PWAF (in_dim:=in_dim) (out_dim:=hidden_dim))
    : PWAF 
    :=
    mkPLF in_dim out_dim (pwaf_compose_body f g) (pwaf_compose_univalence f g).

Theorem pwaf_compose_correct:
  forall in_dim hid_dim out_dim x f_x g_x 
      (f: PWAF (in_dim:=hid_dim) (out_dim:=out_dim)) 
      (g: PWAF (in_dim:=in_dim) (out_dim:=hid_dim)),
      is_pwaf_value g x g_x ->
      is_pwaf_value f g_x f_x ->
      is_pwaf_value (pwaf_compose f g) x f_x.
Proof.
    intros in_dim hid_dim out_dim x f_x g_x f g Hval_g Hval_f.
    unfold is_pwaf_value.
    unfold is_pwaf_value in Hval_g.
    unfold is_pwaf_value in Hval_f.
    destruct Hval_g as [body_seg_g Hbody_seg_g].
    destruct Hval_f as [body_seg_f Hbody_seg_f].
    destruct Hbody_seg_g as [Hseg_gIn Hvalseg_g].
    destruct Hbody_seg_f as [Hseg_fIn Hvalseg_f].
    exists (compose_affine_segments body_seg_f body_seg_g).
    split.
    * unfold pwaf_compose; simpl.
      unfold pwaf_compose_body.
      apply in_map_iff.
      exists ((body_seg_f, body_seg_g)).
      split.
      - reflexivity.
      - apply in_prod_iff.
        split; easy. 
    * apply (is_compose_affine_segments_value _ _ _ _ g_x); easy.
Qed.
    
End PWAFComposition.

(*-----------------------------------------------------------------------------------------*)

Section TPWAFOperations.

Context { RSOPM : RealSubsetOPM }.
Open Scope RSOPM_scope.

Theorem pwaf_concat_total:
  forall in_dim1 in_dim2 out_dim1 out_dim2
    (f: TPWAF (in_dim:=in_dim1) (out_dim:=out_dim1)) 
    (g: TPWAF (in_dim:=in_dim2) (out_dim:=out_dim2)),
    is_total (RSOPM:=RSOPM) (pwaf_concat f g).
Proof.
  intros in_dim1 in_dim2 out_dim1 out_dim2 f g.
  unfold is_total.
  intros x.
  unfold in_pwaf_domain.
  destruct f as [f Hftotal].
  destruct g as [g Hgtotal].
  pose proof Hftotal as Hftotal_cp.
  pose proof Hgtotal as Hgtotal_cp.
  unfold is_total in Hftotal_cp.
  unfold is_total in Hgtotal_cp.
  pose proof (colvec_split (RSOPM:=RSOPM) in_dim1 in_dim2 x) as Hsplit.
  destruct Hsplit as [x1 Hsplit].
  destruct Hsplit as [x2 Hsplit].
  destruct Hsplit as [Hx1 Hsplit].
  destruct Hsplit as [Hx2 Hsplit].
  specialize (Hftotal_cp x1).
  specialize (Hgtotal_cp x2).
  unfold in_pwaf_domain in Hftotal_cp.
  unfold in_pwaf_domain in Hgtotal_cp.
  destruct Hftotal_cp as [body_seg_f Hbody_seg_f].
  destruct Hgtotal_cp as [body_seg_g Hbody_seg_g].
  destruct Hbody_seg_f as [HfIn Hfdomain].
  destruct Hbody_seg_g as [HgIn Hgdomain].
  exists (concat_affine_segments body_seg_f body_seg_g).
  split.
  * apply pwaf_concat_body_inv.
    - apply HfIn. 
    - apply HgIn.
  * rewrite Hsplit.
    apply concat_affine_segments_domain.
    - apply Hfdomain.
    - apply Hgdomain.
Qed.

Definition tpwaf_concat
  {in_dim1 in_dim2 out_dim1 out_dim2: nat} 
  (f: TPWAF (in_dim:=in_dim1) (out_dim:=out_dim1))
  (g: TPWAF (in_dim:=in_dim2) (out_dim:=out_dim2))
  : TPWAF (in_dim:=in_dim1 + in_dim2) (out_dim := out_dim1 + out_dim2)
  :=
  exist _ (pwaf_concat f g) (pwaf_concat_total _ _ _ _ _ _).

Theorem tpwaf_concat_correct:
  forall in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 f_x1 g_x2 
    (f: TPWAF (in_dim:=in_dim1) (out_dim:=out_dim1)) 
    (g: TPWAF (in_dim:=in_dim2) (out_dim:=out_dim2)),
    is_pwaf_value f x1 f_x1 -> is_pwaf_value g x2 g_x2 ->
    is_pwaf_value (tpwaf_concat f g) (colvec_concat x1 x2) (colvec_concat f_x1 g_x2).
Proof.
  intros in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 f_x1 g_x2 f g Hvalf Hvalg.
  unfold tpwaf_concat.
  apply pwaf_concat_correct; easy.
Qed.

Theorem pwaf_compose_total:
  forall in_dim hid_dim out_dim
    (f: TPWAF (in_dim:=hid_dim) (out_dim:=out_dim)) 
    (g: TPWAF (in_dim:=in_dim) (out_dim:=hid_dim)),
    is_total (RSOPM:=RSOPM) (pwaf_compose f g).
Proof.
  intros in_dim hid_dim out_dim f g.
  unfold is_total.
  intros x.
  unfold in_pwaf_domain.
  destruct f as [f Hftotal].
  destruct g as [g Hgtotal].
  pose proof Hftotal as Hftotal_cp.
  pose proof Hgtotal as Hgtotal_cp.  
  unfold is_total in Hftotal_cp.
  unfold is_total in Hgtotal_cp.
  specialize (Hgtotal_cp x).
  unfold is_total in Hgtotal_cp.
  unfold in_pwaf_domain in Hgtotal_cp.
  destruct Hgtotal_cp as [body_seg_g Hbody_seg_g].
  destruct Hbody_seg_g as [HgIn Hgdomain].
  destruct body_seg_g as [p_g af_g].
  specialize (Hftotal_cp (affine_f_eval af_g x)).
  unfold in_pwaf_domain in Hftotal_cp.
  destruct Hftotal_cp as [body_seg_f Hbody_seg_f].
  destruct Hbody_seg_f as [HfIn Hfdomain].
  exists (compose_affine_segments body_seg_f (Segment _ _ p_g af_g)).
  split.
  * simpl. unfold pwaf_compose_body.
    apply in_map_iff.
    exists ((body_seg_f, Segment _ _ p_g af_g)).
    split; try easy.
    apply in_prod_iff.
    split; try easy.
  * apply (compose_affine_segments_in_domain _ _ _ x (affine_f_eval af_g x)).
    - unfold is_affine_segment_value.
      split.
      * apply Hgdomain.
      * apply affine_f_eval_correct; reflexivity.
    - apply Hfdomain.
Qed.  

Definition tpwaf_compose
  {in_dim hidden_dim out_dim: nat} 
  (f: TPWAF (in_dim:=hidden_dim) (out_dim:=out_dim))
  (g: TPWAF (in_dim:=in_dim) (out_dim:=hidden_dim))
  : TPWAF 
  :=
  exist _ (pwaf_compose f g) (pwaf_compose_total _ _ _ f g).

Theorem tpwaf_compose_correct:
  forall in_dim hid_dim out_dim x f_x
      (f: TPWAF (RSOPM:=RSOPM) (in_dim:=hid_dim) (out_dim:=out_dim)) 
      (g: TPWAF (RSOPM:=RSOPM) (in_dim:=in_dim) (out_dim:=hid_dim)),
      is_pwaf_value f (tpwaf_eval g x) f_x ->
      is_pwaf_value (tpwaf_compose f g) x f_x.
Proof.
  intros in_dim hid_dim out_dim x f_x f g H.
  unfold tpwaf_compose.
  apply (pwaf_compose_correct _ _ _ _ _ (tpwaf_eval g x)); try apply H.
  apply tpwaf_eval_correct.
Qed.
  
End TPWAFOperations.

(*-----------------------------------------------------------------------------------------*)

Section PWAFOperationsProperties.

Context { RSOPM : RealSubsetOPM }.
Open Scope RSOPM_scope.

Theorem pwaf_compose_reverse_value_f:
  forall in_dim hid_dim out_dim x g_x fg_x
    (f: PWAF (RSOPM:=RSOPM) (in_dim:=hid_dim) (out_dim:=out_dim)) 
    (g: PWAF (RSOPM:=RSOPM) (in_dim:=in_dim) (out_dim:=hid_dim)),
     is_pwaf_value (pwaf_compose f g) x fg_x ->
     is_pwaf_value g x g_x ->
     is_pwaf_value f g_x fg_x.
Proof.
  intros in_dim hid_dim out_dim x g_x fg_x f g Hval_fg Hval_g.
  unfold is_pwaf_value.
  unfold is_pwaf_value in Hval_fg.
  destruct Hval_fg as [body_seg_fg [Hseg_fg Hval_fg]].
  unfold pwaf_compose in Hseg_fg; simpl in Hseg_fg.
  unfold pwaf_compose_body in Hseg_fg.
  apply in_map_iff in Hseg_fg.
  destruct Hseg_fg as [body_x [Hcompose HIn_prod]].
  destruct body_x as [body_seg_f body_seg_g].
  apply in_prod_iff in HIn_prod.
  destruct HIn_prod as [Hseg_f Hseg_g].
  exists body_seg_f.
  split; first apply Hseg_f.
  rewrite <- Hcompose in Hval_fg.
  apply (compose_affine_segments_value_reverse_f in_dim hid_dim out_dim x g_x fg_x body_seg_f body_seg_g).
  - apply Hval_fg.
  - unfold is_pwaf_value in Hval_g.
    destruct Hval_g as [body_seg_g2 [HIn_elg2 Hval_elg2]].
    destruct g as [body_g ax_g].
    unfold pwaf_univalence in ax_g.
    unfold ForallPairs in ax_g.
    pose proof ax_g as ax_g_cp.
    specialize (ax_g_cp body_seg_g body_seg_g2 Hseg_g HIn_elg2 x).
    apply affine_segment_eval_correct.
    apply affine_segment_eval_correct in Hval_elg2.
    rewrite <- Hval_elg2.
    apply ax_g_cp.
    split.
    * unfold is_affine_segment_value in Hval_fg.
      destruct Hval_fg as [Hdom_fg Hval_fg].
      apply compose_affine_segments_in_domain_g in Hdom_fg.
      apply Hdom_fg.
    * apply affine_segment_eval_correct in Hval_elg2.
      unfold is_affine_segment_value in Hval_elg2.
      apply Hval_elg2.
Qed.

Theorem tpwaf_compose_reverse_value:
  forall in_dim hid_dim out_dim x fg_x
    (f: TPWAF (RSOPM:=RSOPM) (in_dim:=hid_dim) (out_dim:=out_dim)) 
    (g: TPWAF (RSOPM:=RSOPM) (in_dim:=in_dim) (out_dim:=hid_dim)),
        is_pwaf_value (tpwaf_compose f g) x fg_x ->
        is_pwaf_value g x (tpwaf_eval g x) /\ is_pwaf_value f (tpwaf_eval g x) fg_x.
Proof.
  intros in_dim hid_dim out_dim x fg_x f g H.
  split.
  * apply tpwaf_eval_correct.
  * apply (pwaf_compose_reverse_value_f in_dim hid_dim out_dim x _ _ f g).
    - apply H.
    - apply tpwaf_eval_correct. 
Qed.

End PWAFOperationsProperties.

