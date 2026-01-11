From Coq Require Import Reals List Arith Lia Lra.
From Coquelicot Require Import Coquelicot.
From Verinncoq Require Import real_subsets real_subsets_instances matrix_extensions.
Import MatrixNotations.
Import RealSubsetNotations.

Open Scope colvec_scope.
Open Scope matrix_scope.

Section Polehydra.

Context { RSOAM : RealSubsetOAM }.
Open Scope RSOAM_scope.

(** * Basic convex polyhedra theory

Convex polyhedron is a set that arises from a series of
linear constraints and describes set of solutions to
a linear inequalities system. We allow only non-strict
inequalities
*)

(** A linear constraint c * _ <= b *)
Inductive LinearConstraint (dim: nat) : Type :=
| Constraint (c: colvec (RSOAM:=RSOAM) dim) (b: T RSOAM).

(** 
A predicate that a certain point x satisfies a
linear constraint, meaning c*x <= b, where c and b
are from the definition of linear constraint
*)
Definition satisfies_lc {dim: nat} (x: colvec dim) (l: LinearConstraint dim): Prop :=
match l with
| Constraint c b => (c * x)%v <= b = true
end.    

(* Direct evaluation of linear constraint as a function *)
Definition lc_eval {dim: nat} (x: colvec dim) (l: LinearConstraint dim): bool :=
match l with
| Constraint c b => (c * x)%v <= b
end.    

Theorem lc_eval_correct:
    forall dim (x: colvec dim) l,
        (lc_eval x l = true <-> satisfies_lc x l).
Proof.
    intros dim x l.
    induction l.
    unfold lc_eval.
    unfold satisfies_lc.
    split; intro H; exact H.
Qed.

(** A convex polyhedron is described by a set of linear constraints *)
Inductive ConvexPolyhedron (dim: nat) : Type :=
| Polyhedron (constraints: list (LinearConstraint dim)).

(**
A predicate for membership inside of convex polyhedra
x is in the polyhedron <=> x satisfies all linear constraints of the polyherdron
*)
Definition in_convex_polyhedron {dim: nat} (x: colvec dim) (p: ConvexPolyhedron dim) :=
match p with
| Polyhedron lcs =>
    forall constraint, In constraint lcs ->
      satisfies_lc x constraint
end.

Lemma in_convex_polyhedron_remove_constraint:
  forall dim constraint lc (x: colvec (RSOAM:=RSOAM) dim),
    in_convex_polyhedron x (Polyhedron dim (constraint :: lc)) ->
    in_convex_polyhedron x (Polyhedron dim lc).
Proof.
  intros dim lc constraint x HIn.
  unfold in_convex_polyhedron in HIn.
  unfold in_convex_polyhedron.
  intros constraint0 HIn0.
  apply HIn.
  apply in_cons.
  apply HIn0.
Qed.

Fixpoint polyhedron_eval_helper {dim: nat} (l: list (LinearConstraint dim)) (x: colvec dim): bool :=
match l with
| nil => true
| lc :: next => andb (lc_eval x lc) (polyhedron_eval_helper next x)
end.

(**
Direct evaluation of polyhedron membership as a function into bool
*)
Definition polyhedron_eval {dim: nat} (x: colvec dim) (p: ConvexPolyhedron dim): bool :=
match p with
| Polyhedron constraints => polyhedron_eval_helper constraints x
end.

Theorem polyhedron_eval_correct:
    forall dim (x: colvec dim) p,
        polyhedron_eval x p = true <-> in_convex_polyhedron x p.
Proof.
    intros dim x p.
    induction p.
    unfold polyhedron_eval.
    induction constraints.
    * simpl. split. contradiction. reflexivity.
    split. unfold polyhedron_eval_helper. unfold in_convex_polyhedron.
    {
        intros H constraint HIn.
        unfold In in HIn.
        apply andb_prop in H. destruct H.
        destruct HIn.
        * rewrite <- H1. 
          apply lc_eval_correct in H.
          apply H.
        * unfold in_convex_polyhedron in IHconstraints.
          apply IHconstraints.
          apply H0. apply H1.   
    }
    {
        intros H.
        unfold polyhedron_eval_helper.
        apply andb_true_intro.
        split.
        * apply lc_eval_correct.
          unfold in_convex_polyhedron in H.
          apply H. compute. left. reflexivity.
        * apply IHconstraints.
          unfold in_convex_polyhedron.
          intros constraint HIn.
          unfold in_convex_polyhedron in H.
          apply H. unfold In. right. apply HIn.
    }
Qed.

(**
Construction of intersection of two polyhedra
*)
Definition polyhedra_intersect {dim: nat} (p1 p2: ConvexPolyhedron dim) :=
    match p1 with
    | Polyhedron l1 =>
        match p2 with 
        | Polyhedron l2 => 
            Polyhedron dim (l1 ++ l2)
        end
    end.

Theorem polyhedra_intersect_correct:
    forall dim (x: colvec dim) p1 p2,
        in_convex_polyhedron x p1 /\ in_convex_polyhedron x p2 ->
        in_convex_polyhedron x (polyhedra_intersect p1 p2).
Proof.
    intros dim x p1 p2 Hinboth.
    induction p1. induction p2.
    unfold in_convex_polyhedron.
    unfold polyhedra_intersect.
    intros constraint Hin.
    unfold in_convex_polyhedron in Hinboth.
    destruct Hinboth.
    specialize (H constraint).
    specialize (H0 constraint).
    apply in_app_or in Hin.
    destruct Hin.
    - apply (H H1).
    - apply (H0 H1).
Qed. 

Lemma in_polyhedra_intersect1:
  forall dim p1 p2 (x: colvec (RSOAM:=RSOAM) dim),
    in_convex_polyhedron x (polyhedra_intersect p1 p2) ->
    in_convex_polyhedron x p1.
Proof.
  intros dim p1 p2 x Hin.
  unfold in_convex_polyhedron.
  destruct p1 as [lcs1].
  intros constraint HInconstraint.
  unfold in_convex_polyhedron in Hin.
  unfold polyhedra_intersect in Hin.
  destruct p2 as [lcs2].
  specialize (Hin constraint).
  apply Hin.
  apply in_or_app.
  left; apply HInconstraint.
Qed.

Lemma in_polyhedra_intersect2:
  forall dim p1 p2 (x: colvec (RSOAM:=RSOAM) dim),
    in_convex_polyhedron x (polyhedra_intersect p1 p2) ->
    in_convex_polyhedron x p2.
Proof.
  intros dim p1 p2 x Hin.
  unfold in_convex_polyhedron.
  destruct p1 as [lcs1].
  destruct p2 as [lcs2].
  intros constraint HInconstraint.
  unfold in_convex_polyhedron in Hin.
  unfold polyhedra_intersect in Hin.
  specialize (Hin constraint).
  apply Hin.
  apply in_or_app.
  right; apply HInconstraint.
Qed.

End Polehydra.

(** * Constructive piecewise affine functions *)
Section PiecewiseLinear.

Context { RSOAM : RealSubsetOAM }.
Open Scope RSOAM_scope.

(* Affine functions *)
Inductive AffineFunction (in_dim out_dim: nat) :=
| Affine (C: matrix (T:=T RSOAM) out_dim in_dim) 
    (b: colvec (RSOAM:=RSOAM) out_dim).

Definition is_affine_f_value {in_dim out_dim: nat} 
  (f: AffineFunction in_dim out_dim) 
  (x: colvec in_dim) 
  (f_x: colvec out_dim) : Prop 
  :=
  match f with
  | Affine C b => ((Mmult (T:=RSOAM) C x) + b)%M = f_x
  end.


Definition affine_f_eval {in_dim out_dim: nat}
  (f: AffineFunction in_dim out_dim)
  (x: colvec in_dim) : colvec out_dim
  :=
  match f with
  | Affine C b => ((Mmult (T:=RSOAM) C x) + b)%M
  end.

Theorem affine_f_eval_correct:
  forall in_dim out_dim (f: AffineFunction in_dim out_dim) x f_x,
    is_affine_f_value f x f_x <-> affine_f_eval f x = f_x.
Proof.
  intros in_dim out_dim f x f_x.
  unfold is_affine_f_value; unfold affine_f_eval.
  destruct f.
  split; intros H; apply H.
Qed.

(* Affine segment *)
Inductive AffineSegment (in_dim out_dim: nat) :=
| Segment (p: ConvexPolyhedron (RSOAM:=RSOAM) in_dim) 
    (f: AffineFunction in_dim out_dim).

Definition in_affine_segment_domain {in_dim out_dim: nat}
  (f: AffineSegment in_dim out_dim)
  (x: colvec in_dim) := 
  match f with
  | Segment p af => in_convex_polyhedron x p
  end.

Definition is_affine_segment_value {in_dim out_dim: nat} 
  (f: AffineSegment in_dim out_dim) 
  (x: colvec in_dim) 
  (f_x: colvec out_dim) :=
  in_affine_segment_domain f x /\ 
  match f with
  | Segment p af => is_affine_f_value af x f_x
  end.

Lemma affine_seg_in_domain_has_value:
  forall in_dim out_dim (f: AffineSegment in_dim out_dim) x,
    in_affine_segment_domain f x ->
      exists f_x, is_affine_segment_value f x f_x.
Proof.
  intros in_dim out_dim f x Hdomain.
  destruct f as [p af].
  exists (affine_f_eval af x).
  unfold is_affine_segment_value.
  split; try apply Hdomain.
  apply affine_f_eval_correct.
  reflexivity.
Qed.

Definition affine_segment_eval {in_dim out_dim: nat}
  (f: AffineSegment in_dim out_dim)
  (x: colvec in_dim) : option (colvec out_dim)
  :=
  match f with
  | Segment p af => 
      match polyhedron_eval x p with
      | true => Some (affine_f_eval af x)
      | false => None
      end
  end.

Theorem affine_segment_eval_correct:
  forall in_dim out_dim (f: AffineSegment in_dim out_dim) x f_x,
    affine_segment_eval f x = Some f_x <-> is_affine_segment_value f x f_x.
Proof.
  intros in_dim out_dim f x f_x.
  unfold affine_segment_eval. 
  unfold is_affine_segment_value.
  destruct f; simpl.
  split; intros H.
  * destruct (polyhedron_eval x p) eqn:Heval; try inversion H as [Hf_x].
    apply polyhedron_eval_correct in Heval.
    split; try apply Heval.
    unfold is_affine_f_value.
    destruct f.
    unfold affine_f_eval.
    reflexivity.
  * destruct H as [Hinpoly Hvalue].
    apply polyhedron_eval_correct in Hinpoly.
    rewrite Hinpoly.
    unfold is_affine_f_value in Hvalue.
    destruct f.
    rewrite <- Hvalue.
    reflexivity.
Qed.  

(**
PWAF Axiom

For all polehydra pairs (p1 p2) \in body of PWAF f
holds that if p1 and p2 intersect, the corresponding
affine functions are the same, formally: for all
x, such that x \in p1 and x\in p2 holds that

A_1 * x + b_1 = A_2 * x + b_2

where A_i, b_i are affine function parameters
associated with p_i

This guarantees that the output of PWAF is unique
*)
Definition pwaf_univalence 
    {in_dim out_dim: nat}
    (l: list (AffineSegment in_dim out_dim))
    :=
    ForallPairs (
        fun e1 e2 =>
          forall x,
            in_affine_segment_domain e1 x /\ in_affine_segment_domain e2 x ->
            affine_segment_eval e1 x = affine_segment_eval e2 x
    ) l. 

(**
Piecewise affine function (PWAF)

A function is affine if it can be expressed as
f(x) = A*x + b 
where A is a matrix and b is a vector.

PWAF is defined by multiple polyhedra with an affine
function attached to them. To compute f(x), the value of
PWAF f on input x, one needs to find
a polyhedron to which x belongs and compute f(x)
using affine function.

Members:
- body: list of polyhedra with an associated linear function
- prop: PWAF univalence property

Hypothesis: this is a class of functions that can be
defined using a SMT solver.
*)
Record PWAF {in_dim out_dim: nat}: Type := mkPLF {
    body: list (AffineSegment in_dim out_dim);
    prop: pwaf_univalence body;
}.

(**
Useful invariant of pwaf_univalence: 
if pwaf_univalence holds for a list, it holds for tail of that list as well
*)
Lemma pwaf_univalence_inv:
    forall in_dim out_dim h t,
    pwaf_univalence (in_dim:=in_dim) (out_dim:=out_dim) (h :: t) -> pwaf_univalence t.
Proof.
    intros in_dim out_dim h t Hax.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b HaIn HbIn x Hinpolyh.
    unfold pwaf_univalence in Hax.
    assert (ax1 := Hax).
    unfold ForallPairs in ax1.
    specialize (ax1 a b).
    specialize (ax1 (in_cons h a t HaIn)).
    specialize (ax1 (in_cons h b t HbIn)).
    specialize (ax1 x Hinpolyh).
    apply ax1.
Qed.

(**
A point x is in domain of PWAF f, if it has 
a polehydron in body of f

Note that PWAF is not total, it is not required
for polyhedra to cover entire R^n
*)
Definition in_pwaf_domain {in_dim out_dim: nat}
    (f: PWAF (out_dim := out_dim))
    (x: colvec in_dim) :=  
        exists body_el, 
            In body_el (body f) 
                /\ in_affine_segment_domain body_el x.

(** 
A predicate that describes the value of PWAF f
f(x) = f_x for a PWAF f
*)
Definition is_pwaf_value {in_dim out_dim: nat} 
    (f: PWAF) 
    (x: colvec in_dim) 
    (f_x: colvec out_dim) 
    :=
    exists body_el,
        In body_el (body f) 
            /\ is_affine_segment_value body_el x f_x.

Theorem pwaf_value_always_in_domain: 
    forall in_dim out_dim f (x: colvec in_dim) (f_x: colvec out_dim),
      is_pwaf_value f x f_x -> in_pwaf_domain f x.
Proof.
  intros in_dim out_dim f x f_x Hval.
  unfold in_pwaf_domain.
  unfold is_pwaf_value in Hval.
  destruct Hval as [seg_val Hval].
  exists seg_val.
  split; try apply Hval.
Qed.

Fixpoint pwaf_eval_helper 
    {in_dim out_dim: nat}
    (body: list (AffineSegment in_dim out_dim))
    (x: colvec in_dim) 
    :=
    match body with
    | nil => None
    | body_el :: next => 
        match affine_segment_eval body_el x with
        | Some f_x => Some f_x
        | None => pwaf_eval_helper next x
        end
    end.

(**
  Function that directly computes the value of
  PWAF or outputs None if x is not in the domain
*)
Definition pwaf_eval {in_dim out_dim: nat} (f: PWAF)
    (x: colvec in_dim) : option (colvec out_dim)
    :=
    pwaf_eval_helper (body f) x.

Theorem pwaf_eval_correct :
    forall in_dim out_dim f (x: colvec in_dim) (f_x: colvec out_dim),
        pwaf_eval f x = Some f_x <-> is_pwaf_value f x f_x.
Proof.
    intros in_dim out_dim f x f_x.
    unfold pwaf_eval.
    destruct f as [body ax].
    induction body as [|last_el next_els].
    * split.
      - intros H; inversion H.
      - intros Hvalue.
        destruct Hvalue as [seg_for_x Hseg_x].
        simpl in Hseg_x; destruct Hseg_x; contradiction.    
    * unfold pwaf_eval_helper; simpl.
      remember (affine_segment_eval last_el x) as seg_eval.
      destruct seg_eval.
      {
        destruct last_el as [last_seg_p last_seg_af] eqn:Hlast_el.
        split; intro H.
        * inversion H as [Hc].
          symmetry in Heqseg_eval.
          apply affine_segment_eval_correct in Heqseg_eval.
          unfold is_affine_segment_value in Heqseg_eval.
          destruct Heqseg_eval as [Hseg_domain Hseg_value].
          unfold is_pwaf_value.
          exists last_el.
          split.
          - rewrite Hlast_el; apply in_eq.
          - unfold is_affine_segment_value; rewrite Hlast_el.
            split; try apply Hseg_domain.  
            rewrite <- Hc. apply Hseg_value.
        * rewrite Heqseg_eval.
          apply affine_segment_eval_correct.
          destruct H as [body_seg_x Hbody_seg_x].
          destruct Hbody_seg_x as [Hbody_seg_x_in_body Hbody_seg_val_x].
          symmetry in Heqseg_eval. 
          apply affine_segment_eval_correct in Heqseg_eval.
          destruct Heqseg_eval as [H_in_last_seg_x Hlast_seg_x_val].
          unfold pwaf_univalence in ax.
          unfold ForallPairs in ax.
          pose proof ax as ax2.
          specialize (ax2 last_el body_seg_x).
          rewrite Hlast_el in ax2.
          specialize (ax2 (in_eq _ _)).
          specialize (ax2 Hbody_seg_x_in_body x).
          unfold is_affine_segment_value in Hbody_seg_val_x.
          destruct body_seg_x as [body_seg_x_p body_seg_x_ax] eqn:Hbody_el.
          destruct Hbody_seg_val_x as [Hdom_body_x Hvalue_body_x].
          assert (Hintersect: in_affine_segment_domain last_el x /\
                              in_affine_segment_domain body_seg_x x). 
          { split. rewrite Hlast_el. auto. rewrite Hbody_el. auto.  }
          rewrite Hlast_el in Hintersect. rewrite Hbody_el in Hintersect.
          specialize (ax2 Hintersect).
          apply affine_segment_eval_correct.
          rewrite ax2. rewrite <- Hbody_el. 
          apply affine_segment_eval_correct.
          unfold is_affine_segment_value.
          rewrite Hbody_el.
          auto.
      }
      {
        pose proof ax as ax2.
        apply pwaf_univalence_inv in ax2.
        specialize (IHnext_els ax2).
        fold (pwaf_eval_helper next_els x).
        simpl in IHnext_els.
        destruct IHnext_els as [IHnext1 IHnext2]. 
        split.
        - intros Heval.
          specialize (IHnext1 Heval).
          unfold is_pwaf_value.
          unfold is_pwaf_value in IHnext1.
          destruct IHnext1 as [body_el Hbody_el]. 
          exists body_el; destruct Hbody_el as [Hbody_seg_1 Hbody_seg_2]; split.
          * apply in_cons; apply Hbody_seg_1. 
          * apply Hbody_seg_2.
        - intros Hvalue.
          apply IHnext2.
          unfold is_pwaf_value in Hvalue; destruct Hvalue as [body_el Hbody_el].
          destruct Hbody_el as [Hbody_seg_1 Hbody_seg_2].
          apply in_inv in Hbody_seg_1.
          destruct Hbody_seg_1 as [Hbody_seg_1_l | Hbody_seg_1_r].
          * rewrite <- affine_segment_eval_correct in Hbody_seg_2. 
            rewrite <- Hbody_seg_1_l in Hbody_seg_2.
            rewrite <- Heqseg_eval in Hbody_seg_2.
            inversion Hbody_seg_2.
          * unfold is_pwaf_value.
            exists body_el; split.
            - apply Hbody_seg_1_r.
            - apply Hbody_seg_2. 
      }
Qed.
        
(**
A PWAF representation g of a real function f is a PWAF
that is equal to f everywhwere: for all x f(x) = g(x)
*)
Definition pwaf_representation {in_dim out_dim: nat} 
    (f: colvec in_dim -> colvec out_dim) 
    (g: PWAF) :=
    forall x, is_pwaf_value g x (f x).
    
(**
A function is piecewise linear if there is a PWAF representations
*)
Definition is_piecewise_linear {in_dim out_dim: nat} 
    (f: colvec in_dim -> colvec out_dim) 
    :=
    exists pwaf,
        pwaf_representation f pwaf.

(**
PWAF is total if the function is defined on all inputs in R^n
*)
Definition is_total {in_dim out_dim: nat} (f: PWAF (out_dim:=out_dim)) :=
    forall (x: colvec in_dim), in_pwaf_domain f x.

(**
A TPWAF is a total PWAF
*)
Definition TPWAF {in_dim out_dim: nat} := 
    { f: PWAF (in_dim:=in_dim) (out_dim:=out_dim) | is_total f }.

Definition TPWAF2PWAF {in_dim out_dim: nat} 
  (f: TPWAF (in_dim:=in_dim) (out_dim:=out_dim)) : PWAF := proj1_sig f.

Coercion TPWAF2PWAF : TPWAF >-> PWAF.

Lemma tpwaf_pwaf_eval_never_none:
  forall in_dim out_dim 
  (f: TPWAF (in_dim:=in_dim) (out_dim:=out_dim)) x,
    pwaf_eval f x = None -> False.
Proof.
  intros in_dim out_dim f x Heval.
  destruct f as [f Htotal]; simpl in Heval.
  unfold is_total in Htotal.
  specialize (Htotal x).
  unfold in_pwaf_domain in Htotal.
  destruct Htotal as [body_seg_x Hbody_seg_x].
  assert (Hmain: exists f_x, is_pwaf_value f x f_x). {
    destruct Hbody_seg_x as [HIn Hdomain].
    apply affine_seg_in_domain_has_value in Hdomain.
    destruct Hdomain as [f_x Hseg_val].
    exists f_x.
    unfold is_pwaf_value.
    exists body_seg_x.
    split.
    * apply HIn.
    * apply Hseg_val.
  }
  destruct Hmain as [f_x Hvalue].
  apply pwaf_eval_correct in Hvalue.
  rewrite Heval in Hvalue.
  inversion Hvalue.
Qed.

Definition tpwaf_eval {in_dim out_dim: nat} 
  (f: TPWAF) (x: colvec in_dim) : colvec out_dim
  :=
  match pwaf_eval f x as eval_result
    return (pwaf_eval f x = eval_result -> colvec out_dim) with 
  | Some value => fun _ => value
  | None => fun p => 
    False_rect (colvec out_dim) (tpwaf_pwaf_eval_never_none _ _ f x p)
  end (eq_refl (pwaf_eval f x)).

Theorem tpwaf_eval_correct:
  forall in_dim out_dim 
    (f: TPWAF (in_dim:=in_dim) (out_dim:=out_dim)) x,
  is_pwaf_value f x (tpwaf_eval f x).
Proof.
  intros in_dim out_dim f x.
  apply pwaf_eval_correct.
  destruct (pwaf_eval f x) eqn:Heval.
  * f_equal.
    unfold tpwaf_eval.
    generalize (eq_refl (pwaf_eval f x)).
    apply (eq_ind (Some c)
      (fun a =>
        forall e: pwaf_eval f x = a,
          c = 
          match a as eval_result 
            return (pwaf_eval f x = eval_result -> colvec out_dim) with
          | Some value => _
          | None => _
          end e
        )).
    - reflexivity.
    - symmetry; apply Heval.
  * apply tpwaf_pwaf_eval_never_none in Heval; contradiction.
Qed.

Lemma is_pwaf_value_tpwaf_eval:
  forall in_dim out_dim
    (f: TPWAF (in_dim:=in_dim) (out_dim:=out_dim)) x fx,
    is_pwaf_value f x fx <-> tpwaf_eval f x = fx.
Proof.
  intros in_dim out_dim f x fx.
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

End PiecewiseLinear.

(** * Example proof of piecewise linearity via construction

We prove that a simple ReLU function f([x1, x2]) = [ReLU(2 * x1 + x2), x2] is
piecewise linear by constructing a corresponding TCPLF-SO 
using definition from section PiecewiseLinear
*)

Section PiecewiseLinearExample.

(**
Naive/direct defintion of the example simple ReLU function

f([x1, x2]) = [ReLU(2*x1 + x2), x2]
*)
Definition simpleReLU (x: colvec 2): colvec 2 :=
    let c: colvec 2 := [[2%Z], [1%Z]] in
    let dot_val := dot c x in
    let relu_result := if Z.leb dot_val 0%Z then 0%Z else dot_val in
    [[relu_result], [coeff_colvec 0%Z x 1]].

(**
Construction of TCPLF for simple ReLU finction example

TCPLF consists of:
- A polyhedron for 2 * x1 + x2 <= 0
- A polyhedron for 2 * x1 + x2 >= 0
- Proofs of axioms
*)

Definition c_vector: colvec 2 := [[2%Z], [1%Z]]. 
Definition minus_c_vector: colvec 2 := scalar_mult (- 1)%Z c_vector.

Definition lincon1 := Constraint 2 c_vector 0%Z.
Definition lincon2 := Constraint 2 minus_c_vector 0%Z.

(** Polyhedron for 2 * x1 + x2 <= 0 *)
Definition polyhedra1 := Polyhedron 2 (cons lincon1 nil).

(** Polyhedron for 2 * x1 + x2 >= 0 which is equivalent to
    - 2 * x1 - x2 <= 0 *)
Definition polyhedra2 := Polyhedron 2 (cons lincon2 nil).
Definition polyhedra_simpleReLU := (cons polyhedra1 (cons polyhedra2 nil)).

(** 
Function body for TCPLF-SO of simple ReLU

Polyhedron 1 -> [0, x2]     
Polyhedron 2 -> [2 * x1 + x2, x2]
*)
Definition matrix1: matrix 2 2:=
    [[0, 0],
     [0, 1]]%Z.
Definition affine_f_1: AffineFunction 2 2 := Affine 2 2 matrix1 (null_vector 2).

Definition matrix2: matrix 2 2 :=
    [[2, 1],
    [0, 1]]%Z.
Definition affine_f_2: AffineFunction 2 2 := Affine 2 2 matrix2 (null_vector 2).

Definition affine_seg_1: AffineSegment 2 2 := Segment 2 2 polyhedra1 affine_f_1.
Definition affine_seg_2: AffineSegment 2 2 := Segment 2 2 polyhedra2 affine_f_2.

Definition simpleReLU_body := (cons affine_seg_1 (cons affine_seg_2 nil)).

(**
Lemma: two polyhedra intersect at exactly 2*x1 + x2 = 0

Proof requires inference in hypothesis of intersection to
arrive at 2 * x1 + x2 <= 0 and 2 * x1 + x2 >= 0 which is then
proven using Rle_anitsym
*)
Lemma simpleReLU_polyhedra_intersection:
    forall x, 
        in_convex_polyhedron x polyhedra1 /\ in_convex_polyhedron x polyhedra2 ->
        dot c_vector x = 0%Z.
Proof.
    intros x. simpl. 
    unfold satisfies_lc. 
    intros H. destruct H as [H H0].
    specialize (H lincon1). specialize (H0 lincon2).
    unfold lincon1 in H. unfold lincon2 in H0.
    assert (forall dim (c: LinearConstraint (RSOAM:=Z_RSOAM) dim), 
                c = c \/ False). {
        intros dim c. left. reflexivity.
    }
    specialize (H1 2%nat lincon1) as H11.
    specialize (H1 2%nat lincon2) as H12.
    apply H in H11. apply H0 in H12.
    unfold minus_c_vector in H12.
    rewrite dot_scalar_mult in H12.
    simpl in H11; apply Zle_bool_imp_le in H11.
    simpl in H12; apply Zle_bool_imp_le in H12.
    destruct (c_vector * x)%v; lia.
Qed.

(**
Theorem: univalence holds for simple ReLU. This means
that for two polyhedra of simple ReLU, the function is uniquely
defined at their intersection

Proof: we first destruct the goal sufficiently to create a proof
goal for each polyhedra pair and then show for each pair that
the function is the same using simple_ReLU_polyhedra_intersection
lemma
*)
Theorem simpleReLU_prop:
    pwaf_univalence simpleReLU_body.
Proof.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b.
    unfold In. simpl.
    intros Ha Hb x Hintersect.
    assert (Hmain: 
        in_affine_segment_domain affine_seg_1 x /\ 
        in_affine_segment_domain affine_seg_2 x ->
            affine_segment_eval affine_seg_1 x = 
            affine_segment_eval affine_seg_2 x). {
        intros Hinboth.
        unfold in_affine_segment_domain in Hinboth.
        unfold affine_seg_1 in Hinboth; unfold affine_seg_2 in Hinboth.
        unfold affine_segment_eval.
        unfold affine_seg_1; unfold affine_seg_2.
        unfold affine_f_eval.
        unfold affine_f_1; unfold affine_f_2.
        pose proof Hinboth as Hinboth2.
        destruct Hinboth2 as [Hin1 Hin2].
        apply polyhedron_eval_correct in Hin1.
        apply polyhedron_eval_correct in Hin2.
        rewrite Hin1; rewrite Hin2; f_equal.
        repeat rewrite Mplus_null_vector.
        repeat rewrite Mmult_dot_split.
        unfold mk_colvec.
        apply mk_matrix_ext.
        intros i j Hi Hj.
        induction i.
        * match goal with 
          | [ |- (_ * x)%v = ((?X) * x)%v] => remember (X) as rmbrd
          end.
          assert (Hequal: rmbrd = c_vector). {
            rewrite Heqrmbrd.
            unfold c_vector. unfold mk_colvec.
            unfold matrix2. reflexivity.
          }
          rewrite Hequal.
          rewrite simpleReLU_polyhedra_intersection; try apply Hinboth.
          unfold dot. unfold Mmult.
          rewrite coeff_mat_bij; try lia. unfold sum_n.
          assert (Hzero: forall n m, sum_n_m (G:=Z_RSOAM) 
              (fun _ => zero) n m = 0%Z). {
            intros n m.
            rewrite (sum_n_m_const_zero n m).
            reflexivity.
          }
          rewrite <- (Hzero 0%nat 1%nat).
          apply (sum_n_m_ext_loc (G:=Z_RSOAM)). 
          intros n Hn.
          unfold transpose.
          rewrite coeff_mat_bij; try lia.
          unfold coeff_colvec.
          rewrite coeff_mat_bij; try lia.
          unfold matrix1.
          induction n.
          - compute; reflexivity.
          - induction n; compute; reflexivity.
        * assert (Hhelp: i = 0%nat). lia. 
          rewrite Hhelp. unfold matrix1. unfold matrix2. compute; reflexivity.
    } 
    destruct Ha. 
    * destruct Hb.
      - rewrite <- H. rewrite <- H0. reflexivity.
      - destruct H0; try contradiction.
        rewrite <- H. rewrite <- H0. 
        apply Hmain.
        rewrite <- H in Hintersect.
        rewrite <- H0 in Hintersect.
        simpl in Hintersect.
        apply Hintersect.
    * destruct H; try contradiction. destruct Hb.
      - rewrite <- H. rewrite <- H0.
        symmetry. apply Hmain.
        rewrite <- H in Hintersect.
        rewrite <- H0 in Hintersect.
        destruct Hintersect. split. apply H2. apply H1. 
      - destruct H0; try contradiction.
        rewrite <- H. rewrite <- H0. reflexivity.
Qed.

(**
PWAF for simple ReLU
*)
Definition simpleReLU_PWAF := mkPLF 2 2 simpleReLU_body simpleReLU_prop.

(**
Theorem: naive definition of simple ReLU example, simpleReLU, 
is represented by PWAF and hence piecewise linear

Proof: mostly utilizes Rle_dec (x <= y) \/ ~ (x <= y) to 
arrive at four cases for each possible polyhedra and if-statement result
of the naive definition where we then show either contradiction or 
equality of function values
*)
Theorem simpleReLU_piecewise_linear:
    is_piecewise_linear simpleReLU.
Proof.
    unfold is_piecewise_linear.
    exists simpleReLU_PWAF.
    unfold pwaf_representation.
    intros x.
    unfold is_pwaf_value.
    destruct (Z_le_dec (dot c_vector x) 0) as [r|n].
    * exists affine_seg_1.
      split.
      * simpl. left. reflexivity.  
      * split.
        - unfold in_affine_segment_domain. simpl.  
          intros constraint Hconstraint.
          destruct Hconstraint.
          rewrite <- H.
          unfold satisfies_lc. simpl.
          apply Zle_is_le_bool.
          apply r. contradiction.
        - unfold is_affine_f_value. 
          unfold affine_f_1.
          unfold simpleReLU.
          unfold affine_seg_1. unfold affine_f_1.
          rewrite Mplus_null_vector.
          fold c_vector.
          apply Zle_is_le_bool in r; rewrite r.
          unfold matrix1.
          rewrite <- (mk_matrix_bij 0%Z).
          apply mk_matrix_ext.
          intros i j Hi Hj.
          induction i; induction j; try lia.
          * compute; lia.
          * assert (Hhelp: i = 0%nat). lia.
            rewrite Hhelp; simpl.
            unfold sum_n; unfold sum_n_m; unfold Iter.iter_nat; 
            unfold Iter.iter; simpl.
            unfold coeff_colvec; unfold coeff_mat; simpl.
            rewrite (mult_zero_l (K:=Z_RSOAM)).
            rewrite (plus_zero_l (G:=Z_RSOAM)).
            rewrite (mult_one_l (K:=Z_RSOAM)).
            rewrite (plus_zero_r (G:=Z_RSOAM)).
            reflexivity.
    * exists affine_seg_2.
      split.
      * simpl. right. left. reflexivity. 
      * apply Znot_le_gt in n. 
        split.
        - unfold in_convex_polyhedron.
          intros constraint Hconstraint.
          destruct Hconstraint.
          rewrite <- H.
          unfold satisfies_lc. unfold lincon2.
          unfold minus_c_vector.
          rewrite dot_scalar_mult.
          assert (Hhelp: (-1)%Z = Z.opp 1). lia.
          rewrite Hhelp.
          rewrite <- Zopp_mult_distr_l.
          rewrite Zmult_1_l.
          apply Zle_is_le_bool.
          lia. contradiction H.
        - unfold is_affine_f_value.
          unfold affine_f_2.
          unfold simpleReLU.
          fold c_vector.
          unfold affine_seg_2. unfold affine_f_2.
          rewrite Mplus_null_vector.
          destruct (Z_le_dec (dot c_vector x) 0%Z); try lia.
          unfold matrix2.
          rewrite <- (mk_matrix_bij 0%Z). 
          apply mk_matrix_ext.
          intros i j Hi Hj.
          induction i; induction j; try (compute; lia).
          * rewrite Zle_is_le_bool in n0.
            apply Bool.not_true_is_false in n0.
            rewrite n0.
            unfold dot.
            unfold transpose.
            unfold Mmult.
            repeat rewrite coeff_mat_bij; try lia.
            unfold sum_n; unfold sum_n_m; unfold Iter.iter_nat; 
            unfold Iter.iter; simpl.
            unfold coeff_colvec; unfold coeff_mat; simpl.
            reflexivity.            
          * assert (Hhelp: i = 0%nat). lia.
            rewrite Zle_is_le_bool in n0.
            apply Bool.not_true_is_false in n0.
            rewrite n0; simpl.
            unfold sum_n; unfold sum_n_m; unfold Iter.iter_nat; 
            unfold Iter.iter; simpl.
            unfold coeff_colvec; unfold coeff_mat; simpl.
            rewrite Hhelp; simpl.
            rewrite (mult_zero_l (K:=Z_RSOAM)).
            rewrite (plus_zero_l (G:=Z_RSOAM)).
            rewrite (mult_one_l (K:=Z_RSOAM)).
            rewrite (plus_zero_r (G:=Z_RSOAM)).
            reflexivity.
Qed.

(**
Lemma: for all [x1, x2], 2 * x1 + x2 <= 0 or 2 * x1 + x2 >= 0

Proof: By specializing Rle_or_lt that tells that for real numbers
holds (x <= y) or (y < x), we arrive that either 2 * x1 + x2 <= 0 or
0 <= 2 * x1 + x2 that correspond to constraints of simple ReLU polyhedra
*)
Lemma simpleReLU_full_R_split:
    forall x,
        satisfies_lc x lincon1 \/ satisfies_lc x lincon2.
Proof.
    intros x.
    unfold satisfies_lc.
    simpl.
    unfold minus_c_vector.
    rewrite dot_scalar_mult.
    pose proof (Z_le_dec (dot c_vector x) 0) as H.
    destruct H as [H|H].
    * left. apply Zle_is_le_bool. apply H.
    * right. apply Zle_is_le_bool.
      assert (Hhelp: (-1)%Z = Z.opp 1); try lia.  
      rewrite Hhelp.
      rewrite <- Zopp_mult_distr_l.
      rewrite Zmult_1_l.
      lia.
Qed.

(**
Theorem: simple ReLU is a total function

Proof: follows mostly from the simple_ReLU_full_R_split lemma,
we just need to show what polyhedron contains constraint needed
*)
Theorem simpleReLU_total:
    is_total simpleReLU_PWAF.
Proof.
    unfold is_total.
    unfold in_pwaf_domain.
    intros x.
    pose proof (simpleReLU_full_R_split x).
    destruct H.
    - exists affine_seg_1. split.
      * simpl. left. reflexivity.
      * simpl.
        intros constraint Hconstraint.
        destruct Hconstraint.
        rewrite <- H0. apply H.
        contradiction.
    - exists affine_seg_2. split.
      * simpl. right. left. reflexivity.
      * simpl.
        intros constraint Hconstraint.
        destruct Hconstraint.
        rewrite <- H0. apply H.
        contradiction.
Qed.

Definition simpleReLU_TPWAF: TPWAF := 
    exist _ simpleReLU_PWAF simpleReLU_total. 

End PiecewiseLinearExample. 

