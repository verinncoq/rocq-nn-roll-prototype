Section NNDHDeprecated.

(** Code from Lena *)
  
(** Helpers *)

Definition my_max (a b : RS) : RS :=
  if RSle (RSOPM:=RSOPM) a b then b else a.

Definition my_min (a b : RS) : RS :=
  if RSle (RSOPM:=RSOPM) a b then a else b.

Definition first {n: nat} (l : list (colvec (RSOPM:=RSOPM) n)) : (colvec (RSOPM:=RSOPM) n) :=
  match l with
  | [] => (null_vector n)
  | x :: _ => x
  end.

Definition second {n: nat} (l : list (colvec (RSOPM:=RSOPM) n)) : (colvec (RSOPM:=RSOPM) n) :=
  match l with
  | [] => (null_vector n)
  | [_] => (null_vector n)
  | _ :: y :: _ => y
  end.

Fixpoint colvec_to_list_helper {n: nat} (v: colvec n) (counter: nat): list (T RSOPM) :=
match counter with
| 0%nat => [coeff_colvec 0 v 0]
| S n => coeff_colvec 0 v counter :: colvec_to_list_helper v n
end.

Definition colvec_to_list {n: nat} (v: colvec n): list (T RSOPM) :=
match n with
| 0%nat => nil
| S k => colvec_to_list_helper v k
end.

Fixpoint check_list_rltb_zero (lst : list (T RSOPM)) : (T RSOPM) :=
  match lst with
  | nil => RSone
  | x :: xs => if RSle (RSOPM:=RSOPM) x (- RSone) then (- RSone) else check_list_rltb_zero xs
  end.

Definition abs (x1 x2 : RS) : RS :=
  if RSle (RSOPM:=RSOPM) x1 x2 then RSplus (RSOPM:=RSOPM) x2 (RSopp (RSOPM:=RSOPM) x1) 
    else RSplus (RSOPM:=RSOPM) x1 (RSopp (RSOPM:=RSOPM) x2).


Fixpoint max_abs_diff (l1 l2 : list RS) : RS :=
  match l1, l2 with
  | nil, _ => 0
  | _, nil => 0
  | x1 :: xs1, x2 :: xs2 => 
      let diff := abs x1 x2 in
      my_max diff (max_abs_diff xs1 xs2)
  end.


Definition Minus_colvec {n:nat} (x y : colvec (RSOPM:=RSOPM) n) : colvec (RSOPM:=RSOPM) n :=
  Mplus (G:=RSOPM) x (scalar_mult (RSopp (RSOPM:=RSOPM) 1) y).

(** Verify NNDH *)

Fixpoint apply_ae {in_dim out_dim : nat} (ae : AffineElement (RSOPM:=RSOPM) in_dim out_dim) 
  (inputs : list (colvec (RSOPM:=RSOPM) in_dim)) 
    : list (colvec (RSOPM:=RSOPM) out_dim) :=
    let output_set : list (colvec (RSOPM:=RSOPM) out_dim) := [] in
    let none : list (colvec (RSOPM:=RSOPM) out_dim) := [] in
    match inputs with 
      | [] => output_set
      | x :: xs => match affine_element_eval ae x with
                      | Some aex => [aex] ++ (apply_ae ae xs) ++ output_set 
                      | None => none
                   end
    end.

Definition RSle_prop (x: RS (RSOPM:=RSOPM)) (y : RS (RSOPM:=RSOPM)) : Prop :=
  x <= y = true.


Fixpoint nndh_verify_aed {in_dim out_dim w : nat}  {W : ConvexPolyhedron (RSOPM:=RSOPM) w} (pwaf: list (AffineElement in_dim out_dim)) (nndh: NNDH W in_dim out_dim) :=
  match pwaf with
  | [] => match nndh with
                | Hyperproperty netIn netSat => 
                    forall (x: colvec (RSOPM:=RSOPM) w), in_convex_polyhedron x W -> 
                      let input_set : list (colvec (RSOPM:=RSOPM) in_dim) := netIn x in 
                        RSle_prop  0 (netSat input_set [])
              end
  | ae :: aes => match nndh with
                | Hyperproperty netIn netSat => 
                    forall (x: colvec (RSOPM:=RSOPM) w), in_convex_polyhedron x W -> 
                      let input_set : list (colvec (RSOPM:=RSOPM) in_dim) := netIn x in 
                      let output_set : list (colvec (RSOPM:=RSOPM) out_dim) := apply_ae ae input_set in
                        RSle_prop  0 (netSat input_set output_set)
              end
               /\ (nndh_verify_aed aes nndh)
  end. 



Fixpoint apply_nn_eval {in_dim out_dim: nat}
(nn: TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim)) 
(inputs : list (colvec (RSOPM:=RSOPM) in_dim)) 
: list (colvec (RSOPM:=RSOPM) out_dim) :=
  let output_set : list (colvec (RSOPM:=RSOPM) out_dim) := [] in  
  match inputs with
    | [] => output_set
    | x :: xs => [nn_eval nn x] ++ (apply_nn_eval nn xs) ++ output_set
  end. 




Fixpoint apply_tpwaf_eval {in_dim out_dim: nat}
(tpwaf: TPWAF (RSOPM:=RSOPM) (in_dim := in_dim) (out_dim := out_dim)) 
(inputs : list (colvec (RSOPM:=RSOPM) in_dim)) 
: list (colvec (RSOPM:=RSOPM) out_dim) :=
  let output_set : list (colvec (RSOPM:=RSOPM) out_dim) := [] in  
  match inputs with
    | [] => output_set
    | x :: xs => [tpwaf_eval tpwaf x] ++ (apply_tpwaf_eval tpwaf xs) ++ output_set
  end. 

Definition nndh_verify_pwaf {in_dim out_dim w: nat} {W : ConvexPolyhedron (RSOPM:=RSOPM) w} 
  (tpwaf: TPWAF (RSOPM:=RSOPM) (in_dim := in_dim) (out_dim := out_dim)) (nndh: NNDH W in_dim out_dim) : Prop :=
   match nndh with 
  | Hyperproperty netIn netSat =>
    forall (x: colvec (RSOPM:=RSOPM) w), in_convex_polyhedron x W -> 
      let input_set : list (colvec (RSOPM:=RSOPM) in_dim) := netIn x in 
      let output_set : list (colvec (RSOPM:=RSOPM) out_dim) := apply_tpwaf_eval tpwaf input_set in
        RSle_prop  0 (netSat input_set output_set)
  end.
    
Theorem apply_tpwaf_eval_correct :
  forall in_dim out_dim (nn : TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim)) tpwaf (inputs : list (colvec (RSOPM:=RSOPM) in_dim)),
    tpwaf = aed nn -> apply_tpwaf_eval tpwaf inputs = apply_nn_eval nn inputs.

Proof.
  intros in_dim out_dim nn tpwaf inputs Htpwaf.
  induction inputs.
    + simpl.
      reflexivity.
    + simpl.
      rewrite IHinputs.
      rewrite app_nil_r.
      f_equal.
      pose proof (tpwaf_eval_correct _ _ tpwaf a) as H1.
      pose proof (aed_correct _ _ a (tpwaf_eval tpwaf a) nn tpwaf) as H2.
      apply H2 in H1.
      symmetry. exact H1.
      apply Htpwaf.
Qed.

Theorem nndh_nn_pwaf :
   forall in_dim out_dim (nn : TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim)) w (W: ConvexPolyhedron (RSOPM:=RSOPM) w) nndh tpwaf, 
    tpwaf = aed nn ->
    nndh_verify_pwaf (W:=W) (in_dim:=in_dim) (out_dim:=out_dim) (w:=w) tpwaf nndh <-> nndh_verify_nn nn nndh.

Proof.
  intros in_dim out_dim nn w W nndh tpwaf Htpwaf.
  split.
    + unfold nndh_verify_pwaf.
      destruct nndh.
      unfold nndh_verify_nn.
      intros H1 x.
      specialize (H1 x).
      intros HxinW.
      specialize (H1 HxinW).
      pose proof (apply_tpwaf_eval_correct in_dim out_dim nn tpwaf (netIn x)) as Hcorrect.
      rewrite Htpwaf in Hcorrect.
      specialize (Hcorrect eq_refl).
      rewrite Htpwaf in H1.
      rewrite Hcorrect in H1.
      exact H1.
    + unfold nndh_verify_nn.
      destruct nndh.
      unfold nndh_verify_pwaf.
      intros H1 x.
      specialize (H1 x).
      intros HxinW.
      specialize (H1 HxinW).
      pose proof (apply_tpwaf_eval_correct in_dim out_dim nn tpwaf (netIn x)) as Hcorrect.
      rewrite Htpwaf in Hcorrect.
      specialize (Hcorrect eq_refl).
      rewrite Htpwaf.
      rewrite <- Hcorrect in H1.
      exact H1.
Qed.

Theorem nndh_pwaf_aed :
   forall in_dim out_dim w (W: ConvexPolyhedron (RSOPM:=RSOPM) w) nndh (tpwaf: TPWAF (RSOPM:=RSOPM) (in_dim := in_dim) (out_dim := out_dim)) aed, 
    aed = body tpwaf ->
    nndh_verify_aed (W:=W) (in_dim:=in_dim) (out_dim:=out_dim) (w:=w) aed nndh -> nndh_verify_pwaf tpwaf nndh.

Proof.
  intros in_dim out_dim w W nndh tpwaf aed Haed .
  unfold nndh_verify_pwaf.
  destruct nndh as [netIn netSat].
  induction aed as [|hd tl IHaed].
    + simpl.
      intros H.
      intros x HxinW.
      specialize (H x HxinW).
      induction (netIn x) as [|x' input_tl IHinput].
        - simpl.
          exact H.
        - admit.
    + intros H.
      simpl in H.
      intros x HxinW.
Admitted.

Theorem nndh_verification :
  forall in_dim out_dim (nn : TPWANNSequential (input_dim:=in_dim) (output_dim:=out_dim)) w (W: ConvexPolyhedron (RSOPM:=RSOPM) w) nndh nn_pwaf aed_body, 
    nn_pwaf = aed nn ->
    aed_body = body nn_pwaf ->
    nndh_verify_aed (W:=W) (in_dim:=in_dim) (out_dim:=out_dim) (w:=w) aed_body nndh -> nndh_verify_nn nn nndh.
Admitted.

(* Andrei's first attempt on affine element semantics *)

(** Semantics over an affine element *)

Definition affine_el_to_pwaf_body {in_dim out_dim: nat} 
  (el: AffineElement (RSOPM:=RSOPM) in_dim out_dim) 
  : list (AffineElement in_dim out_dim) 
  := [el].

Definition affine_el_to_pwaf_univalence {in_dim out_dim: nat}:
  forall (el: AffineElement (RSOPM:=RSOPM) in_dim out_dim), 
    pwaf_univalence (RSOPM:=RSOPM) (affine_el_to_pwaf_body el).
Proof.
  intro el; unfold pwaf_univalence; unfold ForallPairs.
  intros el1 el2; unfold affine_el_to_pwaf_body, In.
  intros Hel1 Hel2 x Hdomain.
  destruct Hel1 as [Hel1|Hfalse], Hel2 as [Hel2|Hfalse2]; try contradiction.
  rewrite <- Hel1, <- Hel2; reflexivity.
Qed.

Definition affine_element_to_pwaf {in_dim out_dim: nat} 
  (el: AffineElement (RSOPM:=RSOPM) in_dim out_dim) : PWAF (RSOPM:=RSOPM) :=
  mkPLF in_dim out_dim 
    (affine_el_to_pwaf_body el) (affine_el_to_pwaf_univalence el).

Definition affine_element_satisfies_nndh {el_in_dim el_out_dim: nat}
  (affine_el: AffineElement el_in_dim el_out_dim)
  (nndh: NNHyperproperty)
  : Prop
  :=
  pwaf_satisfies_nndh (affine_element_to_pwaf affine_el) nndh.

(** Old monotonicity example *)

Definition netIn_Monotonicity {w : nat} (u: colvec (RSOPM:=RSOPM) w) : list (colvec (RSOPM:=RSOPM) (w/2)) := 
  let w1 := mk_colvec (w/2) (fun i => coeff_colvec 0 u i) in
  let w2 := mk_colvec (w/2) (fun j => coeff_colvec 0 u (j + (w/2))) in
  let w1' := mk_colvec (w/2) (fun k => my_max (coeff_colvec 0 w1 k) (coeff_colvec 0 w2 k)) in
  let w2' := mk_colvec (w/2)  (fun l => my_min (coeff_colvec 0 w1 l) (coeff_colvec 0 w2 l)) in
  [w1'] ++ [w2'].

Definition netSat_Monotonicity {in_dim out_dim : nat} (input: list (colvec (RSOPM:=RSOPM) in_dim)) (output: list (colvec (RSOPM:=RSOPM) out_dim)) : RS :=
  check_list_rltb_zero (colvec_to_list (Minus_colvec (first output) (second output))).


Definition GlobalMonotonicity {w : nat} (W: ConvexPolyhedron (RSOPM:=RSOPM) w) (out_dim : nat): NNDH W (w/2) out_dim := 
  Hyperproperty  W (w/2) out_dim  netIn_Monotonicity netSat_Monotonicity.

End NNDHDeprecated.