From Coq Require Import QArith Reals Lia Lqa.
From Verinncoq Require Import real_subsets real_subsets_instances fourier_motzkin.

Definition QDEP_div (q1 q2: QDEP) :=
    toQDEP (Qdiv q1 q2).

Lemma QDEP_ax_real_div: 
    forall (x y: QDEP),
      Q2R (QDEP_div x y) = Rdiv (Q2R x) (Q2R y).
Proof.
    intros x y.
    destruct x as [x Px]; destruct y as [y Py].
    unfold QDEP_div, toQDEP, toQDEP_impl, QDEP2Q, proj1_sig.
    assert (Hhelp: forall (z: Z), z = 0%Z \/ ~ z = 0%Z). lia.
    destruct (Hhelp (Qnum y)) as [Hzero|Hzero].
    * unfold QDEP_div, Qdiv, Qinv.
      rewrite Hzero.
      rewrite Qmult_0_r.
      rewrite Qred_correct.
      unfold Q2R.
      rewrite Hzero; simpl.
      do 2 rewrite Rmult_0_l.
      rewrite Rdiv_0_r.
      reflexivity.
    * rewrite <- Qreals.Q2R_div.
      - rewrite (Qreals.Qeq_eqR (Qred (x / y)) (x / y)); first reflexivity.
        rewrite Qred_correct; reflexivity.
      - unfold Qeq; simpl.
        lia.
Qed.

Definition Q_RSOPMD := 
    Build_RSOPMD QDEP_RSOPM QDEP_div QDEP_ax_real_div.