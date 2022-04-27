
  Require Export XD.Integers2.

  Definition ZZnZ := { z : ZZ | z <> Zzero }.

  Definition _QPair := @Pair ZZ ZZnZ.

  Definition _Qfirst (p:_QPair) : ZZ := match p with
  | pair f _ => f
  end.

  Definition _Qsecond (p:_QPair) : ZZ := match p with
  | pair _ (exist _ s _) => s
  end.

  Definition _Qrel (x y:_QPair) :=
    Zmult (_Qfirst x) (_Qsecond y) = Zmult (_Qsecond x) (_Qfirst y).

  Theorem _Qrel_equivalence : equivalence _Qrel.
  Proof.
    red.
    split.
    {
      red.
      intros (xf,(xs,hx)).
      red.
      simpl.
      rewrite Zmult_comm.
      reflexivity.
    }
    split.
    {
      red.
      intros (xf,(xs,hx)) (yf,(ys,hy)).
      intro h.
      red.
      red in h.
      simpl in *.
      rewrite (Zmult_comm yf).
      rewrite (Zmult_comm ys).
      symmetry.
      exact h.
    }
    {
      red.
      intros (xf,(xs,hx)) (yf,(ys,hy)) (zf,(zs,hz)) hxy hyz.
      red. red in hxy,hyz.
      simpl in *.
      apply Zmult_elim_l with ys. exact hy.
      rewrite <- Zmult_assoc.
      rewrite (Zmult_comm ys).
      rewrite hxy.
      rewrite Zmult_assoc.
      rewrite hyz.
      rewrite <- Zmult_assoc.
      rewrite (Zmult_comm xs).
      rewrite Zmult_assoc.
      apply Zmult_intro_l.
      reflexivity.
    }
  Qed.

  Definition Zdivides (d x:ZZ) := exists d' : ZZ, Zmult d d' = x.

  Definition Zcoprime (x y:ZZ) := forall d:ZZ, Zdivides d x -> Zdivides d y -> d = Zone.

  (* TODO *)
  Definition _Qcond (p:_QPair) := Zcoprime (_Qfirst p) (_Qsecond p).

  Definition QQ := { p : _QPair | _Qcond p }.

  Lemma _Q_representation : forall (p:_QPair), exists (q:QQ), _Qrel p (proj1_sig q).
  Proof.
    intros (pf,(ps,hps)).
    assert (h:_Qcond p).
    red. trivial.
    exists (exist _ p h).
    red.
    simpl.
    rewrite Zmult_comm.
    reflexivity.
  Qed.

  Lemma _Q_uniqueness : forall (x y:QQ),
    let xp := proj1_sig x in
    let yp := proj1_sig y in
    _Qrel xp yp -> xp = yp.
  Proof.
    intros ((xf,(xs,hxs)),hx) ((yf,(ys,hys)),hy).
    simpl.
    intro h.
    red in hx, hy.
    clear hx hy.
    red in h.
    simpl in h.
    f_equal.
    admit.
    apply proof_irrelevance.
    simpl.
    admit.
  Qed.


