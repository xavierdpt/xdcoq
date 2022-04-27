
  Require Export XD.Integers.

  Lemma Zplus_mult_distr_l : forall w x y,
    Zmult w (Zplus x y) = Zplus (Zmult w x) (Zmult w y).
  Proof.
    intros (wp,hw) (xp,hx) (yp,hy).
    unfold Zmult.
    unfold Zplus.
    unfold Zmake.
    apply proof_irrelevance.
    simpl.
    rewrite _Zmult_repr.
    rewrite <- _Zplus_repr.
    symmetry.
    rewrite _Zplus_comm.
    rewrite <- _Zplus_repr.
    destruct wp as [wf ws];
    destruct xp as [xf xs];
    destruct yp as [yf ys].
    simpl.
    unfold _Zcond in *.
    simpl in *.
    destruct hw;destruct hx;destruct hy;subst.
    {
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nmin_zero_r.
      repeat rewrite Nrest_zero_l.
      repeat rewrite Nrest_zero_r.
      rewrite <- Nplus_mult_distr_l.
      rewrite (Nplus_comm ys).
      reflexivity.
    }
    {
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nplus_zero_r.
      reflexivity.
    }
    {
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_r.
      repeat rewrite Nplus_zero_l.
      reflexivity.
    }
    {
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nmin_zero_l.
      simpl.
      repeat rewrite Nrest_zero_r.
      rewrite <- Nplus_mult_distr_l.
      rewrite (Nplus_comm yf).
      reflexivity.
    }
    {
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nmin_zero_l.
      simpl.
      repeat rewrite Nrest_zero_r.
      repeat rewrite Nplus_zero_r.
      rewrite <- Nplus_mult_distr_l.
      rewrite (Nplus_comm ys).
      reflexivity.
    }
    {
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_r.
      repeat rewrite Nplus_zero_l.
      reflexivity.
    }
    {
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nplus_zero_r.
      reflexivity.
    }
    {
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_r.
      repeat rewrite Nmin_zero_r.
      repeat rewrite Nrest_zero_l.
      repeat rewrite Nrest_zero_r.
      rewrite <- Nplus_mult_distr_l.
      rewrite (Nplus_comm yf).
      reflexivity.
    }
  Qed.

  Lemma Zplus_mult_distr_r : forall w x y,
    Zmult (Zplus x y) w = Zplus (Zmult x w) (Zmult y w).
  Proof.
    intros w x y.
    rewrite Zmult_comm.
    rewrite Zplus_mult_distr_l.
    rewrite (Zmult_comm w).
    rewrite (Zmult_comm w).
    reflexivity.
  Qed.

  Lemma Zopp_intro : forall x y, x = y -> Zopp x = Zopp y.
  Proof.
    intros x y h. subst y. reflexivity.
  Qed.

  Lemma Zmult_elim_l : forall w x y : ZZ, w <> Zzero -> Zmult w x = Zmult w y -> x = y.
  Proof.
    intros ((wf,ws),hw) ((xf,xs),hx) ((yf,ys),hy).
    intro hneq.
    intro h.
    simpl in h.
    unfold Zmake in h.
    unfold _Zmake in h.
    inversion h as [h'];clear h;rename h' into h.
    unfold _Zcond in hw,hx,hy.
    simpl in hw,hx,hy.
    destruct hw;destruct hx;destruct hy;subst.
    {
      repeat rewrite Nmult_zero_l in h.
      repeat rewrite Nmult_zero_r in h.
      repeat rewrite Nplus_zero_l in h.
      repeat rewrite Nrest_zero_r in h.
      repeat rewrite Nrest_zero_l in h.
      repeat rewrite Nmin_zero_r in h.
      destruct (Neq_dec) in h.
      {
        symmetry in e. apply Nmult_zero in e.
        destruct e;subst.
        {
          contradiction hneq.
          apply proof_irrelevance;simpl. reflexivity.
        }
        {
          repeat rewrite Nmult_zero_r in h.
          destruct (Neq_dec) as [d|d] in h.
          {
            symmetry in d. apply Nmult_zero in d.
            destruct d;subst.
            {
              contradiction hneq.
              apply proof_irrelevance;simpl. reflexivity.
            }
            { apply proof_irrelevance;simpl. reflexivity. }
          }
          { inversion h. contradiction. }
        }
      }
      {
        destruct (Neq_dec) as [d|d].
        {
          symmetry in d. apply Nmult_zero in d.
          destruct d;subst.
          {
            rewrite Nmult_zero_l in n.
            contradiction n. reflexivity.
          }
          {
            rewrite Nmult_zero_r in h.
            inversion h as [h']. symmetry in h'. contradiction.
          }
        }
        {
          apply proof_irrelevance;simpl.
          apply f_eq.
          inversion h as [h'].
          apply Nmult_elim_l with ws.
          {
            intro heq. subst.
            rewrite Nmult_zero_l in *.
            apply n. reflexivity.
          }
          { exact h'. }
        }
      }
    }
    {
      repeat rewrite Nmult_zero_l in h.
      repeat rewrite Nmult_zero_r in h.
      repeat rewrite Nplus_zero_l in h.
      repeat rewrite Nmin_zero_r in h.
      repeat rewrite Nrest_zero_l in h.
      repeat rewrite Nrest_zero_r in h.
      repeat rewrite Nmin_zero_l in h.
      destruct (Neq_dec) as [d|d].
      {
        simpl in h.
        symmetry in d. apply Nmult_zero in d.
        destruct d;subst.
        {
          contradiction hneq.
          apply proof_irrelevance;simpl. reflexivity.
        }
        {
          rewrite Nmult_zero_r in h.
          inversion h.
          symmetry in H0.
          apply Nmult_zero in H0.
          destruct H0;subst.
          {
            contradiction hneq.
            apply proof_irrelevance;simpl. reflexivity.
          }
          { apply proof_irrelevance;simpl. reflexivity. }
        }
      }
      {
        simpl in h.
        inversion h as [(hl,hr)].
        symmetry in hl.
        contradiction.
      }
    }
    {
      repeat rewrite Nmult_zero_l in h.
      repeat rewrite Nmult_zero_r in h.
      repeat rewrite Nplus_zero_l in h.
      repeat rewrite Nmin_zero_l in h.
      repeat rewrite Nrest_zero_r in h.
      repeat rewrite Nrest_zero_l in h.
      repeat rewrite Nmin_zero_r in h.
      destruct (Neq_dec) as [d|d] in h at 2 .
      {
        simpl in h.
        symmetry in d.
        apply Nmult_zero in d.
        destruct d;subst.
        {
          contradiction hneq.
          apply proof_irrelevance;simpl. reflexivity.
        }
        {
          rewrite Nmult_zero_r in h.
          inversion h as [hs].
          apply Nmult_zero in hs.
          destruct hs;subst.
          {
            contradiction hneq.
            apply proof_irrelevance;simpl. reflexivity.
          }
          { apply proof_irrelevance;simpl. reflexivity. }
        }
      }
      { simpl in h. inversion h as [(hf,hs)]. contradiction. }
    }
    {
      repeat rewrite Nmult_zero_l in h.
      repeat rewrite Nmult_zero_r in h.
      repeat rewrite Nplus_zero_l in h.
      repeat rewrite Nmin_zero_l in h.
      simpl in h.
      repeat rewrite Nrest_zero_r in h.
      inversion h as [hs].
      apply Nmult_elim_l in hs.
      {
        subst yf.
        apply proof_irrelevance;simpl. reflexivity.
      }
      {
        intro heq. subst ws.
        apply hneq.
        apply proof_irrelevance;simpl. reflexivity.
      }
    }
    {
      repeat rewrite Nmult_zero_r in h.
      repeat rewrite Nmult_zero_l in h.
      repeat rewrite Nplus_zero_l in h.
      repeat rewrite Nmin_zero_l in h.
      simpl in h.
      repeat rewrite Nplus_zero_r in h.
      repeat rewrite Nrest_zero_r in h.
      inversion h as [hs].
      apply Nmult_elim_l in hs.
      {
        subst ys.
        apply proof_irrelevance;simpl. reflexivity.
      }
      {
        intro heq. subst wf. apply hneq.
        apply proof_irrelevance;simpl. reflexivity.
      }
    }
    {
      repeat rewrite Nmult_zero_r in h.
      repeat rewrite Nmult_zero_l in h.
      repeat rewrite Nplus_zero_l in h.
      repeat rewrite Nplus_zero_r in h.
      repeat rewrite Nmin_zero_l in h.
      repeat rewrite Nmin_zero_r in h.
      repeat rewrite Nrest_zero_r in h.
      repeat rewrite Nrest_zero_l in h.
      destruct (Neq_dec) as [d|d] in h at 2.
      {
        symmetry in d.
        apply Nmult_zero in d.
        destruct d;subst.
        {
          contradiction hneq.
          apply proof_irrelevance;simpl. reflexivity.
        }
        {
          simpl in h.
          rewrite Nmult_zero_r in h.
          inversion h as [hs].
          apply Nmult_zero in hs.
          destruct hs;subst.
          {
            contradiction hneq.
            apply proof_irrelevance;simpl. reflexivity.
          }
          { apply proof_irrelevance;simpl. reflexivity. }
        }
      }
      {
        simpl in h.
        inversion h as [(hf,hs)].
        contradiction.
      }
    }
    {
      repeat rewrite Nmult_zero_l in h.
      repeat rewrite Nmult_zero_r in h.
      repeat rewrite Nplus_zero_l in h.
      repeat rewrite Nplus_zero_r in h.
      repeat rewrite Nmin_zero_r in h.
      repeat rewrite Nrest_zero_l in h.
      repeat rewrite Nrest_zero_r in h.
      repeat rewrite Nmin_zero_l in h.
      destruct (Neq_dec) as [d|d] in h.
      {
        simpl in h.
        symmetry in d.
        apply Nmult_zero in d.
        destruct d;subst.
        {
          contradiction hneq.
          apply proof_irrelevance;simpl. reflexivity.
        }
        {
          rewrite Nmult_zero_r in h.
          inversion h as [hs].
          symmetry in hs.
          apply Nmult_zero in hs.
          destruct hs;subst.
          {
            contradiction hneq.
            apply proof_irrelevance;simpl. reflexivity.
          }
          { apply proof_irrelevance;simpl. reflexivity. }
        }
      }
      {
        simpl in h.
        inversion h as [(hf,hs)].
        symmetry in hf.
        contradiction.
      }
    }
    {
      repeat rewrite Nmult_zero_l in h.
      repeat rewrite Nmult_zero_r in h.
      repeat rewrite Nplus_zero_r in h.
      repeat rewrite Nmin_zero_r in h.
      repeat rewrite Nrest_zero_l in h.
      repeat rewrite Nrest_zero_r in h.
      destruct (Neq_dec) as [d|d].
      {
        symmetry in d.
        apply Nmult_zero in d.
        destruct d;subst.
        {
          contradiction hneq.
          apply proof_irrelevance;simpl. reflexivity.
        }
        {
          rewrite Nmult_zero_r in h.
          destruct (Neq_dec) as [d|d].
          {
            symmetry in d.
            apply Nmult_zero in d.
            destruct d;subst.
            {
              contradiction hneq.
              apply proof_irrelevance;simpl. reflexivity.
            }
            { apply proof_irrelevance;simpl. reflexivity. }
          }
          { inversion h as [hf]. contradiction. }
        }
      }
      {
        destruct (Neq_dec) as [d'|d'].
        {
          symmetry in d'.
          apply Nmult_zero in d'.
          destruct d';subst.
          {
            rewrite Nmult_zero_l in d.
            contradiction d. reflexivity.
          }
          {
            rewrite Nmult_zero_r in h.
            inversion h as [hf].
            symmetry in hf.
            contradiction.
          }
        }
        {
          inversion h as [hf].
          apply Nmult_elim_l in hf.
          {
            subst yf.
            apply proof_irrelevance;simpl. reflexivity.
          }
          {
            intro heq. subst.
            repeat rewrite Nmult_zero_l in *.
            contradiction.
          }
        }
      }
    }
  Qed.

  Lemma Zle_zero_mult : forall x y:ZZ, Zle Zzero x -> Zle Zzero y -> Zle Zzero (Zmult x y).
  Proof.
    intros ((xf,xs),hx) ((yf,ys),hy).
    unfold _Zcond in hx,hy.
    simpl in hx,hy.
    simpl.
    destruct hx;destruct hy;subst.
    {
      intros [_ hxs] [_ hys].
      apply Nle_zero_r in hxs,hys.
      subst.
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nmin_zero_r.
      repeat rewrite Nrest_zero_l.
      simpl.
      split;apply Nle_refl.
    }
    {
      intros [_ hxs] [hyf _].
      apply Nle_zero_r in hxs. subst.
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nplus_zero_r.
      repeat rewrite Nmin_zero_l.
      simpl.
      split. apply Nle_refl.
      unfold Nle. simpl. trivial.
    }
    {
      intros [hxf _] [_ hys].
      apply Nle_zero_r in hys. subst.
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_r.
      rewrite Nmin_cancel.
      simpl.
      split.
      apply Nle_refl.
      unfold Nle. simpl. trivial.
    }
    {
      intros [hxf _] [hyf _].
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nplus_zero_r.
      rewrite Nmin_zero_r.
      rewrite Nrest_zero_l.
      rewrite Nrest_zero_r.
      destruct (Neq_dec) as [d|d].
      {
        rewrite <- d.
        split;apply Nle_refl.
      }
      { split. apply Nle_zero_l. apply Nle_refl. }
    }
  Qed.

  Lemma Zopp_elim : forall x y, Zopp x = Zopp y -> x = y.
  Proof.
    intros x y h.
    apply Zopp_intro in h.
    rewrite Zopp_involutive in h.
    rewrite Zopp_involutive in h.
    exact h.
  Qed.

  Lemma Zplus_intro_l : forall w x y, x = y -> Zplus w x = Zplus w y.
  Proof.
    intros w x y h. subst y. reflexivity.
  Qed.

  Lemma Zplus_intro_r : forall w x y , x = y -> Zplus x w = Zplus y w.
  Proof.
    intros w x y h. subst y. reflexivity.
  Qed.

  Lemma Zmult_intro_l : forall w x y, x = y -> Zmult w x = Zmult w y.
  Proof.
    intros w x y h. subst y. reflexivity.
  Qed.

  Lemma Zmult_intro_r : forall w x y, x = y -> Zmult x w = Zmult y w.
  Proof.
    intros w x y h. subst y. reflexivity.
  Qed.

  Lemma Zplus_elim_r : forall w x y, Zplus x w = Zplus y w -> x = y.
  Proof.
    intros w x y h.
    apply (Zplus_intro_r (Zopp w)) in h .
    rewrite Zplus_assoc in h.
    rewrite Zplus_assoc in h.
    rewrite Zplus_opp_r in h.
    rewrite Zplus_zero_r in h.
    rewrite Zplus_zero_r in h.
    exact h.
  Qed.

  Lemma Zplus_elim_l : forall w x y, Zplus w x = Zplus w y -> x = y.
  Proof.
    intros w x y h.
    apply Zplus_elim_r with w.
    rewrite (Zplus_comm x).
    rewrite (Zplus_comm y).
    exact h.
  Qed.

  Lemma Zplus_zero : forall x y, Zplus x y = Zzero -> x = Zopp y.
  Proof.
    intros x y h.
    apply Zplus_elim_r with y.
    rewrite Zplus_opp_l.
    exact h.
  Qed.


  Lemma Zmult_elim_r : forall w x y : ZZ, w <> Zzero -> Zmult x w = Zmult y w -> x = y.
  Proof.
    intros w x y hneq heq.
    apply Zmult_elim_l with w.
    exact hneq.
    repeat rewrite (Zmult_comm w).
    exact heq.
  Qed.

  Lemma Zmult_zero : forall x y, Zmult x y = Zzero -> x = Zzero \/ y = Zzero.
  Proof.
    intros x y heq.
    destruct (Zeq_dec x Zzero) as [dx|dx].
    (* x = 0 : ok *)
    subst x. left. reflexivity.
    destruct (Zeq_dec y Zzero) as [dy|dy].
    (* y = 0 : ok *)
    subst y. right. reflexivity.
    (* x <> 0 and y <> 0 => contradiction *)
    contradiction dy.
    apply Zmult_elim_l with x.
    { exact dx. }
    {
      rewrite Zmult_zero_r.
      rewrite heq.
      reflexivity.
    }
  Qed.

  Lemma Zopp_zero : Zopp Zzero = Zzero.
  Proof.
    unfold Zopp. rewrite Zmult_zero_l. reflexivity.
  Qed.

  Lemma Zopp_one: Zopp Zone = Zone_opp.
  Proof.
    unfold Zopp.
    rewrite Zmult_one_l.
    reflexivity.
  Qed.

  Lemma Zopp_oneopp : Zopp Zone_opp = Zone.
  Proof.
    apply Zopp_elim.
    rewrite Zopp_involutive.
    rewrite Zopp_one.
    reflexivity.
  Qed.

  Lemma Zopp_plus_distr: forall x y:ZZ, Zopp (Zplus x y) = Zplus (Zopp x) (Zopp y).
  Proof.
    intros x y.
    unfold Zopp.
    rewrite Zplus_mult_distr_r.
    reflexivity.
  Qed.

  Lemma Zopp_mult_distr_l : forall x y:ZZ, Zopp (Zmult x y) = Zmult (Zopp x) y.
  Proof.
    intros x y.
    unfold Zopp.
    repeat rewrite Zmult_assoc.
    rewrite (Zmult_comm y).
    reflexivity.
  Qed.

  Lemma Zopp_mult_distr_r : forall x y:ZZ, Zopp (Zmult x y) = Zmult x (Zopp y).
  Proof.
    intros x y.
    rewrite Zmult_comm.
    rewrite Zopp_mult_distr_l.
    rewrite Zmult_comm.
    reflexivity.
  Qed.

  Lemma Ztrichotomy : forall x y:ZZ, Zlt x y \/ x = y \/ Zlt y x.
  Proof.
    intros x y.
    destruct (Zeq_dec x y).
    { subst y. right. left. reflexivity. }
    destruct (Zle_dec x y).
    { left. unfold Zlt. split;assumption. }
    {
      right. right. unfold Zlt. split.
      { assumption. }
      { unfold not. intro heq. subst y. contradiction. }
    }
  Qed.

Search Zle.

Lemma Zle_plus_intro_l: forall w x y : ZZ, Zle x y -> Zle (Zplus w x) (Zplus w y).
intros ((wf,ws),hw) ((xf,xs),hx) ((yf,ys),hy) [hl hr].
unfold _Zcond in hw,hx,hy.
simpl in hw,hx,hy.
simpl.
destruct hw,hx,hy;subst.
{
repeat rewrite Nplus_zero_l.
repeat rewrite Nmin_zero_l.
simpl.
repeat rewrite Nrest_zero_r.
split.
apply Nle_refl.
apply Nle_plus_intro_l.
exact hr.
}
{
repeat rewrite Nplus_zero_l.
repeat rewrite Nplus_zero_r.
repeat rewrite Nmin_zero_l.
simpl.
destruct (Neq_dec) as [d|d].
{
rewrite Nrest_zero_r.
apply Nmin_le in d.
split.
{ apply Nle_refl. }
{
apply Nle_nmk in d.
destruct d as [k heqk].
subst ws.
rewrite (Nplus_comm yf).
rewrite Nrest_plus_nmm.
rewrite <- Nplus_assoc.
pattern k at 1;rewrite <- Nplus_zero_r.
apply Nle_plus_intro_l.
apply Nle_zero_l.
}
}
{
split.
apply Nle_zero_l.
apply Nle_zero_l.
}
}
{
apply Nle_zero_r in hl.
apply Nle_zero_r in hr.
subst.
repeat rewrite Nplus_zero_l.
repeat rewrite Nplus_zero_r.
repeat rewrite Nmin_zero_l.
simpl.
rewrite Nrest_zero_r.
split.
{ apply Nle_refl. }
{ apply Nle_refl. }
}
{
repeat rewrite Nplus_zero_l.
repeat rewrite Nplus_zero_r.
destruct (Neq_dec) as [d1|d1].
{
apply Nmin_le in d1.
destruct (Neq_dec) as [d2|d2].
{
apply Nmin_le in d2.
split.
{ apply Nle_refl. }
{
clear hr.
apply Nle_nmk in d1. destruct d1 as [k1 heqk1].
apply Nle_nmk in d2. destruct d2 as [k2 heqk2].
pattern ws at 1;rewrite <- heqk2.
rewrite <- heqk1.
rewrite (Nplus_comm yf).
rewrite (Nplus_comm xf).
rewrite Nrest_plus_nmm.
rewrite Nrest_plus_nmm.
apply Nle_plus_elim_l with yf.
rewrite heqk2.
apply Nle_plus_elim_r with xf.
rewrite <- Nplus_assoc.
rewrite (Nplus_comm k1).
rewrite heqk1.
rewrite Nplus_comm.
apply Nle_plus_intro_r.
exact hl.
}
}
{
split.
apply Nle_zero_l.
apply Nle_zero_l.
}
}
{
clear hr.
apply Nmin_neq_le in d1.
destruct (Neq_dec) as [d2|d2].
{
apply Nmin_le in d2.
assert (heq:xf=yf).
{
eapply Nle_antisym.
apply hl.
eapply Nle_trans.
apply d2.
apply d1.
}
subst yf.
clear hl.
assert (heq:=Nle_antisym _ _ d1 d2).
subst xf.
rewrite Nrest_cancel.
split;apply Nle_refl.
}
{
apply Nmin_neq_le in d2.
split.
{
apply Nle_nmk in d1, d2.
destruct d1 as [k1 heqk1].
destruct d2 as [k2 heqk2].
rewrite <- heqk1.
rewrite <- heqk2.
repeat rewrite (Nplus_comm ws).
repeat rewrite Nrest_plus_nmm.
apply Nle_plus_elim_l with ws.
rewrite heqk1.
rewrite heqk2.
exact hl.
}
{ apply Nle_refl. }
}
}
}
{
clear hl.
repeat rewrite Nplus_zero_r.
repeat rewrite Nplus_zero_l.
destruct (Neq_dec) as [d1|d1].
{
apply Nmin_le in d1.
destruct (Neq_dec) as [d2|d2].
{
apply Nmin_le in d2.
split.
{ apply Nle_refl. }
{
apply Nle_nmk in d1,d2.
destruct d1 as [k1 heqk1].
destruct d2 as [k2 heqk2].
rewrite <- heqk1.
rewrite <- heqk2.
repeat rewrite (Nplus_comm wf).
repeat rewrite Nrest_plus_nmm.
apply Nle_plus_elim_l with wf.
rewrite heqk1,heqk2.
exact hr.
}
}
{
split;apply Nle_zero_l.
}
}
{
apply Nmin_neq_le in d1.
destruct (Neq_dec) as [d2|d2].
{
apply Nmin_le in d2.
assert (heq:xs=ys).
{
apply Nle_antisym.
eapply Nle_trans.
apply d1.
apply d2.
apply hr.
}
subst ys.
clear hr.
assert (heq:=Nle_antisym _ _ d1 d2).
subst xs.
rewrite Nrest_cancel.
split;apply Nle_refl.
}
{
apply Nmin_neq_le in d2.
split.
{
apply Nle_nmk in d1,d2.
destruct d1 as [k1 heqk1].
destruct d2 as [k2 heqk2].
pattern wf at 1;rewrite <- heqk1.
rewrite <- heqk2.
rewrite (Nplus_comm xs).
rewrite (Nplus_comm ys).
repeat rewrite Nrest_plus_nmm.
apply Nle_plus_elim_l with xs.
rewrite heqk1.
rewrite Nplus_comm.
apply Nle_plus_elim_l with ys.
rewrite Nplus_assoc.
rewrite heqk2.
rewrite Nplus_comm.
apply Nle_plus_intro_l.
exact hr.
}
{ apply Nle_refl. }
}
}
}
{
repeat rewrite Nplus_zero_r.
repeat rewrite Nplus_zero_l.
repeat rewrite Nmin_zero_r.
repeat rewrite Nrest_zero_l.
repeat rewrite Nrest_zero_r.
destruct (Neq_dec) as [d1|d1].
{
apply Nmin_le in d1.
destruct (Neq_dec) as [d2|d2].
{
symmetry in d2.
apply Nplus_zero in d2.
destruct d2.
subst wf yf.
split.
apply Nle_refl.
rewrite Nplus_zero_l.
rewrite Nrest_zero_r.
exact hr.
}
{
split;apply Nle_zero_l.
}
}
{
apply Nmin_neq_le in d1.
destruct (Neq_dec) as [d2|d2].
{
symmetry in d2.
apply Nplus_zero in d2.
destruct d2. subst wf yf.
apply Nle_zero_r in d1. subst xs.
rewrite Nrest_cancel.
rewrite Nplus_zero_l.
split;apply Nle_refl.
}
{
split.
{
apply Nle_nmk in d1.
destruct d1 as [k1 heqk1].
subst wf.
rewrite (Nplus_comm xs).
rewrite Nrest_plus_nmm.
rewrite <- Nplus_assoc.
pattern k1 at 1;rewrite <- Nplus_zero_r.
apply Nle_plus_intro_l.
apply Nle_zero_l.
}
{ apply Nle_refl. }
}
}
}
{
apply Nle_zero_r in hl,hr.
subst xf ys.
repeat rewrite Nplus_zero_l.
repeat rewrite Nplus_zero_r.
repeat rewrite Nmin_zero_r.
repeat rewrite Nrest_zero_l.
repeat rewrite Nrest_zero_r.
destruct (Neq_dec) as [d|d].
{ split;apply Nle_refl. }
{ split;apply Nle_refl. }
}
{
repeat rewrite Nplus_zero_l.
repeat rewrite Nmin_zero_r.
repeat rewrite Nrest_zero_l.
repeat rewrite Nrest_zero_r.
clear hr.
destruct (Neq_dec) as [d1|d1].
{
symmetry in d1.
apply Nplus_zero in d1.
destruct d1;subst.
repeat rewrite Nplus_zero_l.
destruct (Neq_dec) as [d2|d2].
{
subst yf.
split;apply Nle_refl.
}
{ split;apply Nle_zero_l. }
}
{
destruct (Neq_dec) as [d2|d2].
{
symmetry in d2.
apply Nplus_zero in d2.
destruct d2;subst.
repeat rewrite Nplus_zero_l.
split. assumption. apply Nle_refl.
}
{
split.
apply Nle_plus_intro_l. exact hl.
apply Nle_refl.
}
}
}
Qed.

  Lemma Zle_plus_intro_r: forall w x y : ZZ, Zle x y -> Zle (Zplus x w) (Zplus y w).
  Proof.
    intros w x y h.
    rewrite (Zplus_comm x).
    rewrite (Zplus_comm y).
    apply Zle_plus_intro_l.
    exact h.
  Qed.

  Lemma Zle_plus_elim_l: forall w x y : ZZ, Zle (Zplus x w) (Zplus y w) -> Zle x y.
  Proof.
    intros w x y h.
    pattern x;rewrite <- Zplus_zero_r.
    pattern y;rewrite <- Zplus_zero_r.
    rewrite <- Zplus_opp_r with w.
    repeat rewrite <- Zplus_assoc.
    apply Zle_plus_intro_r.
    exact h.
  Qed.

  Lemma Zle_plus_elim_r: forall w x y : ZZ, Zle (Zplus w x) (Zplus w y) -> Zle x y.
  Proof.
    intros w x y h.
    apply Zle_plus_elim_l with w.
    repeat rewrite (Zplus_comm _ w).
    exact h.
  Qed.

  Lemma Zle_zero_one : Zle Zzero Zone.
  Proof.
    simpl. split;apply Nle_zero_l.
  Qed.

  Lemma Zle_oneopp_zero : Zle Zone_opp Zzero.
  Proof.
    simpl. split;apply Nle_zero_l.
  Qed.


  Lemma Zle_zero_plus: forall x y:ZZ, Zle Zzero x -> Zle Zzero y -> Zle Zzero (Zplus x y).
  Proof.
    intros x y hx hy.
    apply (Zle_plus_intro_r y) in hx.
    rewrite Zplus_zero_l in hx.
    apply Zle_trans with y.
    exact hy.
    exact hx.
  Qed.

  Lemma Zle_mult_intro_l: forall w x y, Zle x y -> Zle Zzero w -> Zle (Zmult w x) (Zmult w y).
  Proof.
    intros ((wf,ws),hw) ((xf,xs),hx) ((yf,ys),hy).
    unfold _Zcond in hw,hx,hy.
    simpl in hw,hx,hy.
    simpl.
    intros [hl hr].
    intros [hwl hwr].
    apply Nle_zero_r in hwr. subst ws.
    repeat rewrite Nmult_zero_l.
    repeat rewrite Nplus_zero_r.
    destruct hw as [hw|hw];subst.
    {
      repeat rewrite Nmult_zero_l.
      repeat rewrite Nrest_cancel.
      repeat rewrite Nmin_zero_l.
      simpl.
      split;apply Nle_refl.
    }
    {
      clear hw.
      destruct hx;destruct hy;subst.
      {
        repeat rewrite Nmult_zero_r.
        repeat rewrite Nmin_zero_l.
        simpl.
        repeat rewrite Nrest_zero_r.
        split. apply Nle_refl.
        clear hl.
        apply Nle_mult_intro_l.
        exact hr.
      }
      {
        repeat rewrite Nmult_zero_r.
        repeat rewrite Nmin_zero_l.
        repeat rewrite Nmin_zero_r.
        repeat rewrite Nrest_zero_r.
        repeat rewrite Nrest_zero_l.
        destruct (Neq_dec) as [d|d] at 2 .
        {
          simpl.
          split. apply Nle_refl.
          symmetry in d.
          apply Nmult_zero in d.
          destruct d;subst.
          repeat rewrite Nmult_zero_l. apply Nle_refl.
          rewrite Nmult_zero_r. apply Nle_zero_l.
        }
        {
          simpl.
          split;apply Nle_zero_l.
        }
      }
      {
        apply Nle_zero_r in hl,hr. subst xf ys.
        repeat rewrite Nmult_zero_r.
        simpl.
        split. apply Nle_refl.
        apply Nle_refl.
      }
      {
        clear hr.
        repeat rewrite Nmult_zero_r.
        repeat rewrite Nmin_zero_r.
        repeat rewrite Nrest_zero_l.
        repeat rewrite Nrest_zero_r.
        destruct (Neq_dec) as [d1|d1].
        {
          symmetry in d1.
          apply Nmult_zero in d1.
          destruct d1;subst.
          {
            repeat rewrite Nmult_zero_l.
            simpl.
            split;apply Nle_refl.
          }
          {
            repeat rewrite Nmult_zero_r.
            destruct (Neq_dec) as [d|d].
            {
              symmetry in d.
              apply Nmult_zero in d.
              destruct d;subst.
              {
                rewrite Nmult_zero_l.
                split;apply Nle_refl.
              }
              {
                rewrite Nmult_zero_r.
                split;apply Nle_refl.
              }
            }
            { split;apply Nle_zero_l. }
          }
        }
        {
          destruct (Neq_dec) as [d2|d2].
          {
            symmetry in d2.
            apply Nmult_zero in d2.
            destruct d2;subst.
            { repeat rewrite Nmult_zero_l. split;apply Nle_refl. }
            {
              apply Nle_zero_r in hl. subst xf.
              repeat rewrite Nmult_zero_r.
              split;apply Nle_refl.
            }
          }
          {
            split.
            apply Nle_mult_intro_l. exact hl.
            apply Nle_refl.
          }
        }
      }
    }
  Qed.

  Lemma Zle_mult_intro_r: forall w x y, Zle x y -> Zle Zzero w -> Zle (Zmult x w) (Zmult y w).
  Proof.
    intros w x y hxy hw.
    repeat rewrite (Zmult_comm _ w).
    apply Zle_mult_intro_l.
    exact hxy. exact hw.
  Qed.

  Lemma Zle_mult_elim_l: forall w x y, Zlt Zzero w -> Zle (Zmult w x) (Zmult w y) -> Zle x y.
intros w x y hw hle.
unfold Zlt in hw.
destruct hw as [hlew hneqw].
destruct w as [ [wf ws ] hw];
destruct x as [ [xf xs ] hx];
destruct y as [ [yf ys ] hy].
simpl.
unfold _Zcond in hw,hx,hy.
simpl in hw,hx,hy.
simpl in hlew.
simpl in hle.
destruct hlew as [hlewf hlews].
apply Nle_zero_r in hlews.
subst ws.
repeat rewrite Nmult_zero_l in hle.
repeat rewrite Nplus_zero_r in hle.
destruct hw as [hw|hw].
{
subst wf.
repeat rewrite Nmult_zero_l in hle.
repeat rewrite Nmin_zero_r in hle.
simpl in hle.
clear hle.
clear hlewf.
contradiction hneqw.
apply proof_irrelevance.
simpl.
reflexivity.
}
{
clear hlewf.
destruct hx as [hx|hx];destruct hy as [hy|hy].
{
subst xf yf.
repeat rewrite Nmult_zero_r in hle.
repeat rewrite Nmin_zero_l in hle.
simpl in hle.
destruct hle as [_ hle].
repeat rewrite Nrest_zero_r in hle.
apply Nle_mult_elim_l in hle.
split. apply Nle_refl. exact hle.
intro heq. subst wf. apply hneqw. apply proof_irrelevance. simpl. reflexivity.
}
{
subst xf ys.
split;apply Nle_zero_l.
}
{
subst xs yf.
repeat rewrite Nmult_zero_r in hle.
repeat rewrite Nmin_zero_r in hle.
repeat rewrite Nrest_zero_l in hle.
repeat rewrite Nrest_zero_r in hle.
repeat rewrite Nmin_zero_l in hle.
destruct (Neq_dec) as [d|d] in hle .
{
symmetry in d.
apply Nmult_zero in d.
destruct d as [d|d].
{
subst wf.
contradiction hneqw.
apply proof_irrelevance. simpl. reflexivity.
}
{
subst xf.
repeat rewrite Nmult_zero_r in hle.
simpl in hle.
destruct hle as [_ hle].
apply Nle_zero_r in hle.
apply Nmult_zero in hle.
destruct hle as [hle|hle].
{
subst wf. contradiction hneqw. apply proof_irrelevance. simpl. reflexivity.
}
{
subst ys. split;apply Nle_refl.
}
}
}
{
simpl in hle.
destruct hle as [hlel hler].
apply Nle_zero_r in hlel, hler.
apply Nmult_zero in hlel, hler.
destruct hlel as [hlel|hlel].
{
subst wf. contradiction hneqw. apply proof_irrelevance. simpl. reflexivity.
}
{
subst xf.
rewrite Nmult_zero_r in d.
contradiction d.
}
}
}
{
subst xs ys.
repeat rewrite Nmult_zero_r in hle.
repeat rewrite Nmin_zero_r in hle.
repeat rewrite Nrest_zero_l in hle.
repeat rewrite Nrest_zero_r in hle.
destruct (Neq_dec) as [d1|d1].
{
symmetry in d1.
apply Nmult_zero in d1.
destruct d1 as [d1|d1].
{
subst wf. contradiction hneqw. apply proof_irrelevance. simpl. reflexivity.
}
{
subst xf.
split;apply Nle_zero_l.
}
}
{
destruct (Neq_dec) as [d2|d2].
{
symmetry in d2.
apply Nmult_zero in d2.
destruct d2 as [d2|d2].
{
subst wf. contradiction hneqw. apply proof_irrelevance. simpl. reflexivity.
}
{
subst yf.
rewrite Nmult_zero_r in hle.
destruct hle as [hle _].
apply Nle_zero_r in hle.
apply Nmult_zero in hle.
destruct hle as [hle|hle].
{
subst wf. contradiction hneqw. apply proof_irrelevance. simpl. reflexivity.
}
{
subst xf.
split;apply Nle_refl.
}
}
}
{
destruct hle as [hle _].
apply Nle_mult_elim_l in hle.
split.
exact hle.
apply Nle_refl.
intro heq. subst wf.
contradiction hneqw. apply proof_irrelevance. simpl. reflexivity.
}
}
}
}
Qed.


  Lemma Zle_mult_elim_r: forall w x y, Zlt Zzero w -> Zle (Zmult x w) (Zmult y w) -> Zle x y.
  Proof.
    intros w x y hlt hle.
    apply Zle_mult_elim_l with w.
    exact hlt.
    repeat rewrite (Zmult_comm w).
    exact hle.
  Qed.

  Definition Zabs x := if Zle_dec Zzero x then x else Zopp x.

  Lemma  Zle_opp : forall x y, Zle x y -> Zle (Zopp y) (Zopp x).
  Proof.
    intros ((xf,xs),hx) ((yf,ys),hy) h.
    unfold Zopp.
    destruct Zone_opp as ((xof,xos),xoh) eqn:heqxo.
    red in hx,hy.
    simpl in hx,hy.
    inversion heqxo.
    subst xof xos.
    simpl.
    repeat rewrite Nmult_zero_r.
    repeat rewrite Nplus_zero_l.
    repeat rewrite Nmult_one_r.
    repeat rewrite Nplus_zero_r.
    clear heqxo. clear xoh.
    simpl in h.
    destruct hx;destruct hy;subst.
    {
      repeat rewrite Nmin_zero_r.
      repeat rewrite Nrest_zero_l.
      repeat rewrite Nrest_zero_r.
      destruct (Neq_dec) as [d|d] at 2.
      {
        subst xs.
        destruct h as [_ h].
        apply Nle_zero_r in h.
        subst ys.
        simpl.
        split;apply Nle_refl.
      }
      {
        destruct (Neq_dec) as [dy|dy].
        { subst. split;apply Nle_zero_l. }
        { destruct h as [_ h]. split. exact h. apply Nle_refl. }
      }
    }
    {
      clear h.
      repeat rewrite Nmin_zero_r.
      repeat rewrite Nmin_zero_l.
      repeat rewrite Nrest_zero_r.
      repeat rewrite Nrest_zero_l.
      destruct (Neq_dec) as [d|d] at 2.
      { subst xs. simpl. split;apply Nle_zero_l. }
      { simpl. split;apply Nle_zero_l. }
    }
    {
      destruct h as [hl hr].
      apply Nle_zero_r in hl,hr.
      subst.
      repeat rewrite Nmin_zero_l.
      simpl.
      split;apply Nle_refl.
    }
    {
      destruct h as [h _].
      repeat rewrite Nmin_zero_l.
      simpl.
      repeat rewrite Nrest_zero_r.
      split.
      apply Nle_refl.
      exact h.
    }
  Qed.

  Lemma Zabs_pos : forall x:ZZ, Zle Zzero (Zabs x).
  Proof.
    intro x.
    unfold Zabs.
    destruct (Zle_dec) as [d|d].
    { exact d. }
    {
      rewrite <- Zopp_zero.
      apply Zle_opp.
      exact d.
    }
  Qed.

  Definition _NtoZ (n:NN) : (PairOf NN) := pair n Nzero.

  Lemma _NtoZ_ok : forall (n:NN), _Zcond (_NtoZ n).
  Proof.
    intro n.
    red.
    unfold _NtoZ.
    simpl.
    right.
    reflexivity.
  Qed.
  
  Definition NtoZ (n:NN) : ZZ := exist _ (_NtoZ n) (_NtoZ_ok n).

  Lemma NtoZ_pos : forall n:NN, Zle Zzero (NtoZ n).
  Proof.
    intro n.
    unfold NtoZ.
    simpl.
    split;apply Nle_zero_l.
  Qed.

  Definition ZtoN (x:ZZ) : NN := first (proj1_sig (Zabs x)).

  Lemma NtoZtoN : forall n:NN, n = ZtoN (NtoZ n).
  Proof.
    intro n.
    unfold NtoZ.
    unfold ZtoN.
    unfold Zabs.
    destruct (Zle_dec) as [d|d].
    {
      simpl.
      reflexivity.
    }
    {
      simpl in d.
      destruct d as [d _].
      apply Nle_zero_r in d.
      subst n.
      simpl.
      reflexivity.
    }
  Qed.

  Lemma ZtoNtoZ : forall x:ZZ, Zle Zzero x -> x = NtoZ (ZtoN x).
  Proof.
    intros ((xf,xs),hx) hle.
    simpl in hle.
    destruct hle as [hl hr].
    apply Nle_zero_r in hr.
    subst xs.
    apply proof_irrelevance.
    simpl.
    unfold _NtoZ.
    f_equal.
    red in hx.
    simpl in hx.
    unfold ZtoN.
    unfold Zabs.
    destruct (Zle_dec) as [d|d].
    {
      simpl. reflexivity.
    }
    {
      simpl in d.
      destruct d as [d _].
      apply Nle_zero_r in d.
      subst xf.
      simpl.
      reflexivity.
    }
  Qed.

  Definition Zsign (x:ZZ) := if Zle_dec Zzero x then Zone else Zone_opp.

  Lemma Zabs_sign : forall x:ZZ, x = Zmult (Zsign x) (Zabs x).
  Proof.
    intros x.
    unfold Zsign.
    unfold Zabs.
    destruct (Zle_dec) as [d|d].
    {
      rewrite Zmult_one_l.
      reflexivity.
    }
    {
      unfold Zopp.
      rewrite (Zmult_comm x).
      rewrite <- Zmult_assoc.
      rewrite Zmult_oneopp.
      rewrite Zmult_one_l.
      reflexivity.
    }
  Qed.

  Lemma Nle_neq_lt : forall x y, Nle x y -> x <> y -> Nlt x y.
Proof.
intro x.
induction x as [|x ih] using Ninduction.
{
intros y _ hneq.
red.
induction y as [|y _] using Ninduction.
{ contradiction hneq. reflexivity. }
{ apply Nle_next_intro. apply Nle_zero_l. }
}
{
intro y.
induction y as [|y _] using Ninduction.
{ intro h. inversion h. }
{
intros hle hneq.
apply Nle_next_elim in hle.
red.
apply Nle_next_intro.
apply ih.
exact hle.
intro heq. subst y. contradiction hneq. reflexivity.
}
}
Qed.

  Definition _NEuclidPair := @Pair NN NN.

  Definition _NEuclidLe (p1 p2:_NEuclidPair) :=
    let (pf1,ps1) := p1 in
    let (pf2,ps2) := p2 in
    Nle pf1 pf2 /\ Nle ps1 ps2.

  Definition _NEuclidLt (p1 p2:_NEuclidPair) :=
    let (pf1,ps1) := p1 in
    let (pf2,ps2) := p2 in
    _NEuclidLe p1 p2 /\ (pf1 <> pf2 \/ ps1 <> ps2 ).


  Lemma pair_neq:forall a b c d:NN, pair a b <> pair c d ->
    (a <> c /\ b = d) \/
    (a = c /\ b <> d) \/
    (a <> c /\ b <> d).
  Proof.
    intros a b c d hneq.
    destruct (Neq_dec a c) as [df|df];
    destruct (Neq_dec b d) as [ds|ds].
    { subst. contradiction hneq. reflexivity. }
    { right. left. split;assumption. }
    { left. split;assumption. }
    { right. right. split;assumption. }
  Qed.

  Lemma Nnext_neq : forall x, x = Nnext x -> False.
  Proof.
    intro x.
    induction x as [|x ih] using Ninduction.
    { intro heq. inversion heq. }
    { intro heq. apply Nnext_elim in heq. apply ih. exact heq. }
  Qed.



  Lemma _NEuclidLt_wf: well_founded _NEuclidLt.
  Proof.
    red.
    intros (xf,xs).
    generalize dependent xs.
    induction xf as [|xf ih] using Ninduction.
    {
      intros xs.
      induction xs as [|xs ih] using Ninduction.
      {
        constructor.
        intros (yf,ys) [ [hyf hys] hyneq].
        apply Nle_zero_r in hyf,hys.
        subst yf ys.
        destruct hyneq as [ hyneq  | hyneq ] .
        contradiction hyneq. reflexivity.
        contradiction hyneq. reflexivity.
      }
      {
        constructor.
        intros (yf,ys)  [ [ hyf hys ] hyneq ].
        apply Nle_zero_r in hyf.
        subst yf.
        destruct hyneq as [ hyneq | hyneq ] .
        { contradiction hyneq. reflexivity. }
        assert (hylt:=Nle_neq_lt _ _ hys hyneq).
        clear hys hyneq. red in hylt. apply Nle_next_elim in hylt.
        constructor. intros (zf,zs) [ [ hzf hzs ] hzneq ].
        apply Nle_zero_r in hzf. subst zf.
        destruct hzneq as [ hzneq | hzneq ] .
        { contradiction hzneq. reflexivity. }
        assert (hzlt:=Nle_neq_lt _ _ hzs hzneq).
        clear hzs hzneq. red in hzlt.
        inversion ih as [ih']. clear ih.
        apply ih'. red. split. red. split.
        apply Nle_refl.
        apply Nle_trans with (Nnext zs). apply Nle_next.
        apply Nle_trans with ys. exact hzlt. exact hylt.
        right. intro heq. subst zs.
        apply (Nlt_irrefl xs). red.
        apply Nle_trans with ys. exact hzlt. exact hylt.
      }
    }
    (* xf induction *)
    {
      intros xs.
      (* xs induction *)
      induction xs as [|xs ihs] using Ninduction.
      (* xs = 0 *)
      {
        constructor.
        intros (yf,ys) [ [ hyf hys ] hyneq ].
        apply Nle_zero_r in hys.
        subst ys.
        (* y left side not equal *)
        destruct hyneq as [hyneq|hyneq].
        {
          assert (hylt:=Nle_neq_lt _ _ hyf hyneq). clear hyf hyneq.
          red in hylt.
          constructor.
          intros (zf,zs) [ [ hzf hzs ] hzneq ].
          apply Nle_zero_r in hzs.
          subst zs.
          destruct hzneq as [ hzneq | hzneq ].
          (* z lef side not equal *)
          {
            assert (hzlt:=Nle_neq_lt _ _ hzf hzneq).
            clear hzf hzneq.
            red in hzlt.
            specialize (ih Nzero).
            inversion ih as [ih'].
            clear ih.
            apply ih'.
            clear ih'.
            red. split. red. split.
            {
              apply Nle_next_elim in hylt.
              apply Nle_trans with (Nnext zf).
              apply Nle_next.
              apply Nle_trans with yf.
              exact hzlt.
              exact hylt.
            }
            { apply Nle_refl. }
            {
              left.
              intro heq.
              subst zf.
              apply Nle_next_elim in hylt.
              apply (Nlt_irrefl xf).
              red.
              apply Nle_trans with yf.
              exact hzlt.
              exact hylt.
            }
          }
          (* z right side not equal (clamped to 0 because xs = 0 *)
          { contradiction hzneq.  reflexivity. }
        }
        (* y right side not equal (clamped to 0 because xs = 0 *)
        { contradiction hyneq. reflexivity. }
      }
      (* xs induction *)
      {
        inversion ihs as [ihs'].
        clear ihs.
        constructor.
        intros (yf,ys) [ [hyf hys] hyneq].
        destruct hyneq as [hyneq|hyneq].
        (* y left side not equal *)
        {
          assert (hylt:=Nle_neq_lt _ _ hyf hyneq).
          clear hyf hyneq.
          red in hylt.
          apply Nle_next_elim in hylt.
          constructor.
          intros (zf,zs) [ [ hzf hzs ] hzneq ].
          destruct hzneq as [ hzneq | hzneq ].
          (* z left side not equal *)
          {
            assert (hzlt:=Nle_neq_lt _ _ hzf hzneq).
            clear hzf hzneq.
            red in hzlt.
            specialize (ih zs).
            inversion ih as [ih'].
            clear ih.
            apply ih'.
            clear ih'.
            red. split. red. split.
            {
              apply Nle_trans with (Nnext zf).
              apply Nle_next.
              apply Nle_trans with yf.
              exact hzlt.
              exact hylt.
            }
            { apply Nle_refl. }
            {
              left.
              intro heq.
              subst zf.
              apply (Nlt_irrefl xf).
              red.
              apply Nle_trans with yf.
              exact hzlt.
              exact hylt.
            }
          }
          (* z right side not equal *)
          {
            assert (hzlt:=Nle_neq_lt _ _ hzs hzneq).
            clear hzs hzneq.
            red in hzlt.
            specialize (ih (Nnext zs)).
            inversion ih as [ih'].
            clear ih.
            apply ih'.
            clear ih'.
            red. split. red. split.
            {
              apply Nle_trans with yf.
              exact hzf.
              exact hylt.
            }
            { apply Nle_next. }
            {
              right.
              intro heq.
              apply Nnext_neq in heq.
              contradiction heq.
            }
          }
        }
        (* y right side not equal *)
        {
          assert (hylt:=Nle_neq_lt _ _ hys hyneq).
          clear hys hyneq.
          red in hylt.
          apply Nle_next_elim in hylt.
          constructor.
          intros (zf,zs) [ [ hzf hzs ] hzneq ].
          destruct hzneq as [hzneq|hzneq].
          (* z left side not equal *)
          {
            assert (hzlt:=Nle_neq_lt _ _ hzf hzneq).
            clear hzf hzneq.
            red in hzlt.
            specialize (ih (Nnext zs)).
            inversion ih as [ih'].
            clear ih.
            apply ih'.
            clear ih'.
            red. split. red. split.
            {
              apply Nle_next_elim.
              apply Nle_trans with yf.
              exact hzlt.
              exact hyf.
            }
            { apply Nle_next. }
            {
              right.
              intro heq.
              apply Nnext_neq in heq.
              contradiction heq.
            }
          }
          (* z right side not equal *)
          {
            assert (hzlt:=Nle_neq_lt _ _ hzs hzneq).
            clear hzs hzneq.
            red in hzlt.
            apply ihs'.
            red. split. red. split.
            {
              apply Nle_trans with yf.
              exact hzf.
              exact hyf.
            }
            {
              apply Nle_trans with (Nnext zs).
              apply Nle_next.
              apply Nle_trans with ys.
              exact hzlt.
              exact hylt.
            }
            {
              right.
              intro heq.
              subst zs.
              apply Nlt_irrefl with xs.
              red.
              apply Nle_trans with ys.
              exact hzlt.
              exact hylt.
            }
          }
        }
      }
    }
    Qed.


(*
  if Neq_dec Zzero a then b
  else if Neq_dec Zzero b then a
  else if Neq_dec a b then a
  else if Nle_dec a b then
    gcd a (Nrest a b)
  else
    gcd (Nrest a b) b

*)


d = (Ngcd (ZtoN x) (ZtoN y))