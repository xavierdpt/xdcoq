
  Axiom Tf1_equality  : forall {T U:Type} (f g:T->U),
    (forall x, f x = g x) -> f = g.

  Axiom Tf2_equality : forall {T U V:Type} (f g:T->U->V),
    (forall x y, f x y = g x y) -> f = g.

  Definition idempotent {T:Type} (f:T->T) :=
    forall x, f x =  f (f x).

  Definition involutive {T:Type} (f:T->T) :=
     forall x, f (f x) = x.

  Definition injective {T U:Type} (f:T->U) :=
    forall x y, f x = f y -> x = y.

  Definition surjective {T U:Type} (f:T-> U) :=
    forall y, exists x, f x = y.

  Definition bijective {T U:Type} (f:T->U) :=
    injective f /\ surjective f.

  Definition periodic {T U:Type} (f:T->U) (Tplus:T->T->T) :=
    exists P, forall x, f(Tplus x P) = f x.

  Definition commutative {T:Type} (f:T->T->T) := 
    forall x y, f x y = f y x.

  Definition associative {T:Type} (f:T->T->T) :=
    forall x y z, f x (f y z) = f (f x y) z.

  Definition distributive_r {T:Type} (f g:T->T->T) :=
    forall x y z, f (g x y) z = f (g x z) (g y z).

  Definition distributive_l {T:Type} (f g:T->T->T) :=
    forall x y z, f z (g x y) = f (g z x) (g z y).

  Definition neutral {T:Type} (Top:T->T->T)(e:T) :=
    forall x, Top x e = x.

  Definition cancel {T:Type} (Top:T->T->T) (e:T) :=
    forall x, Top x e = e.

  Definition even {T:Type} (f:T->T) (Topp:T->T) :=
    forall x, f (Topp x) = f x.

  Definition odd {T:Type} (f:T->T) (Topp:T->T) :=
    forall x, f (Topp x) = Topp (f x).

  Definition monotonic {T U:Type} (f:T->U) (ordT:T->T->Prop) (ordU:U->U->Prop) :=
    forall x y, ordT x y -> ordU (f x) (f y).

  Definition between {T:Type} (R:T->T->Prop) x y z :=
    R x y /\ R y z.

  (* TODO: Check correctness *)
  Definition continuous {T U:Type}
      (RT:T->T->Prop) (RU:U->U->Prop)
      (Tzero:T) (Uzero:U)
      (Tminus:T->T->T) (Tplus:T->T->T)
      (Uminus:U->U->U) (Uplus:U->U->U)
      (f:T->U) (D:T->Prop) (x0:T) :=
    D x0 ->
    forall e, RU Uzero e -> (
      exists d, RT Tzero d -> (
        forall x, D x ->
          between RT (Tminus x0 d) x (Tplus x0 d) ->
          between RU (Uminus (f x0) e) (f x) (Uplus (f x0) e)
      )
    ).

  (* TODO: Check correctness *)
  Definition uniform_continuous {T U:Type}
      (RT:T->T->Prop) (RU:U->U->Prop)
      (Tzero:T) (Uzero:U)
      (Tminus:T->T->T) (Tplus:T->T->T)
      (Uminus:U->U->U) (Uplus:U->U->U)
      (f:T->U) (D:T->Prop) (x0:T) :=
    D x0 ->
    forall e, RU Uzero e -> (
      exists d, RT Tzero d -> (
        forall x y, D x -> D y ->
          (RT (Tminus x y) d /\ RT (Tminus y x) d) ->
          (RU (Uminus (f x) (f y)) e /\ RU (Uminus (f y) (f x)) e)
      )
    ).

  Definition reflexive {T:Type} (R:T->T->Prop) :=
    forall x, R x x.

  Definition irreflexive {T:Type} (R:T->T->Prop) := 
    forall x y, R x y -> R y x -> False.

  Definition symmetric {T:Type} (R:T->T->Prop) :=
    forall x y, R x y -> R y x.

  Definition transitive {T:Type} (R:T->T->Prop) :=
    forall x y z, R x y -> R y z -> R x z.

  Definition antisymmetric {T:Type} (R:T->T->Prop) :=
    forall x y, R x y -> R y x -> x = y.

  Definition equivalence {T:Type} (R:T->T->Prop) :=
    reflexive R  /\ symmetric R /\ transitive R.

  Definition identity (T:Type) (x:T) := x.

  Lemma Tidentity_bijective : forall (T:Type), bijective (identity T).
  Proof.
    intro T.
    red.
    split;red.
    {
      intros x y h.
      unfold identity in h.
      exact h.
    }
    {
      intro y.
      unfold identity.
      exists y.
      reflexivity.
    }
  Qed.

  Lemma Tf1_intro : forall {T U:Type} (f:T->U) x y, x = y -> f x = f y.
  Proof.
  intros T U f x y heq.
  subst y.
  reflexivity.
  Qed.

  Lemma Tf2_intro_r : forall {T U V:Type} {f:T->U->V} x y z, x = y -> f x z = f y z.
  Proof.
    intros T U V f x y z heq.
    subst y.
    reflexivity.
  Qed.

  Lemma Tf2_intro_l : forall {T U V:Type} {f:T->U->V} x y z, x = y -> f z x = f z y.
  Proof.
    intros T U V f x y z heq.
    subst y.
    reflexivity.
  Qed.

  Parameter A:Type.

  Parameter Aplus : A->A->A.
  Parameter Amult : A->A->A.

  Axiom Aplus_comm: commutative Aplus.
  Axiom Amult_comm: commutative Amult.
  Axiom Aplus_assoc: associative Aplus.
  Axiom Amult_assoc: associative Amult.

  Parameter Azero : A.
  Parameter Aone : A.

  Axiom Aplus_zero_l : forall x, Aplus Azero x = x.
  Axiom Amult_zero_l : forall x, Amult Azero x = Azero.
  Axiom Amult_one_l : forall x, Amult Aone x = x.

  Parameter Aopp : A->A.

  Axiom Aopp_cancel_r : forall x, Aplus x (Aopp x) = Azero.

  Parameter Ale : A->A->Prop.

  Axiom Aeq_neq : forall (x y:A), x = y \/ x <> y.
  Axiom Aeq_dec : forall (x y:A), sumbool (x=y) (x<>y).

  Axiom Ale_le : forall x y, Ale x y \/ Ale y x.
  Axiom Ale_dec : forall x y, sumbool (Ale x y) (Ale y x).

  Definition Alt x y := Ale x y /\ x <> y.

  Axiom Aplus_elim_r : forall x y z, Aplus x z = Aplus y z -> x = y.
  Axiom Amult_elim_r : forall x y z, Amult x z = Amult y z -> x = y.

  Lemma Aopp_cancel_l : forall x, Aplus (Aopp x) x = Azero.
  Proof.
    intro x.
    rewrite (Aplus_comm _ x).
    rewrite Aopp_cancel_r.
    reflexivity.
  Qed.

  Lemma Aplus_elim_l : forall x y z, Aplus z x = Aplus z y -> x = y.
  Proof.
    intros x y z heq.
    apply Aplus_elim_r with z.
    repeat rewrite (Aplus_comm _ z).
    exact heq.
  Qed.

  Lemma Amult_elim_l : forall x y z, Amult z x = Amult z y -> x = y.
  Proof.
    intros x y z heq.
    apply Amult_elim_r with z.
    repeat rewrite (Amult_comm _ z).
    exact heq.
  Qed.

  Lemma Aplus_intro_l : forall x y z, x = y -> Aplus x z = Aplus y z.
  Proof.
    intros x y z heq.
    apply Tf2_intro_r.
    assumption.
  Qed.

  Lemma Aplus_intro_r : forall x y z, x = y -> Aplus z x = Aplus z y.
  Proof.
    intros x y z heq.
    apply Tf2_intro_l.
    assumption.
  Qed.

  Lemma Amult_intro_l : forall x y z, x = y -> Amult x z = Amult y z.
  Proof.
    intros x y z heq.
    apply Tf2_intro_r.
    assumption.
  Qed.

  Lemma Amult_intro_r : forall x y z, x = y -> Amult z x = Amult z y.
  Proof.
    intros x y z heq.
    apply Tf2_intro_l.
    assumption.
  Qed.

  Lemma Aopp_intro : forall x y, x = y -> Aopp x = Aopp y.
  Proof.
    intros x y heq.
    apply Tf1_intro.
    assumption.
  Qed.


  Lemma Aplus_zero_r : forall x, Aplus x Azero = x.
  Proof.
    intro x. rewrite Aplus_comm. apply Aplus_zero_l.
  Qed.

  Lemma Amult_zero_r : forall x, Amult x Azero = Azero.
  Proof.
    intro x. rewrite Amult_comm. apply Amult_zero_l.
  Qed.

  Lemma Amult_one_r : forall x, Amult x Aone = x.
  Proof.
    intro x. rewrite Amult_comm. apply Amult_one_l.
  Qed.

  Lemma Ale_refl : forall x, Ale x x.
  Proof.
    intro x.
    assert (ha:=Ale_le x x ).
    destruct ha as [h|h].
    { exact h. }
    { exact h. }
  Qed.

  Lemma Aopp_involutive : involutive Aopp.
  Proof.
    red.
    intro x.
    Search Aopp.
    apply Aplus_elim_r with (Aopp x).
    rewrite Aopp_cancel_l.
    rewrite Aopp_cancel_r.
    reflexivity.
  Qed.

