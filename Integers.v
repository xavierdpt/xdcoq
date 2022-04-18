
  (************************************************************************************)
  (*                                                                                  *)
  (* In this file, we construct the relative integers (..., -2, -1, 0, 1, 2, ...)     *)
  (*                                                                                  *)
  (* In the standard library, these integers are constructed as an inductive type.    *)
  (*                                                                                  *)
  (* But I don't think it is very sexy, because I read that it is possible to         *)
  (* construct the relative integers from the natural integers, then the rational     *)
  (* numbers from the integers, and the real numbers from the rationals.              *)
  (*                                                                                  *)
  (* The construction I will be using is actually well known in the litterature.      *)
  (* It consists of defining an equivalence class over pairs of natural integers,     *)
  (* then defining the addition and the multiplication on those.                      *)
  (*                                                                                  *)
  (* More details can be found here, in an article by Alexander Farrugia.             *)
  (* https://www.um.edu.mt/library/oar/bitstream/123456789/24485/1/                   *)
  (* A%20construction%20of%20the%20set%20of%20integers.pdf                            *)
  (*                                                                                  *)
  (* One challenge is that it is quite difficult to work with equivalence classes     *)
  (* in Coq, and there is some litterature on that topic.                             *)
  (*                                                                                  *)
  (* To deal with this, I elected to define a normalizing condition and a             *)
  (* function that maps any pair to that normalized representative.                   *)
  (*                                                                                  *)
  (* Then because the result of any operation is one of these representative, this    *)
  (* allows working with equality more easily.                                        *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (* We will construct the integers from the naturals that we defined earlier, so we  *)
  (* import them.                                                                     *)
  Require Export XD.Naturals.

  (* We define a notion of pairs. They are probably defined better in the standard    *)
  (* library, but I don't need fancy things.                                          *)
  Inductive Pair {A B:Type} :=
  | pair : A -> B -> Pair
  .

  (* We will work with pairs of NN *)
  Definition PairOf (A:Type) := @Pair A A.

  (* These two functions retrieve the first and second elements of the pair           *)
  Definition first {A:Type} (p : PairOf A) : A := match p with
  | pair l _ => l
  end.

  Definition second {A:Type} (p : PairOf A) : A := match p with
  | pair _ r => r
  end.

  (* An equivalence relation is reflexive, symmetric and transitive *)

  Definition reflexive {A:Type} (R:A->A->Prop) :=
    forall x, R x x.

  Definition symmetric {A:Type} (R:A->A->Prop) :=
    forall x y, R x y -> R y x.

  Definition transitive {A:Type} (R:A->A->Prop) :=
    forall x y z, R x y -> R y z -> R x z.

  Definition equivalence {A:Type} (R:A->A->Prop) :=
      reflexive R /\ symmetric R /\ transitive R.

  (* While we are at it, we define commutativity and associativity                    *)
  Definition commutative {T:Type} (f:T->T->T) :=
    forall x y, f x y = f y x.
  Definition associative {T:Type} (f:T->T->T) :=
    forall x y z, f (f x y) z = f x (f y z).

  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Construction                                                                 *)
  (*                                                                                  *)
  (************************************************************************************)


  (* The equivalence relation is that (fst x) + (snd y) = (snd x) + (fst y)           *)
  Definition _Zrel (x y:PairOf NN) :=
    Nplus (first x) (second y) = Nplus (second x) (first y).

  (* We can prove that this is an equivalence, the proof is easy, and relies heavily  *)
  (* on the commutativity of addition.                                                *)
  Theorem _Zrel_equivalence : equivalence _Zrel.
  Proof.
    red.
    split.
    (* reflexivity *)
    {
      red. intros (xf,xs). red. simpl.
      rewrite Nplus_comm. reflexivity.
    }
    split.
    (* symmetry *)
    {
      red. intros (xf,xs) (yf,ys) h. red. simpl. red in h. simpl in h.
      rewrite (Nplus_comm ys).
      rewrite h.
      rewrite (Nplus_comm xs).
      reflexivity.
    }
    (* transitivity *)
    {
      red. intros (xf,xs) (yf,ys) (zf,zs). unfold _Zrel. simpl.
      intros hxy hyz.
      apply Nplus_elim_l with ys.
      repeat rewrite Nplus_assoc.
      rewrite (Nplus_comm ys).
      rewrite hxy.
      clear hxy.
      rewrite <- Nplus_assoc.
      rewrite hyz.
      clear hyz.
      rewrite Nplus_assoc.
      rewrite (Nplus_comm xs).
      reflexivity.
    }
  Qed.


  (************************************************************************************)
  (* A note on notations                                                              *)
  (* I try to be systematic when introducing notations.                               *)
  (* If x is a pair, then xf and xs are the first and second element.                 *)
  (* If z is an object make of a pair and an hypothesis, then xp is the pair, and     *)
  (* hx is the hypothesis.                                                            *)
  (* If there is an equality about x, then it should be named heqx.                   *)
  (* If there is a decision to be made in an if-then, then the variable for the       *)
  (* decision is named d.                                                             *)
  (* And so on. This makes long proofs more manageable.                               *)
  (************************************************************************************)

  
  

  (* Membership condition for a class equivalence representative                      *)
  (* One of the elements of the pair must be zero.                                    *)
  (* What this actually models is going forward on one component and backwards on the *)
  (* other.                                                                           *)
  Definition _Zcond p := first p = Nzero \/ second p = Nzero.

  (* The set of integers is the set of pairs which match this condition.              *)
  Definition ZZ := { p : PairOf NN | _Zcond p }.


  (* In the next two lemmas, to reassure ourselves, we prove two things               *)
  (* First, any pair is equivalent to a least one pair which matches the condition.   *)
  (* Second, if any two pairs match the condition, then they are not equivalent,      *)
  (* thus guaranteeing uniqueness.                                                    *)

  (* This is the first part                                                           *)
  (* For any pair of natural numbers, there exist an element of Z that is equivalent  *)
  (* to that pair.                                                                    *)
  Lemma _Z_representation : forall (p:PairOf NN), exists (z:ZZ), _Zrel p (proj1_sig z).
  Proof.
    (* We work on that pair *)
    intros (pf,ps).
    unfold _Zrel.
    simpl.
    (* We'll proceed by induction over pf *)
    pattern pf;apply Ninduction;clear pf.
    (* pf = 0 *)
    {
      (* The representative is (0,ps) *)
      set(zp:=pair Nzero ps).
      (* We just need to prove that it satisfies Zcond to create an element of ZZ *)
      assert(zh:_Zcond zp).
      { red. left. simpl. reflexivity. }
      exists (exist _ zp zh).
      subst zp. simpl.
      rewrite Nplus_zero_r.
      rewrite Nplus_zero_l.
      reflexivity.
    }
    (* Induction case *)
    {
      intro pf'. intro ih.
      (* We have a z that satisfies the condition for (pf', ps), and pf' is not zero *)
      destruct ih as [z ih].
      (* So we extract its parts *)
      destruct z as [ [zf zs ] hz].
      red in hz.
      simpl in hz.
      simpl in ih.
      destruct hz as [hz|hz].
      (* zf = 0 *)
      {
        (* We handle zs = zero separately *)
        induction zs as [|zs _] using Ninduction.
        (* zs = 0 *)
        {
          rewrite Nplus_zero_r in ih.
          subst pf'.
          subst zf.
          rewrite Nplus_zero_r.
          (* Answer is (1,0) *)
          set(zp:=pair None Nzero).
          assert (zh:_Zcond zp).
          { red. simpl. right. reflexivity. }
          exists (exist _ zp zh).
          simpl.
          rewrite Nplus_zero_r.
          subst zp.
          rewrite Nnext_eq.
          reflexivity.
        }
        (* zs is not 0 *)
        {
          subst zf.
          rewrite Nplus_zero_r in ih.
          subst ps.
          (* answer is (0, pred(zs)) *)
          set(zp:=pair Nzero zs).
          assert (zh:_Zcond zp).
          { red. simpl. left. reflexivity. }
          exists (exist _ zp zh).
          simpl.
          subst zp.
          rewrite Nplus_zero_r.
          repeat rewrite Nnext_eq.
          repeat rewrite <- Nplus_assoc.
          apply Nplus_intro_l.
          rewrite Nplus_comm.
          reflexivity.
        }
      }
      (* zs = 0 *)
      {
        subst zs.
        rewrite Nplus_zero_r in ih.
        subst pf'.
        (* answer is (zf+1,0) *)
        set(zp:=pair (Nnext zf) Nzero).
        assert (zh:_Zcond zp).
        { red. simpl. right. reflexivity. }
        exists (exist _ zp zh).
        subst zp.
        simpl.
        rewrite Nplus_zero_r.
        repeat rewrite Nnext_eq.
        repeat rewrite Nplus_assoc.
        reflexivity.
      }
    }
  Qed.

  (* Note about induction:                                                             *)
  (* When doing induction over a natural number n, there are two cases:               *)
  (* - In the first case, n = 0 and the substitution is done by Coq.                  *)
  (* - In the other case, we can define the name of the variable that will be         *)
  (*   introduced in the induction step.                                              *)
  (*   Since the original variable is lost, it is my habit to reuse the same name.    *)
  (*   But keep in mind the the value is actually the predecessor of the original n.  *)
  (*   This can lead to some confusion when writing comments, because it can be       *)
  (*   difficult to remember which is which.                                          *)
  (*   I should be more pedantic and use n' m', k', etc.                              *)


  (* For any x y, if x and y are equivalent, then they are equal                      *)
  Lemma _Z_uniqueness : forall (x y:ZZ),
    let xp := proj1_sig x in
    let yp := proj1_sig y in
    _Zrel xp yp -> xp = yp.
  Proof.
    intros ((xf,xs), hx) ((yf,ys), hy).
    simpl.
    intro h.
    unfold _Zrel in h.
    unfold _Zcond in hx, hy.
    simpl in h, hx, hy.
    (* The proof proceeds by examining all possibilities on the conditions on x and y *)
    destruct hx as [ hx | hx ];
    destruct hy as [ hy | hy ].
    {
      subst xf yf.
      rewrite Nplus_zero_l in h.
      rewrite Nplus_zero_r in h.
      subst ys. reflexivity.
    }
    {
      subst xf ys.
      rewrite Nplus_zero_l in h.
      symmetry in h.
      apply Nplus_zero in h.
      destruct h as [hx hy].
      subst xs yf. reflexivity.
    }
    {
      subst xs yf.
      rewrite Nplus_zero_r in h.
      apply Nplus_zero in h.
      destruct h as [hx hy].
      subst xf ys. reflexivity.
    }
    {
      subst xs ys.
      rewrite Nplus_zero_l in h.
      rewrite Nplus_zero_r in h.
      subst yf. reflexivity.
    }
  Qed.

  (* To define functions over ZZ, we first define them over pairs of natural nubmers  *)
  (* then we prove that they match the condition for membership in ZZ,                *)
  (* then we define the corresponding function over ZZ.                               *)

  (* This an function that sends any pairs of integers to a pair that matches the     *)
  (* membership condition.                                                            *)
  (* What it does is that it removes the minimum of the two numbers from both numbers *)
  (* so that one of the element becomes zero.                                         *)
  Definition _Zmake (p:PairOf NN) : (PairOf NN) :=
    match p with
    | pair pf ps => let m := Nmin pf ps in
      match (Neq_dec m pf) with
      | left _ => pair Nzero (Nrest ps pf)
      | right _ => pair (Nrest pf ps) Nzero
      end
    end.

  (* Here we prove that it satisfies the membership condition                         *)
  Lemma _Zmake_ok : forall (p:PairOf NN), _Zcond (_Zmake p).
  Proof.
    intros (pf,ps).
    unfold _Zcond.
    unfold _Zmake.
    destruct (Neq_dec) as [d|d].
    { simpl. left. reflexivity. }
    { simpl. right. reflexivity. }
  Qed.
 
  (* This is the representative function over ZZ                                      *)
  Definition Zmake (x : PairOf NN) := exist _ (_Zmake x) (_Zmake_ok x).

  (* Next we define zero, one, and the opposite of one using a similar strategy.      *)

  Definition _Zzero := @pair NN NN Nzero Nzero.
  Definition _Zone := @pair NN NN None Nzero.
  Definition _Zone_opp := @pair NN NN Nzero None.

  (* Note: I explicitly typed the pairs because otherwise,                            *)
  (* Coq infers { x | isnatural x } instead of NN and then confuses itself            *)

  Lemma _Zzero_ok : _Zcond _Zzero.
  Proof.
    unfold _Zcond. simpl. left. reflexivity.
  Qed.

  Lemma _Zone_ok : _Zcond _Zone.
  Proof.
    unfold _Zcond. simpl. right. reflexivity.
  Qed.

  Lemma _Zone_opp_ok : _Zcond _Zone_opp.
  Proof.
    unfold _Zcond. simpl. left. reflexivity.
  Qed.

  (* We don't use Zmake to define those, because Zmake computes numbers that will     *)
  (* not be exactly the same, and they will have to be proven equal using             *)
  (* proof irrelevance. We want to minize this and you will see an example shortly.   *)

  Definition Zzero := exist _ _Zzero _Zzero_ok.
  Notation "0z" := Zzero (only printing) : maths. 

  Definition Zone := exist _ _Zone _Zone_ok.
  Notation "1z" := Zone (only printing) : maths. 

  Definition Zone_opp := exist _ _Zone_opp _Zone_opp_ok.
  Notation "-1z" := Zone_opp (only printing) : maths. 

  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Addition                                                                     *)
  (*                                                                                  *)
  (************************************************************************************)


  (* That's addition, defined as in the paper *)
  Definition _Zplus (x y : PairOf NN) : (PairOf NN) := match x, y with
  | pair xf xs, pair yf ys => pair (Nplus xf yf) (Nplus xs ys)
  end.
  Notation "x _+z y" := (_Zplus x y) (only printing, at level 50) : maths.

  (* And that's addition going through Zmake                                          *)
  Definition Zplus (x y : ZZ) : ZZ :=
    let (xp, hx) := x in
    let (yp, hy) := y in
    Zmake (_Zplus xp yp).
  Notation "x +z y" := (Zplus x y) (only printing, at level 50) : maths.

  (* To prove commmutativity and associativity, we first prove it on the 'naked'      *)
  (* function, because Zmake makes things more difficult by adding a layer of logic.  *)

  (* _Zplus is commutative *)
  Lemma _Zplus_comm : commutative _Zplus.
  Proof.
    red. intros (xf,xs) (yf,ys). simpl.
    rewrite (Nplus_comm yf).
    rewrite (Nplus_comm ys).
    reflexivity.
  Qed.

  (* _Zplus is associative *)
  Lemma _Zplus_assoc : associative _Zplus.
  Proof.
    red.
    intros (xf,xs) (yf,ys) (zf,zs).
    simpl.
    repeat rewrite <- Nplus_assoc.
    reflexivity.
  Qed.


  (* Commutativity of addition is not difficult *)
  Lemma Zplus_comm : commutative Zplus.
  Proof.
    red.
    intros (xp,hx) (yp,hy).
    apply proof_irrelevance.
    simpl.
    apply f_eq.
    rewrite _Zplus_comm.
    reflexivity.
  Qed.

  (* Note: in the standard library, they write the full definition of commutativity and *)
  (* associativity in all the theorems instead of using generitc definitions of these   *)
  (* properties.                                                                        *)
  (* Coq does not mind, but one disandvantage of writing 'commutative Zplus' instead of *)
  (* definition is that the Search command will match against 'commutative _', but not  *)
  (* against 'Zplus _ _'.                                                               *)
  (* It would be nice to have a way for search to match multiple forms of the same      *)
  (* theorem, maybe it is possible, I don't know.                                       *)

  (* Zplus_comm and _Zplus_comm are found, but Nplus_comm and Nmult_comm are not found  *)
  Search (commutative _).

  (* This search for exploded forms of commutativity,                                   *)
  Search (?f ?a ?b = ?f ?b ?a).

  (* x + 0 = x *)
  Lemma Zplus_zero_r : forall x:ZZ, Zplus x Zzero = x.
  Proof.
    intros ((xf,xs),hx).
    apply proof_irrelevance.
    simpl.
    red in hx. simpl in hx.
    rewrite Nplus_zero_r.
    rewrite Nplus_zero_r.
    destruct hx as [ hx | hx ].
    {
      subst xf.
      rewrite Nmin_zero_l.
      simpl.
      rewrite Nrest_zero_r. reflexivity.
    }
    {
      subst xs.
      rewrite Nmin_zero_r.
      rewrite Nrest_zero_l.
      rewrite Nrest_zero_r.
      destruct (Neq_dec) as [d|d].
      { subst xf. reflexivity. }
      { reflexivity. }
    }
  Qed.

  (* 0 + x = x *)
  Lemma Zplus_zero_l : forall x:ZZ, Zplus Zzero x = x.
  Proof.
    intro x. rewrite Zplus_comm. rewrite Zplus_zero_r. reflexivity.
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Preparation to prove associativity                                           *)
  (*                                                                                  *)
  (************************************************************************************)

  (* To prove associativivity, we will have to deal with multiple layers of Zmake     *)
  (* To make this more manageable, we first prove that one of them can disappear      *)
  (* without changing the results.                                                    *)
  Lemma _Zplus_repr : forall x y, _Zmake (_Zplus x y) = _Zmake (_Zplus x (_Zmake y)).
  Proof.
    (* This proof is very long, but there is a common strategy that I will explain    *)
    (* as we go.                                                                      *)
    intros [xf xs] [ys yf].
    unfold _Zmake. unfold _Zplus.
    (* First strategy is to deal with each decision on at a time, and there are three *)
    (* We name them d1, d2, d3 *)
    (* Coq will choose one of them for us. This is not very robust, but saves the     *)
    (* trouble of copy/pasting enough to have an unambiguous match                    *)
    destruct (Neq_dec) as [d1|d1].
    {
      (* _Zmake is predictable, and we know without looking that the decision in d1   *)
      (* will simplify, because there is a common subexpression, so we leverage that  *)
      apply Nmin_le in d1.
      (* Now we don't have much to work with in d1, let's proceed down.               *)
      destruct (Neq_dec) as [d2|d2].
      {
        apply Nmin_le in d2.
        rewrite Nplus_zero_r.
        (* for d2, we can find the missing number, since it's on d2, we call it k2    *)
        apply Nle_nmk in d2. destruct d2 as [k2 heqk2].
        subst yf.
        (* Now we simplify a few things *)
        rewrite (Nplus_comm ys) in d1.
        rewrite Nplus_assoc in d1.
        apply Nle_plus_elim_r in d1.
        rewrite (Nplus_comm ys).
        (* And here, we simplify (rest (a+b) b) to a *)
        rewrite Nrest_plus_nmm.
        (* fill in the other inequality *)
        apply Nle_nmk in d1. destruct d1 as [k1 heqk1].
        (* rearrange and rewrite *)
        rewrite Nplus_assoc.
        rewrite <- heqk1.
        rewrite (Nplus_comm xf).
        rewrite <- Nplus_assoc.
        (* simplify calls to 'rest' *)
        rewrite Nrest_plus_nmm.
        rewrite Nrest_plus_nmm.
        rewrite (Nrest_comm xf).
        rewrite Nrest_plus_nmm.
        (* Go down with another decision *)
        destruct (Neq_dec) as [d3|d3].
        {
          (* Here we're done *)
          reflexivity.
        }
        {
          (* Here we have a negation on Nmin, and we also have a theorem for that     *)
          (* Nmin a b <> a -> a <= b *)
          apply Nmin_neq_le in d3.
          (* So we kind find that k1 is 0 *)
          apply Nle_plus_elim_zero_l in d3.
          subst k1.
          (* And we're done *)
          reflexivity.
        }
      }
      {
        apply Nmin_neq_le in d2.
        rewrite Nplus_zero_r.
        apply Nle_nmk in d2.
        destruct d2 as [k2 heqk2].
        subst ys.
        rewrite (Nplus_comm yf) in d1.
        rewrite Nplus_assoc in d1.
        apply Nle_plus_elim_r in d1.
        rewrite (Nplus_comm yf).
        rewrite Nrest_plus_nmm.
        destruct (Neq_dec) as [d2|d2].
        {
          apply Nmin_le in d2. clear d2.
          (* Here we do f k x = f k y -> x = y to remove a few characters from the screen *)
          apply f_eq.
          apply Nle_nmk in d1. destruct d1 as [k1 heqk1].
          subst xs.
          rewrite (Nplus_comm _ k1).
          repeat rewrite <- Nplus_assoc.
          rewrite Nrest_plus_nmm.
          rewrite Nrest_plus_nmm.
          reflexivity.
        }
        {
          apply Nmin_neq_le in d2.
          (* Here's how to convert the two inequalities to an equality *)
          assert(heq:=Nle_antisym _ _ d1 d2).
          subst xs. clear d1 d2.
          repeat rewrite <- Nplus_assoc.
          (* rest x x = 0 *)
          rewrite Nrest_cancel.
          rewrite Nrest_cancel.
          reflexivity.
        }
      }
    }
    {
      apply Nmin_neq_le in d1.
      destruct (Neq_dec) as [d2|d2].
      {
        apply Nmin_le in d2.
        apply Nle_nmk in d2. destruct d2 as [k2 heqk2].
        subst yf.
        rewrite (Nplus_comm ys) in d1.
        rewrite Nplus_assoc in d1.
        apply Nle_plus_elim_r in d1.
        rewrite Nplus_zero_r.
        rewrite (Nplus_comm ys).
        rewrite Nrest_plus_nmm.
        destruct (Neq_dec) as [d3|d3].
        {
          apply Nmin_le in d3.
          assert(heq:=Nle_antisym _ _ d1 d3).
          subst xf. clear d1 d3.
          repeat rewrite <- Nplus_assoc.
          rewrite Nrest_cancel.
          rewrite Nrest_cancel.
          reflexivity.
        }
        {
          apply Nmin_neq_le in d3. clear d3.
          apply feq_l.
          apply Nle_nmk in d1. destruct d1 as [k1 heqk1].
          subst xf.
          rewrite (Nplus_comm _ k1).
          repeat rewrite <- Nplus_assoc.
          rewrite Nrest_plus_nmm.
          rewrite Nrest_plus_nmm.
          reflexivity.
        }
      }
      {
        apply Nmin_neq_le in d2.
        apply Nle_nmk in d2.
        destruct d2 as [k2 heqk2].
        subst ys.
        rewrite Nplus_zero_r.
        rewrite (Nplus_comm yf).
        rewrite Nrest_plus_nmm.
        destruct (Neq_dec) as [d3|d3].
        {
          apply Nmin_le in d3.
          apply Nle_nmk in d3. destruct d3 as [k3 heqk3].
          subst xs.
          rewrite Nrest_comm.
          (* Coq is not very good we automatically normalizing custom expressions     *)
          (* so we have to manually rewrite using commutativity and associativity to  *)
          (* arrange the expressions as we want                                       *)
          (* One technique that works well is to normalize using associativity        *)
          (* then use commutativity to pivot the expressions and move a variable that *)
          (* is not inplace at the end, and repeat.                                   *)
          (* This does not work well when multiples variables have the same name in   *)
          (* an expression though.                                                    *)
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm k3).
          repeat rewrite Nplus_assoc.
          rewrite (Nplus_comm _ k3).
          rewrite <- Nplus_assoc.
          rewrite Nrest_plus_nmm.
          rewrite (Nplus_comm _ k3).
          rewrite Nrest_plus_nmm.
          rewrite (Nplus_comm yf) in d1.
          repeat rewrite Nplus_assoc in d1.
          apply Nle_plus_elim_r in d1.
          rewrite <- Nplus_assoc in d1.
          apply Nle_plus_elim_l in d1.
          rewrite Nplus_comm in d1.
          apply Nle_plus_elim_zero_l in d1.
          subst k3.
          reflexivity.
        }
        {
          apply Nmin_neq_le in d3.
          clear d1.
          apply Nle_nmk in d3. destruct d3 as [k3 heqk3].
          rewrite Nplus_assoc.
          rewrite <- heqk3.
          rewrite (Nplus_comm _ k3).
          repeat rewrite <- Nplus_assoc.
          rewrite Nrest_plus_nmm.
          rewrite Nrest_plus_nmm.
          reflexivity.
        }
      }
    }
  Qed.

  (* Now we can prove associativity of addition *)
  Lemma Zplus_assoc : forall x y z:ZZ, Zplus (Zplus x y) z = Zplus x (Zplus y z).
  Proof.
    intros (xp,hx) (yp,hy) (zp,hz).
    unfold Zplus.
    apply proof_irrelevance.
    simpl.
    rewrite <- _Zplus_repr.
    rewrite (_Zplus_comm (_Zmake _)).
    rewrite <- _Zplus_repr.
    rewrite (_Zplus_comm zp).
    rewrite _Zplus_assoc.
    reflexivity.
  Qed.

  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Induction property                                                           *)
  (*                                                                                  *)
  (************************************************************************************)

  (* Here we prove a custom induction for the integers                                *)
  (* A property is true for all integers if:                                          *)
  (* - it is true for 0                                                               *)
  (* - if it is true for z, then it is true for z + 1                                 *)
  (* - if it is true for z, then it is true for z - 1                                 *)


  Lemma Zinduction : forall (P:ZZ->Prop),
    (P Zzero) ->
    (forall x, P x -> P (Zplus x Zone)) ->
    (forall x, P x -> P (Zplus x Zone_opp)) ->
    forall x, P x.
  Proof.
    (* The predicate *)
    intros P.
    (* Predicate is true for zero *)
    intro hz.
    (* P z -> P (z+1) (up) *)
    intro hup.
    (* P z -> P (z-1) (down) *)
    intro hdown.
    (* We want to prove that P applies to any x, such as that one *)
    intro x.
    (* x consists of a pair and a proof that it satisfies the membership condition *)
    destruct x as [xp hx] eqn:heqx.
    (* Here's the condition *)
    unfold _Zcond in hx.
    (* The pair itself is made of two natural integers *)
    destruct xp as [xf xs] eqn:heqxp.
    (* The condition is more readable now *)
    simpl in hx.
    (* We can look at the two possibilites *)
    destruct hx as [hx|hx].
    (* xf = 0 *)
    {
      subst xf.
      (* We fold z to ease proving what z is equal to later *)
      rewrite <- heqx.
      (* Prepare the induction on any other x *)
      generalize dependent heqx.
      generalize dependent heqxp.
      generalize dependent xp.
      generalize dependent x.
      (* We're doing induction on xs *)
      induction xs as [|xs ih] using Ninduction.
      (* xs = 0 *)
      {
        intros x xp heqxp heqx.
        (* To prove that x = 0, we have to deal with proof irrelevance *)
        assert (heqxz:x = Zzero).
        {
          subst x. unfold Zzero.
          apply proof_irrelevance.
          simpl. reflexivity.
        }
        (* We are now free to substitute xz with Zzero *)
        rewrite heqxz.
        (* And that is hz *)
        exact hz.
      }
      (* Induction case: xs is not zero *)
      {
        (* We want to prove that P holds for (0, xs - 1) *)
        intro x.
        intro xp.
        intro heqxp.
        intro heqx.
        (* We will feed (xs, 0) to our induction hypothesis *)
        remember (pair Nzero xs) as yp eqn:heqyp.
        (* yp satisfies the membership condition *)
        assert (hy:_Zcond yp).
        {
          unfold _Zcond.
          rewrite heqyp. simpl.
          left. reflexivity.
        }
        (* Now we can create the corresponding integer yz *)
        remember (exist _ yp hy) as y eqn:heqy.
        (* And we use that in our induction hypothesis *)
        specialize (ih y).
        specialize (ih yp).
        specialize (ih heqyp).
        (* And we give it to hdown too *)
        specialize (hdown y).
        (* Now we need to prove that x = y + -1, and that's messy *)
        assert (heqyx:Zplus y Zone_opp = x).
        {
          (* Start we some substitutions *)
          subst x.
          subst y.
          (* Unfold the value of -1 *)
          unfold Zone_opp.
          (* Unfold some functions *)
          unfold Zplus.
          unfold _Zplus.
          (* match => destruct *)
          destruct yp as [yf ys].
          (* Use inversion to plug in the values *)
          inversion heqyp as [(heqyf,heqys)].
          (* An substitute those *)
          subst yf. subst ys.
          (* Now we unfold the rest and get a big mess *)
          unfold Zmake.
          simpl.
          (* And we apply proof irrelevance on that mess *)
          apply proof_irrelevance.
          simpl.
          (* Some easy rewriting *)
          rewrite Nplus_zero_l.
          rewrite Nmin_zero_l.
          (* Nice, Neq_dec should simplify now *)
          simpl.
          (* More rewriting *)
          rewrite Nrest_zero_r.
          rewrite Nnext_eq.
          (* And we have equality! *)
          reflexivity.
        }
        (* Now we can identify x with y - 1 *)
        rewrite <- heqyx.
        (* apply hdown to get to y *)
        apply hdown.
        (* apply ih to get to the equality requirement *)
        apply ih.
        (* and another round of proof irrelevance *)
        subst y.
        subst yp.
        apply proof_irrelevance.
        simpl.
        (* And we have equality *)
        reflexivity.
      }
    }
    (* Here's when the right number is zero *)
    {
      (* It's like the other case, but using 'hup' instead of 'hdown' *)
      subst xs.
      rewrite <- heqx.
      generalize dependent heqx.
      generalize dependent heqxp.
      generalize dependent xp.
      generalize dependent x.
      (* Induction *)
      induction xf as [|xf ih] using Ninduction.
      (* x = zero *)
      {
        intros x xp heqxp heqx.
        assert (heqxz:x=Zzero).
        { subst x. unfold Zzero. apply proof_irrelevance. simpl. reflexivity. }
        rewrite heqxz. exact hz.
      }
      (* Induction case *)
      {
        intros x xp heqxp heqx.
        clear hz hdown.
        (* We're going to use (xf, 0) here *)
        remember (pair xf Nzero) as yp eqn:heqyp.
        assert (hy:_Zcond yp).
        { unfold _Zcond. rewrite heqyp. simpl. right. reflexivity. }
        remember (exist _ yp hy) as y eqn:heqy.
        specialize (ih y).
        specialize (ih yp).
        specialize (ih heqyp).
        specialize (hup y).
        (* Here we show that x = y + 1 *)
        assert (heqxy:x = Zplus y Zone).
        {
          subst x. subst y. subst yp. unfold Zone.
          unfold Zplus.
          unfold _Zplus.
          apply proof_irrelevance.
          simpl.
          rewrite Nplus_zero_r.
          (* This time, the Neq_dec does not simplify very easily *)
          destruct (Neq_dec) as [d|d].
          {
            (* Bad branch *)
            rewrite Nmin_zero_r in d.
            rewrite <- Nnext_eq in d.
            inversion d.
          }
          {
            (* Right branch *)
            rewrite Nrest_zero_r.
            rewrite Nnext_eq.
            reflexivity.
          }
        }
        (* No we can complete this second part *)
        rewrite heqxy. apply hup. apply ih.
        subst y. subst yp. apply proof_irrelevance. simpl. reflexivity.
      }
    }
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Multiplication                                                               *)
  (*                                                                                  *)
  (************************************************************************************)

  (* Here we're defining multiplication with the same two technique *)
  (* First on any pairs, then on ZZ with Zmake *)

  Definition _Zmult (x y : PairOf NN) : (PairOf NN) := match x, y with
  | pair a b, pair c d => pair
    (Nplus(Nmult a c) (Nmult b d))
    (Nplus(Nmult a d) (Nmult b c))
  end.
  Notation "x _*z y" := (_Zmult x y) (only printing, at level 50) : maths. 

  Definition Zmult (x y : ZZ) : ZZ :=
    let (xp, hx) := x in
    let (yp, hy) := y in
    Zmake (_Zmult xp yp).
  Notation "x *z y" := (Zmult x y) (only printing, at level 50) : maths. 

  (* _Zmult is commutative *)
  Lemma _Zmult_comm : commutative _Zmult.
  Proof.
    red.
    intros (xf,xs) (yf,ys).
    unfold _Zmult.
    f_equal.
    { rewrite (Nmult_comm yf). rewrite (Nmult_comm ys). reflexivity. }
    {
      rewrite (Nmult_comm yf). rewrite (Nmult_comm ys).
      rewrite Nplus_comm. reflexivity.
    }
  Qed.

  (* 0 * x = 0 *)
  Lemma Zmult_zero_l : forall x, Zmult Zzero x = Zzero.
  Proof.
    intros ((xf,xs),xh).
    apply proof_irrelevance.
    (* Simplification works nice here *)
    simpl.
    unfold _Zzero.
    apply f_eq.
    (* Here Zmake created a zero that is not exactly NZero *)
    apply proof_irrelevance.
    simpl.
    unfold _Nzero.
    reflexivity.
  Qed.

  (* x * 0 = 0 *)
  Lemma Zmult_zero_r : forall x, Zmult x Zzero = Zzero.
  Proof.
    intros ((xf,xs),xh).
    apply proof_irrelevance.
    (* Simplification is less nice here, but we can deal with it *)
    simpl.
    rewrite Nmult_zero_r.
    rewrite Nplus_zero_l.
    rewrite Nmult_zero_r.
    rewrite Nmin_cancel.
    simpl.
    unfold _Zzero.
    apply f_eq.
    apply proof_irrelevance.
    simpl.
    unfold _Nzero.
    reflexivity.
  Qed.

  (* Zmult is commutative, and we don't even have to expand Zmake *)
  Lemma Zmult_comm : commutative Zmult.
  Proof.
    red.
    intros ((xf,xs),xh) ((yf,ys),yh).
    unfold _Zcond in xh,yh.
    simpl in xh,yh.
    simpl.
    rewrite (Nmult_comm yf).
    rewrite (Nmult_comm ys).
    rewrite (Nmult_comm yf).
    rewrite (Nmult_comm ys).
    destruct xh as [xh|xh].
    {
      subst xf.
      rewrite Nmult_zero_l.
      rewrite Nplus_zero_l.
      rewrite Nmult_zero_l.
      rewrite Nplus_zero_l.
      rewrite Nplus_zero_r.
      reflexivity.
    }
    {
      subst xs.
      rewrite Nmult_zero_l.
      rewrite Nplus_zero_r.
      rewrite Nmult_zero_l.
      rewrite Nplus_zero_r.
      rewrite Nplus_zero_l.
      reflexivity.
    }
  Qed.

  (* x * 1 = x *)
  Lemma Zmult_one_r : forall x, Zmult x Zone = x.
  Proof.
    intros ((xf,xs),hx).
    destruct Zone as [ [ of os ] ho ] eqn:heqo.
    apply proof_irrelevance.
    simpl.
    inversion heqo as [(heqof,heqos)].
    subst.
    unfold _Zcond in *. simpl in *.
    rewrite Nmult_one_r.
    rewrite Nmult_zero_r.
    rewrite Nplus_zero_r.
    rewrite Nmult_zero_r.
    rewrite Nplus_zero_l.
    rewrite Nmult_one_r.
    destruct hx as [hx|hx].
    {
      subst xf. rewrite Nmin_zero_l. simpl.
      rewrite Nrest_zero_r. reflexivity.
    }
    {
      subst xs. rewrite Nmin_zero_r.
      destruct (Neq_dec) as [d|d].
      { subst xf. rewrite Nrest_cancel. reflexivity. }
      { rewrite Nrest_zero_r. reflexivity. }
    }
  Qed.

  (* 1 * x = x *)
  Lemma Zmult_one_l : forall x, Zmult Zone x = x.
  Proof.
    intro x. rewrite Zmult_comm. rewrite Zmult_one_r. reflexivity.
  Qed.

  (* _Zmult is associative *)
  Lemma _Zmult_assoc : associative _Zmult.
  Proof.
    red.
    intros (xf,xs) (yf,ys) (zf,zs).
    simpl.
    (* This tactic implements functional equality for any number of arguments *)
    f_equal.
    {
      repeat rewrite Nplus_mult_distr_l.
      repeat rewrite Nplus_mult_distr_r.
      repeat rewrite <- Nmult_assoc.
      repeat rewrite <- Nplus_assoc.
      apply f_eq.
      rewrite Nplus_comm.
      repeat rewrite <- Nplus_assoc.
      reflexivity.
    }
    {
      repeat rewrite Nplus_mult_distr_l.
      repeat rewrite Nplus_mult_distr_r.
      repeat rewrite <- Nmult_assoc.
      repeat rewrite <- Nplus_assoc.
      apply f_eq.
      rewrite Nplus_comm.
      repeat rewrite <- Nplus_assoc.
      reflexivity.
    }
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Preparation to prove associativity of multiplication                         *)
  (*                                                                                  *)
  (************************************************************************************)

  (* Collapse one call to Zmake to prove associativity of multiplication *)
  (* Same strategy as for addition                                       *)
  Lemma _Zmult_repr : forall x y, _Zmake (_Zmult x (_Zmake y)) = _Zmake (_Zmult x y).
  Proof.
    (* I won't go over the proof, but it was quite some fun! *)
    (* I need short variable names for this one *)
    intros (a,b) (c,d).
    simpl.
    destruct (Neq_dec) as [d1|d1].
    {
      apply Nmin_le in d1.
      apply Nle_nmk in d1. destruct d1 as [k1 heqk1].
      simpl.
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_l.
      repeat rewrite Nplus_zero_r.
      destruct (Neq_dec) as [d2|d2].
      {
        subst d.
        rewrite (Nplus_comm c) in *.
        rewrite Nrest_plus_nmm in *.
        apply Nmin_le in d2.
        destruct (Neq_dec) as [d3|d3].
        {
          apply Nmin_le in d3.
          apply f_eq.
          repeat rewrite Nplus_mult_distr_l in *.
          remember (Nmult a c) as ac.
          remember (Nmult b k1) as bk1.
          remember (Nmult b c) as bc.
          remember (Nmult a k1) as ak1.
          repeat rewrite Nplus_assoc in d3.
          apply Nle_plus_elim_r in d3.
          rewrite Nplus_comm in d3.
          apply Nle_plus_elim_r in d3.
          clear d2.
          apply Nle_nmk in d3.
          destruct d3 as [d3 heqk3].
          rewrite <- heqk3.
          rewrite (Nplus_comm bk1).
          rewrite Nrest_plus_nmm.
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm bk1).
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm bc).
          rewrite Nrest_plus_nmm.
          reflexivity.
        }
        {
          apply Nmin_neq_le in d3.
          repeat rewrite Nplus_mult_distr_l in d3.
          repeat rewrite Nplus_mult_distr_l.
          remember (Nmult a k1) as ak1.
          remember (Nmult a c) as ac.
          remember (Nmult b c) as bc.
          remember (Nmult b k1) as bk1.
          rewrite (Nplus_comm _ ac) in d3.
          repeat rewrite <- Nplus_assoc in d3.
          apply Nle_plus_elim_l in d3.
          apply Nle_plus_elim_r in d3.
          assert(heq:=Nle_antisym _ _ d2 d3).
          clear d2 d3.
          rewrite <- heq.
          rewrite Nrest_cancel.
          repeat rewrite Nplus_assoc.
          rewrite (Nplus_comm ac).
          repeat rewrite <- Nplus_assoc.
          rewrite Nrest_cancel.
          reflexivity.
        }
      }
      {
        apply Nmin_neq_le in d2.
        subst d.
        rewrite (Nplus_comm c) in *.
        rewrite Nrest_plus_nmm in *.
        destruct (Neq_dec) as [d3|d3].
        {
          apply Nmin_le in d3.
          repeat rewrite Nplus_mult_distr_l in *.
          remember (Nmult a c) as ac.
          remember (Nmult b k1) as bk1.
          remember (Nmult b c) as bc.
          remember (Nmult a k1) as ak1.
          repeat rewrite Nplus_assoc in d3.
          apply Nle_plus_elim_r in d3.
          rewrite Nplus_comm in d3.
          apply Nle_plus_elim_r in d3.
          assert (heq:=Nle_antisym _ _ d2 d3).
          rewrite heq in *.
          rewrite Nrest_cancel.
          rewrite (Nplus_comm bk1).
          repeat rewrite Nplus_assoc.
          rewrite Nrest_cancel.
          reflexivity.
        }
        {
          apply Nmin_neq_le in d3.
          repeat rewrite Nplus_mult_distr_l in *.
          repeat rewrite Nplus_assoc in *.
          apply Nle_plus_elim_r in d3.
          remember (Nmult a k1) as ak1.
          remember (Nmult a c) as ac.
          remember (Nmult b k1) as bk1.
          remember (Nmult b c) as bc.
          rewrite (Nplus_comm ak1) in d3.
          apply Nle_plus_elim_l in d3.
          clear d2.
          apply Nle_nmk in d3.
          destruct d3 as [k3 heqk3].
          rewrite <- heqk3.
          rewrite (Nplus_comm ak1).
          rewrite Nrest_plus_nmm.
          repeat rewrite Nplus_assoc.
          rewrite (Nplus_comm _ k3).
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm ac).
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm bc).
          rewrite Nrest_plus_nmm.
          reflexivity.
        }
      }
    }
    {
      repeat rewrite Nmult_zero_r.
      repeat rewrite Nplus_zero_r.
      repeat rewrite Nplus_zero_l.
      apply Nmin_neq_le in d1.
      apply Nle_nmk in d1.
      destruct d1 as [k1 heqk1].
      destruct (Neq_dec) as [d2|d2].
      {
        apply Nmin_le in d2.
        simpl.
        destruct (Neq_dec) as [d3|d3].
        {
          apply Nmin_le in d3.
          subst c.
          rewrite (Nplus_comm d) in *.
          rewrite Nrest_plus_nmm in *.
          repeat rewrite Nplus_mult_distr_l in *.
          remember (Nmult a k1) as ak1.
          remember (Nmult b k1) as nk1.
          remember (Nmult a d) as ad.
          remember (Nmult b d) as bd.
          repeat rewrite Nplus_assoc in d2.
          apply Nle_plus_elim_r in d2.
          rewrite Nplus_comm in d2.
          apply Nle_plus_elim_l in d2.
          apply Nle_nmk in d2. destruct d2 as [k2 heqk2].
          rewrite <- heqk2.
          rewrite (Nplus_comm ak1).
          rewrite Nrest_plus_nmm.
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm ad).
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm bd).
          rewrite Nrest_plus_nmm.
          reflexivity.
        }
        {
          apply Nmin_neq_le in d3.
          subst c.
          rewrite (Nplus_comm d) in *.
          rewrite Nrest_plus_nmm in *.
          repeat rewrite Nplus_mult_distr_l in *.
          remember (Nmult a k1) as ak1.
          remember (Nmult a d) as ad.
          remember (Nmult b d) as bd.
          remember (Nmult b k1) as bk1.
          repeat rewrite Nplus_assoc in d2.
          apply Nle_plus_elim_r in d2.
          rewrite Nplus_comm in d2.
          apply Nle_plus_elim_l in d2.
          apply Nle_nmk in d2. destruct d2 as [k2 heqk2].
          rewrite <- heqk2.
          repeat rewrite (Nrest_comm ak1).
          rewrite (Nplus_comm ak1).
          rewrite Nrest_plus_nmm.
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm ad).
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm ad).
          rewrite Nrest_plus_nmm.
          rewrite <- heqk2 in d3.
          rewrite Nplus_comm in d3.
          apply Nle_plus_elim_zero_l in d3.
          subst k2.
          reflexivity.
        }
      }
      {
        apply Nmin_neq_le in d2.
        simpl.
        destruct (Neq_dec) as [d3 | d3].
        {
          apply Nmin_le in d3.
          subst c.
          rewrite (Nplus_comm d) in *.
          rewrite Nrest_plus_nmm in *.
          repeat rewrite Nplus_mult_distr_l in *.
          remember (Nmult a k1) as ak1.
          remember (Nmult b d) as bd.
          remember (Nmult a d) as ad.
          remember (Nmult b k1) as bk1.
          repeat rewrite Nplus_assoc in d2.
          apply Nle_plus_elim_r in d2.
          rewrite Nplus_comm in d2.
          apply Nle_plus_elim_r in d2.
          assert(ha:=Nle_antisym  _ _ d3 d2).
          clear d3 d2.
          rewrite <- ha.
          rewrite Nrest_cancel.
          rewrite (Nplus_comm ad).
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm ad).
          rewrite Nrest_cancel.
          reflexivity.
        }
        {
          apply Nmin_neq_le in d3.
          subst c.
          rewrite (Nplus_comm d) in *.
          rewrite Nrest_plus_nmm in *.
          repeat rewrite Nplus_mult_distr_l in *.
          remember (Nmult a k1) as ak1.
          remember (Nmult b k1) as bk1.
          remember (Nmult a d) as ad.
          remember (Nmult b d) as bd.
          repeat rewrite Nplus_assoc in d2.
          apply Nle_plus_elim_r in d2.
          rewrite Nplus_comm in d2.
          apply Nle_plus_elim_r in d2.
          clear d2.
          apply Nle_nmk in d3. destruct d3 as [k3 heqk3].
          rewrite <- heqk3.
          rewrite (Nplus_comm bk1).
          rewrite Nrest_plus_nmm.
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm bk1).
          repeat rewrite <- Nplus_assoc.
          rewrite (Nplus_comm bd).
          rewrite Nrest_plus_nmm.
          reflexivity.
        }
      }
    }
  Qed.

  (* Multiplication is associative *)
  Lemma Zmult_assoc : associative Zmult.
  Proof.
    red.
    intros x y z.
    unfold Zmult.
    unfold Zmake.
    apply proof_irrelevance.
    simpl.
    destruct x as [xp xh] eqn:hex.
    destruct y as [yp yh] eqn:hey.
    destruct z as [zp zh] eqn:hez.
    simpl.
    rewrite _Zmult_repr.
    rewrite (_Zmult_comm).
    rewrite _Zmult_repr.
    rewrite (_Zmult_comm).
    repeat rewrite _Zmult_assoc.
    reflexivity.
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Decidability of equality                                                     *)
  (*                                                                                  *)
  (************************************************************************************)

  (* Equality on ZZ is dedicable *)
  Definition Zeq_dec (x y:ZZ) : sumbool (x = y) (x <> y).
  Proof.
    (* We simply use Neq_dec on the pairs *)
    destruct x as [ [xf xs] hx].
    destruct y as [ [yf ys] hy].
    destruct (Neq_dec xf yf) as [df|df].
    {
      subst yf.
      destruct (Neq_dec xs ys) as [ds|ds].
      {
        subst ys. left.
        apply proof_irrelevance. simpl. reflexivity.
      }
      {
        right. unfold not. intro heq. inversion heq.
        subst ys. contradiction ds. reflexivity.
      }
    }
    {
      right. intro heq. inversion heq.
      subst yf. contradiction df. reflexivity.
    }
  Defined.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Order                                                                        *)
  (*                                                                                  *)
  (************************************************************************************)

  (* This is the definition of 'less than or equal' *)
  Definition Zle (x y:ZZ) : Prop :=
    let (xp, xh) := x in
    let (yp, yh) := y in
    let (xf, xs):=xp in
    let (yf, ys):=yp in
      Nle xf yf /\ Nle ys xs.
  Notation "x <=z y" := (Zle x y) (only printing, at level 50) : maths. 

  (* Definitoin of 'less than and not equal' *)
  Definition Zlt x y := Zle x y /\ x <> y.
  Notation "x <z y" := (Zlt x y) (only printing, at level 50) : maths. 

  (* reflexivity : x <= x *)
  Lemma Zle_refl : forall x, Zle x x.
  Proof.
    intros ((xf,xs),xh).
    unfold Zle.
    split.
    { apply Nle_refl. }
    { apply Nle_refl. }
  Qed.

  (* transitivity : x <= y -> y <= z -> x <= z *)
  Lemma Zle_trans : forall x y z, Zle x y -> Zle y z -> Zle x z.
  Proof.
    intros ((xf,xs),xh) ((yf,ys),yh) ((zf,zs),zh).
    unfold Zle.
    intros hxy hyz.
    destruct hxy as [hxyl hxyr].
    destruct hyz as [hyzl hyzr].
    split.
    { apply Nle_trans with yf. exact hxyl. exact hyzl. }
    { apply Nle_trans with ys. exact hyzr. exact hxyr. }
  Qed.

  (* antisymmetry : x <= y -> y <= x -> x = y *)
  Lemma Zle_antisym : forall x y , Zle x y -> Zle y x -> x = y.
  Proof.
    intros ((xf,xs),xh) ((yf,ys),yh).
    unfold Zle.
    intros hxy hyx.
    destruct hxy as [hxyl hxyr].
    destruct hyx as [hyxl hyxr].
    apply proof_irrelevance. simpl. f_equal.
    { apply Nle_antisym. exact hxyl. exact hyxl. }
    { apply Nle_antisym. exact hyxr. exact hxyr. }
  Qed.

  (* irreflexivity : x < x -> False *)
  Lemma Zlt_irrefl : forall x , Zlt x x -> False.
  Proof.
    intros x h.
    unfold Zlt in h.
    destruct h as [_ h].
    contradiction h.
    reflexivity.
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Decidability of order                                                        *)
  (*                                                                                  *)
  (************************************************************************************)

  (* Zle is decidable *)
  Definition Zle_dec (x y:ZZ) : sumbool (Zle x y) (Zle y x).
  Proof.
    (* The proof is a bit difficult because we cannot destruct disjunction *)
    assert(tech : forall P Q, P \/ Q -> not P -> not Q -> False).
    {
      intros P Q h np nq.
      (* We can't do that in the proof itself *)
      destruct h as [h|h].
      { apply np. exact h. }
      { apply nq. exact h. }
    }
    destruct x as [ [ xf xs ] xh] eqn:heqx.
    destruct y as [ [ yf ys ] yh] eqn:heqy.
    unfold Zle.
    unfold _Zcond in xh, yh. simpl in xh, yh.
    (* So we will ahve to use Neq_dec and detect contradictions *)
    destruct (Neq_dec xf Nzero) as [dxf|dxf].
    {
      subst xf.
      destruct (Neq_dec ys Nzero) as [dys|dys].
      {
        (* This is the nice case *)
        subst ys. left. split. apply Nle_zero_l. apply Nle_zero_l.
      }
      {
        destruct (Neq_dec yf Nzero) as [dyf|dyf].
        {
          subst yf.
          (* Both numbers are on the same side, so we compare them *)
          destruct (Nle_dec xs ys) as [ds|ds].
          { right. split. apply Nle_zero_l. exact ds. }
          { left. split. apply Nle_zero_l. exact ds. }
        }
        {
          (* Bad branch: We need at least side of y at zero *)
          specialize (tech _ _ yh). contradiction tech.
        }
      }
    }
    {
      destruct (Neq_dec xs Nzero) as [dxs|dxs].
      {
        subst xs.
        destruct (Neq_dec ys Nzero) as [dys|dys].
        {
          subst ys.
          (* Both numbers are on the same side, so we compare them *)
          destruct (Nle_dec xf yf) as [df|df].
          { left. split. exact df. apply Nle_zero_l. }
          { right. split. exact df. apply Nle_zero_l. }
        }
        {
          destruct (Neq_dec yf Nzero) as [dxs|dxs].
          {
            (* Another nice cases *)
            subst yf. right. split. apply Nle_zero_l.  apply Nle_zero_l.
          }
          {
            (* Remaining two cases are contradiction *)
            specialize (tech _ _ yh). contradiction tech.
          }
        }
      }
      { specialize (tech _ _ xh). contradiction tech. }
    }
  Qed.

  (* -1 * -1 = 1 *)
  Lemma Zmult_oneopp : Zmult Zone_opp Zone_opp = Zone.
  Proof.
    destruct Zone as [ [ of os ] ho ] eqn:heqo.
    destruct Zone_opp as [ [ opf ops ] hop ] eqn:heqop.
    apply proof_irrelevance.
    simpl.
    inversion heqo as [(heqof,heqos)].
    inversion heqop as [(heqopf,heqops)].
    subst.
    rewrite Nmult_zero_l.
    rewrite Nplus_zero_l.
    rewrite Nmult_one_l.
    rewrite Nmult_zero_l.
    rewrite Nplus_zero_l.
    rewrite Nmult_one_l.
    rewrite Nmin_zero_r.
    destruct (Neq_dec) as [d|_].
    { inversion d. }
    rewrite Nrest_zero_r.
    reflexivity.
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Opposite                                                                     *)
  (*                                                                                  *)
  (************************************************************************************)


  (* The opposite of x is x * -1 *)
  Definition Zopp (x:ZZ) := Zmult x Zone_opp.

  (* x + (-x) = 0 *)
  Lemma Zplus_opp_r : forall x, Zplus x (Zopp x) = Zzero.
  Proof.
    (* Again lots of cases because of Zmake *)
    unfold Zopp.
    intros ((xf,xs),xh).
    simpl.
    rewrite Nmult_zero_r.
    rewrite Nplus_zero_l.
    rewrite Nmult_one_r.
    rewrite Nmult_one_r.
    rewrite Nmult_zero_r.
    rewrite Nplus_zero_r.
    unfold _Zcond in xh. simpl in xh.
    destruct xh as [xh|xh].
    {
      subst xf.
      rewrite Nmin_zero_r.
      destruct (Neq_dec) as [d|d].
      {
        subst xs.
        rewrite Nrest_zero_r.
        rewrite Nplus_zero_r.
        apply proof_irrelevance.
        simpl.
        apply f_eq.
        apply proof_irrelevance.
        simpl.
        unfold _Nzero.
        reflexivity.
      }
      {
        rewrite Nrest_zero_r.
        rewrite Nplus_zero_r.
        rewrite Nplus_zero_l.
        apply proof_irrelevance.
        simpl.
        rewrite Nmin_cancel.
        destruct (Neq_dec) as [d'|d'].
        {
          rewrite Nrest_cancel.
          unfold _Zzero.
          reflexivity.
        }
        { contradiction d'. reflexivity. }
      }
    }
    {
      subst xs.
      rewrite Nmin_zero_l.
      simpl.
      rewrite Nplus_zero_r.
      rewrite Nrest_zero_r.
      rewrite Nplus_zero_l.
      apply proof_irrelevance.
      simpl.
      rewrite Nmin_cancel.
      destruct (Neq_dec) as [d|d].
      {
        rewrite Nrest_cancel.
        unfold _Zzero.
        reflexivity.
      }
      { contradiction d. reflexivity. }
    }
  Qed.

  (* (-x) + x = 0 *)
  Lemma Zplus_opp_l : forall x, Zplus (Zopp x) x  = Zzero.
  Proof.
    intro x. rewrite Zplus_comm. rewrite Zplus_opp_r. reflexivity.
  Qed.

  (* - (- x) = x *)
  Lemma Zopp_involutive : forall x, Zopp (Zopp x) = x.
  Proof.
    intro z.
    unfold Zopp.
    rewrite Zmult_assoc.
    rewrite Zmult_oneopp.
    rewrite Zmult_one_r.
    reflexivity.
  Qed.

  (* Definition of substraction *)
  Definition Zminus x y := Zplus x (Zopp y).

  (* Like Nle_nmk, probably not as useful because we have susbtraction in Z *)
  Lemma Zle_nmk : forall x y, exists z, Zplus x z = y.
  Proof.
    intros x y.
    exists (Zplus (Zopp x) y).
    rewrite <- Zplus_assoc.
    rewrite Zplus_opp_r.
    rewrite Zplus_zero_l.
    reflexivity.
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* There you go. The integers defined over the naturals, with                       *)
  (* - addition and proof of commutativity and associativity                          *)
  (* - multiplication and proof of commutativity and associativity                    *)
  (* - negation                                                                       *)
  (* - order                                                                          *)
  (* - induction property                                                             *)
  (*                                                                                  *)
  (* Classical theorems will be added soon.                                           *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

