

  (*                                                                                  *)
  (* To convert cons to append in proofs *)
  (*
  Lemma cons_append {A:Type} : forall (head:A) (tail:LO A), cons head tail = append (cons head nil) tail.
  Proof.
    intros head tail.
    simpl.
    reflexivity.
  Qed.
  *)


  (* Simplification lemma to remove empty lists on the right of append *)
  (*
  Lemma append_nil {A:Type} : forall l : LO A, append l nil = l.
  Proof.
    (* We will work on that list *)
    intro l.
    (* We proceed by induction over the list *)
    induction l as [| head tail ih].
    (* Base case *)
    {
      (* Simple evaluation of the fixpoint *)
      simpl.
      (* We have equality *)
      reflexivity.
    }
    (* Induction case *)
    {
      (* Evaluation *)
      simpl.
      (* By induction, appending nil to the tail gives back the tail *)
      rewrite ih.
      (* So we have equality *)
      reflexivity.
    }
  Qed.
  *)

  (* Associativity of append *)
  (*
  Lemma append_assoc {A:Type} : associative (append (A:=A)) .
  Proof.
    (* We unfold the definition of associativity *)
    red.
    (* We introduce our three lists *)
    intros x y z.
    (* And we proceed by induction over x *)
    induction x as [|head tail ih].
    (* Base case *)
    {
      (* Simple evaluation on both sides *)
      simpl.
      (* And we have equality *)
      reflexivity.
    }
    (* Induction case *)
    {
      (* Simple evaluation on both sides *)
      simpl.
      (* We can use our induction hypothesis *)
      rewrite ih.
      (* And we have equality *)
      reflexivity.
    }
  Qed.
  *)

  (* Simple lemmas to eliminate the left part on append when it is the same *)
  (*
  Lemma append_intro_l {A:Type} : forall (l m n: LO A), m = n -> append l m = append l n.
  Proof.
    (* Introduce the three lists *)
    intros l m n.
    (* Introduce the equality hypothesis *)
    intro heq.
    (* Replace m with n *)
    subst m.
    (* And we have equality *)
    reflexivity.
  Qed.
  *)

  (* Same for the right part on append *)
  (*
  Lemma append_intro_r (A:Type) : forall (l m n: LO A), m = n -> append m l = append n l.
  Proof.
    intros l m n heq. subst m. reflexivity.
  Qed.
  *)








  (* This lemma shows that isnatural is conserved by append *)
(*
  Lemma append_natural : forall l m, isnatural l -> isnatural m -> isnatural (append l m).
  Proof.
    intros l m.
    unfold isnatural.
    unfold allnil.
    (* The induction is actually quite simple, so no comments *)
    induction l as [|head tail ih].
    { simpl. intros _ h. exact h. }
    {
      simpl.
      intros [hnil hmatch].
      intro hm.
      split.
      { exact hnil. }
      { apply ih.
        { exact hmatch. }
        { exact hm. }
      }
    }
  Qed.
*)






  (* The set of natural numbers is a commutative monoid for addition and multiplication *)
  (*
  Theorem N_commutative_monoid : commutative_monoid NN Nplus /\ commutative_monoid NN Nmult.
  Proof.
    split.
    {
      red.
      repeat split.
      { apply Nplus_assoc. }
      { apply Nplus_comm. }
      { exists Nzero.
        intro a.
        split.
        { rewrite Nplus_zero_l. reflexivity. }
        { rewrite Nplus_zero_r. reflexivity. }
      }
    }
      red.
      repeat split.
      { apply Nmult_assoc. }
      { apply Nmult_comm. }
      { exists None.
        intro a.
        split.
        { rewrite Nmult_one_l. reflexivity. }
        { rewrite Nmult_one_r. reflexivity. }
      }
  Qed.
*)

  (* (next n) + m = n + (next m) *)
  Lemma Nplus_next: forall (n m:NN), Nplus (Nnext n) m = Nplus n (Nnext m).
  Proof.
    intros n m.
    rewrite Nplus_next_l.
    rewrite Nplus_next_r.
    reflexivity.
  Qed.







  (* n <= n + m *)
  Lemma Nle_plus_l : forall n m, Nle n (Nplus n m).
  Proof.

  Admitted.








  (* To converts "<" back to "<=" in proofs *)
  Lemma Nlt_le: forall n m, Nle (Nnext n) m -> Nlt n m.
  Proof.
    intros n m h.
    unfold Nlt.
    exact h.
  Qed.


  (* Length of a list *)
  Fixpoint length {A:Type} (l : List A) : NN := match l with
  | nil => Nzero
  | cons _ tail => Nnext (length tail)
  end.

  (* A type is infinite if for any (finite) list of elements of that type,
     it's possible to find another element that is not in the list *)
  Definition is_infinite (A:Type) := forall (l:List A), exists (a:A), not (inlist l a).


  (* Sum of a list *)
  Fixpoint Nsum (l:List NN) := match l with
  | nil => Nzero
  | cons head tail => Nplus head (Nsum tail)
  end.

  (* If the sum of a list is zero, then all its elements are zero *)
  Lemma sum_zero : forall (l:List NN), Nsum l = Nzero -> forall a, inlist l a -> a = Nzero.
  Proof.
    intro l.
    induction l as [|head tail ih].
    (* Base case *)
    {
      (* We can't find anything in an empty list *)
      simpl.
      intros _.
      intros a f.
      inversion f.
    }
    {
      simpl.
      intro heq.
      (* head = 0 and sum tail = 0 *)
      apply Nplus_zero in heq.
      destruct heq as [hl hr].
      subst head.
      specialize (ih hr).
      clear hr.
      intro a.
      specialize (ih a).
      intro h.
      (* a = 0 or a is in the tail *)
      destruct h as [hr | hl].
      (* a=0 *)
      {
        (* therefore a=0 *)
        exact hr.
      }
      (* a is in the tail *)
      {
        (* then the induction hypothesis says that a=0 *)
        specialize (ih hl).
        exact ih.
      }
    }
  Qed.

  (* Any element in a list is less than their sum *)
  Lemma sum_lt : forall (l:List NN), forall a, inlist l a -> Nle a (Nsum l).
  Proof.
  intro l.
  induction l as [|head tail ih].
  (* Base case *)
  { (* There are no elements in an empty list *)
    intros a h. simpl in h. inversion h.
  }
  {
    (* Assuming it's true for the tail, we just need to get rid of the head of the list *)
    intros a h.
    simpl in *.
    destruct h as [hl|hr].
    (* a is the head *)
    {
      subst a. simpl.
      apply Nle_plus_l.
    }
    (* a is in the tail *)
    {
      specialize (ih _ hr).
      apply Nle_trans with (Nsum tail).
      { exact ih. }
      {
        simpl.
        rewrite Nplus_comm.
        apply Nle_plus_l.
      }
    }
  }
  Qed.


  (* If an element is bigger than any element of the list, then it is not in the list *)
  Lemma lt_notin_list : forall (l:List NN) (a:NN), (forall x, inlist l x -> Nlt a x) -> not (inlist l a).
  Proof.
    intro l.
    induction l as [|head tail ih].
    {
      (* There are no elements in an empty list *)
      simpl.
      intros _ _.
      unfold not.
      intro f. exact f.
    }
    {
      (* if a is in the list, then we can show that a<a *)
      intros a h.
      unfold not.
      intro hin.
      unfold not in ih.
      specialize (h _ hin).
      apply Nlt_irrefl in h.
      inversion h.
    }
  Qed.

  (* The sum of the elements of a list + 1 is not in the list *)
  Lemma sum1_not_in_list : forall (l:List NN), not (inlist l (Nplus (Nsum l) None)).
  Proof.

    (* The sum + 1 of a list is bigger than any elements of the list *)
    assert(thm:=sum_lt).

    (* We will work on that list *)
    intro l.
    specialize (thm l).

    (* Let's call the sum 'S' *)
    set (S:=Nplus (Nsum l) None). 

    (* Negation means proving False *)
    unfold not in *.

    (* We assume that S in in the list, then derive a contradiction *)
    intro h.

    (* We can apply thm on S *)
    specialize (thm S).
    specialize (thm h).
    clear h.

    (* Now we can use irreflexivity of "<" to derive a contradiction *)
    eapply Nlt_irrefl with S.
    subst S.
    unfold Nlt.
    rewrite <- Nnext_eq.
    apply Nle_next_intro.
    rewrite <- Nnext_eq in thm.
    exact thm.
  Qed.

  (* The set of naturals is infinite *)
  Theorem Ninfinite : is_infinite NN.
  Proof.
    (* Being infinite means that for any finite list l of elements of type T,
       we can find an element of type T that is not in the list *)
    red.
    (* We will work on that list *)
    intro l.
    (* And in particular, the sum of the list + 1 is not in the list *)
    exists (Nplus (Nsum l) None).
    (* This it what we proved just above *)
    apply sum1_not_in_list.
  Qed.


  Definition divides d n := exists d', Nmult d d' = n.

  Lemma divides_zero_n : forall n:NN, divides n Nzero.
  Proof.
    intro n.
    red.
    exists Nzero.
    rewrite Nmult_zero_r.
    reflexivity.
  Qed.

  Lemma divides_n_zero : forall n:NN, divides Nzero n -> n = Nzero.
  Proof.
    intro n.
    pattern n;apply Ninduction.
    (* n = 0 *)
    { intros _. reflexivity. }
    (* n > 0 => impossible *)
    {
      clear n. intro n.
      intro ih. clear ih.
      intro h.
      unfold divides in *.
      destruct h as [d h].
      rewrite Nmult_zero_l in h.
      (* inversion is kind of magic here, but it will try to match nil against cons head tail and find it can't *)
      inversion h.
    }
  Qed.

  Lemma divides_one_n : forall n:NN, divides None n.
  Proof.
    intro n.
    unfold divides.
    exists n.
    rewrite Nmult_one_l.
    reflexivity.
  Qed.

  (* n + m = 1 -> (n = 1 and m = 0) or (n = 0 and m = 1) *)
  Lemma plus_eq_one : forall (n m:NN), Nplus n m = None -> n = None /\ m = Nzero \/ n = Nzero /\ m = None.
  Proof.
    (* Induction on n *)
    intro n.
    pattern n;apply Ninduction.
    (* Base case *)
    {
      (* n = 0 -> m = 1 *)
      intros m h.
      rewrite Nplus_zero_l in h.
      subst m.
      (* The right part of the disjunction applies *)
      right.
      split.
      { reflexivity. }
      { reflexivity. }
    }
    (* Induction case *)
    {
      (* n and induction hypothesis *)
      clear n. intro n. intro ih.
      (* m and equality hypothesis *)
      intro m. intro h.
      (* We can deduce n = 0 and m = 0 *)
      rewrite Nplus_next_l in h.
      unfold None in h.
      apply Nnext_elim in h.
      apply Nplus_zero in h.
      destruct h as [ hl hr ].
      (* Substitute n and m with zero *)
      subst n. subst m.
      (* Prepare the induction hypothesis *)
      specialize (ih None).
      rewrite Nplus_zero_l in ih.
      specialize (ih (eq_refl _)).
      (* Examine each "possibility" *)
      destruct ih as [hl | hr].
      (* The left case is impossible *)
      {
        destruct hl as [hl hr].
        inversion hl.
      }
      (* The right case is obvious *)
      {
        clear hr.
        left.
        split.
        { unfold None. reflexivity. }
        { reflexivity. }
      }
    }
  Qed.

  (* n * m = 1 -> n = 1 and m = 1 *)
  Theorem Nmult_one : forall n m : NN, Nmult n m = None -> n = None /\ m = None.
  Proof.
    (* Induction over n *)
    intro n.
    pattern n;apply Ninduction.
    (* Base case *)
    {
      (* n = 0 -> impossible *)
      intros m h.
      rewrite Nmult_zero_l in h.
      inversion h.
    }
    (* Induction case *)
    {
      (* We don't need the induction hypothesis *)
      clear n. intro n'. intro ih. clear ih.
      intro m. intro  h.
      (* We can deduce that m = 0 or m = 1 *)
      rewrite Nnext_eq in h.
      rewrite Nplus_mult_distr_r in h.
      rewrite Nmult_one_l in h.
      apply plus_eq_one in h.
      destruct h as [hl | hr ].
      (* m = 0 -> impossible *)
      {
        destruct hl as [hl hr].
        subst m.
        rewrite Nmult_zero_r in hl.
        inversion hl.
      }
      (* m = 1 *)
      {
        (* so n' must be zero *)
        destruct hr as [hl hr].
        subst m.
        rewrite Nmult_one_r in hl.
        subst n'.
        (* And now it's obvious *)
        split.
        { unfold None. reflexivity . }
        { reflexivity. }
      }
    }
  Qed.

  Lemma divides_n_one : forall n:NN, divides n None -> n = None.
  Proof.
  intros n h.
  unfold divides in h.
  destruct h as [d h].
  generalize dependent d.
  (* Induction over n *)
  pattern n;apply Ninduction.
  (* Base case *)
  {
    intros d h.
    rewrite Nmult_zero_l in h.
    inversion h.
  }
  (* Induction case *)
  {
    (* We don't need the induction hypothesis *)
    clear n. intro n'. intro ih. clear ih.
    intro d. intro h.
    (* From h, we can deduce that n' = zero, and therefore n = 1 *)
    apply Nmult_one in h.
    destruct h as [hl hr].
    subst d.
    unfold None in hl.
    apply Nnext_elim in hl.
    subst n'.
    unfold None.
    reflexivity.
  }
  Qed.

  Lemma divides_n_n : forall n, divides n n.
  Proof.
    intro n.
    unfold divides.
    exists None.
    rewrite Nmult_one_r.
    reflexivity.
  Qed.

  Definition isprime n := forall d, divides d n -> d<>n -> d = None.

  Lemma zero_not_eq_one : Nzero = None -> False.
  Proof.
    intro h.
    inversion h.
  Qed.

  Lemma two_not_eq_one : Ntwo = None -> False.
  Proof.
    intro h.
    inversion h.
  Qed.

  Lemma next_zero : Nnext Nzero = None.
  Proof. unfold None. reflexivity. Qed.

  Lemma zero_not_prime : not (isprime Nzero).
  Proof.
    unfold not. intro h.
    unfold isprime in h.
    (* For d = zero, we would prove 0 = 1, which is impossible *)
    specialize (h Ntwo).
    apply two_not_eq_one.
    apply h.
    (* Two divides zero indeed *)
    clear h.
    apply divides_zero_n.
    unfold not. intro heq. inversion heq.
  Qed.

  Lemma isprime_one : isprime None.
  Proof.
    unfold isprime.
    intro d.
    intro h.
    unfold divides in h.
    destruct h as [d' heq].
    apply Nmult_one in heq.
    destruct heq as [hl _].
    subst d.
    intros _.
    reflexivity.
  Qed.


  Lemma plus_eq_two : forall (n m:NN), Nplus n m = Ntwo -> (n = Nzero /\ m = Ntwo) \/ (n = None /\ m = None) \/ (n = Ntwo /\ m = Nzero).
  Proof.
  intro n.
  pattern n;apply Ninduction.
  {
    intros m h.
    rewrite Nplus_zero_l in h.
    subst m.
    left. split.
    { reflexivity. }
    { reflexivity. }
  }
  {
    intros n' ih. clear ih.
    intros m heq.
    rewrite Nnext_eq in heq.
    unfold Ntwo in heq.
    rewrite Nnext_eq in heq.
    rewrite (Nplus_comm n') in heq.
    repeat rewrite <- Nplus_assoc in heq.
    apply Nplus_elim_l in heq.
    apply plus_eq_one in heq.
    destruct heq as [heql | heqr].
    {
      destruct heql as [hn hm].
      subst m.
      subst n'.
      right. right.
      split.
      { unfold Ntwo. reflexivity. }
      { reflexivity. }
    }
    {
      destruct heqr as [hn hm].
      subst n'. subst m.
      right. left. split.
      { unfold None. reflexivity. }
      { reflexivity. }
    }
  }
  Qed.

  Lemma Nmult_zero : forall n m, Nmult n m = Nzero -> n = Nzero \/ m = Nzero.
  Proof.
  intro n.
  pattern n;apply Ninduction.
  {
    intro m. intro heq. clear heq.
    left. reflexivity.
  }
  {
    clear n. intro n'. intro ih. clear ih.
    intro m. intro heq.
    rewrite Nnext_eq in heq.
    rewrite Nplus_mult_distr_r in heq.
    rewrite Nmult_one_l in heq.
    apply Nplus_zero in heq.
    destruct heq as [hl hr].
    subst m.
    right.
    reflexivity.
  }
  Qed.

  Lemma isprime_two : isprime Ntwo.
  Proof.
    unfold isprime.
    intro d.
    intro h.
    intro hneq.
    unfold divides in h.
    destruct h as [d' heq].
    generalize dependent d'.
    generalize dependent hneq.
    pattern d;apply Ninduction.
    {
      intros hneq d' heq.
      rewrite Nmult_zero_l in heq.
      inversion heq.
    }
    {
      clear d. intro d. intro ih.
      intro hneq. intro d'. intro heq.
      rewrite Nnext_eq in heq.
      rewrite Nplus_mult_distr_r in heq.
      rewrite Nmult_one_l in heq.
      apply plus_eq_two in heq.
      destruct heq as [h02 | [h11 | h20]].
      {
        destruct h02 as [hl hr].
        subst d'.
        apply Nmult_zero in hl.
        destruct hl as [hl | hr].
        {
          subst d.
          unfold None.
          reflexivity.
        }
        { inversion hr. }
      }
      {
        destruct h11 as [hl hr].
        subst d'.
        rewrite Nmult_one_r in hl.
        subst d.
        clear ih.
        exfalso.
        apply hneq.
        unfold Ntwo.
        reflexivity.
      }
      {
        destruct h20 as [hl hr].
        subst d'.
        rewrite Nmult_zero_r in hl.
        inversion hl.
      }
    }
  Qed.

  Lemma zero_neq_two : Nzero = Ntwo -> False.
  Proof.
    intro i. inversion i.
  Qed.

  Lemma one_neq_two : None = Ntwo -> False.
  Proof.
    intro h.
    inversion h.
  Qed.

  Lemma Nplus_elim_one_r : forall n m p:NN, Nplus n m = Nplus p None ->
    (exists n', Nplus n' m  = p) \/
    (exists m', Nplus n  m' = p).
  Proof.
    intro n.
    pattern n;apply Ninduction.
    {
      intro m.
      intro p.
      intro heq.
      rewrite Nplus_zero_l in heq.
      subst m.
      right.
      exists p.
      rewrite Nplus_zero_l.
      reflexivity.
    }
    {
      clear n. intro n'. intro ih.
      intro m. intro p. intro heq.
      specialize (ih (Nnext m)).
      specialize (ih p).
      rewrite Nplus_next_l in heq.
      rewrite <- Nplus_next_r in heq.
      specialize (ih heq).
      destruct ih as [hl | hr].
      {
        destruct hl as [z hz].
        left.
        exists (Nnext z).
        rewrite Nplus_next_l.
        rewrite <- Nplus_next_r.
        exact hz.
      }
      {
        destruct hr as [z hz].
        rewrite Nplus_next_r in heq.
        rewrite <- Nnext_eq in heq.
        apply Nnext_elim in heq.
        rewrite <- heq in hz.
        apply Nplus_elim_l in hz.
        subst z.
        left.
        exists n'.
        exact heq.
      }
    }
  Qed.

  Definition three := Nnext Ntwo.

  Lemma isprime_three : isprime three.
  Proof.

  Admitted.

  Definition Neven (n:NN) := divides Ntwo n.
  Definition Nodd (n:NN) := not (Neven n).

  Lemma mult_two_r : forall n, Nmult n Ntwo = Nplus n n.
  Proof.
    intro n.
    unfold Ntwo.
    rewrite Nnext_eq.
    rewrite Nplus_mult_distr_l.
    repeat rewrite Nmult_one_r.
    reflexivity.
  Qed.

  Lemma mult_two_l : forall n, Nmult Ntwo n = Nplus n n.
  Proof.
    intro n.
    rewrite Nmult_comm.
    apply mult_two_r.
  Qed.

  Lemma not_even_odd : forall (n:NN), not (Neven n /\ Nodd n).
  Proof.
    intro n.
    unfold not.
    intros [heven hodd].
    unfold Nodd in hodd.
    apply hodd.
    exact heven.
  Qed.

  Lemma Neven_2k : forall (k:NN), Neven (Nmult Ntwo k).
  Proof.
  intro k.
  pattern k;apply Ninduction.
  { unfold Neven. rewrite Nmult_zero_r. apply divides_zero_n. }
  {
    clear k. intro k'. intro ih. clear ih.
    unfold Neven.
    unfold divides.
    exists (Nnext k').
    reflexivity.
  }
  Qed.
  
  Lemma Ndestruct : forall n:NN, n = Nzero \/ exists n', n = Nnext n'.
  Proof.
    intro n.
    pattern n;apply Ninduction.
    { left. reflexivity. }
    {
      clear n. intro n'. intro ih.
      destruct ih as [hl | hr].
      {
        subst n'.
        right.
        exists Nzero.
        reflexivity.
      }
      {
        destruct hr as [n'' heq].
        subst n'.
        right.
        exists (Nnext n'').
        reflexivity.
      }
    }
  Qed.
    

  Lemma Nodd_2k1 : forall (k:NN), Nodd (Nnext (Nmult Ntwo k)).
  Proof.
  intro k.
  pattern k;apply Ninduction.
  {
    rewrite Nmult_zero_r.
    unfold Nodd.
    unfold not.
    intro heven.
    unfold Neven in heven.
    unfold divides in heven.
    destruct heven as [e he].
    clear k.
    generalize dependent he.
    pattern e;apply Ninduction.
    {
      intro h.
      rewrite Nmult_zero_r in h.
      inversion h.
    }
    {
      clear e. intro e'. intro hi. clear hi. intro h.
      rewrite mult_two_l in h.
      fold None in h.
      apply plus_eq_one in h.
      destruct h as [h | h].
      { destruct h as [hl hr]. rewrite hr in hl. inversion hl. }
      { destruct h as [hl hr]. rewrite hr in hl. inversion hl. }
    }
  }
  {
    clear k. intro k'. intro ih.
    unfold Nodd.
    unfold not.
    intro heq.
    unfold Neven in heq.
    unfold divides in heq.
    destruct heq as [d heq].
    unfold Nodd in ih.
    unfold not in ih.
    apply ih.
    clear ih.
    unfold Neven.
    unfold divides.
    rewrite mult_two_l in heq.
    rewrite mult_two_l in heq.
    rewrite Nplus_next_r in heq.
    rewrite Nplus_next_l in heq.
    rewrite mult_two_l.
    assert (hd:=Ndestruct d).
    {
      destruct hd as [hz | he].
      { subst d. rewrite Nplus_zero_l in heq. inversion heq. }
      {
        destruct he as [d' heq']. subst d.
        rewrite Nplus_next_r in heq.
        rewrite Nplus_next_l in heq.
        apply Nnext_elim in heq.
        apply Nnext_elim in heq.
        exists d'.
        rewrite mult_two_l.
        exact heq.
      }
    }
  }
  Qed.

  Lemma Ndestruct_odd_even : forall n:NN, (exists k, n = Nmult Ntwo k) \/ (exists k, n = Nnext (Nmult Ntwo k)).
  Proof.
  intro n.
  pattern n;apply Ninduction.
  {
    left.
    exists Nzero.
    rewrite Nmult_zero_r.
    reflexivity.
  }
  {
    clear n. intro n'. intro ih.
    destruct ih as [h|h].
    {
      destruct h as [k h].
      subst n'.
      right.
      exists k.
      reflexivity.
    }
    {
      destruct h as [k h].
      subst n'.
      left.
      exists (Nnext k).
      rewrite mult_two_l.
      rewrite mult_two_l.
      rewrite Nplus_next_r.
      rewrite Nplus_next_l.
      reflexivity.
    }
  }
  Qed.

  Lemma next_not_eq : forall n:NN, n = Nnext n -> False.
  Proof.
    intro n.
    pattern n;apply Ninduction.
    { intro heq. inversion heq. }
    {
      clear n. intro n'. intro ih.
      intro hneq.
      apply Nnext_elim in hneq.
      apply ih.
      exact hneq.
    }
  Qed.

  Lemma even_or_odd : forall (n:NN), Neven n \/ Nodd n.
  Proof.
    intro n.
    assert (h:=Ndestruct_odd_even n).
    destruct h as [h | h].
    {
      destruct h as [k h].
      left.
      unfold Neven.
      unfold divides.
      exists k.
      subst n.
      reflexivity.
    }
    {
      destruct h as [k h].
      right.
      unfold Nodd.
      unfold not.
      intro heven.
      unfold Neven in heven.
      unfold divides in heven.
      destruct heven as [k' h'].
      rewrite <- h' in h.
      clear h'. clear n.
      rename k into m.
      rename k' into n.
      repeat rewrite mult_two_l in h.
      generalize dependent m.
      pattern n;apply Ninduction.
      {
        intro m.
        rewrite Nplus_zero_l.
        intro h.
        inversion h.
      }
      {
        clear n. intros n' ih. intros m heq.
        rewrite Nplus_next_r in heq.
        rewrite Nplus_next_l in heq.
        apply Nnext_elim in heq.
        assert (dm:=Ndestruct m).
        destruct dm as [hl | hr].
        { subst m. rewrite Nplus_zero_l in heq. inversion heq. }
        {
          destruct hr as [m' heq'].
          subst m.
          specialize (ih m').
          apply ih.
          rewrite Nplus_next_r in heq.
          rewrite Nplus_next_l in heq.
          apply Nnext_elim in heq.
          exact heq.
        }
      }
    }
  Qed.








  Lemma min_nm : forall n m, Nle (Nmin n m) n /\ Nle (Nmin n m) m.
  Proof.
    intros n m.
    split.
    {
      unfold Nmin.
      destruct (Nle_dec n m).
      { apply Nle_refl. }
      { exact n0. }
    }
    {
      unfold Nmin.
      destruct (Nle_dec n m).
      { exact n0. }
      { apply Nle_refl. }
    }
  Qed.


  Lemma plus_min_minus_max : forall n m, Nplus (Nmin n m) (Nrest n m) = Nmax n m.
  
  Proof.
    intro n.
    pattern n;apply Ninduction;clear n.
    {
      intro m.
      rewrite Nmin_zero_l.
      rewrite Nrest_zero_l.
      rewrite Nplus_zero_l.
      rewrite Nmax_zero_l.
      reflexivity.
    }
    {
      intros n' ih.
      intro m.
      destruct (Ndestruct m).
      {
        subst m.
        rewrite Nmin_zero_r.
        rewrite Nrest_zero_r.
        rewrite Nmax_zero_r.
        rewrite Nplus_zero_l.
        reflexivity.
      }
      {
        destruct H. subst m. rename x into m.
        rewrite Nmin_next.
        rewrite Nrest_next.
        rewrite Nmax_next.
        rewrite Nplus_next_l.
        apply f_eq.
        apply ih.
      }
    }
  Qed.

  Lemma zero_eq : forall (h:isnatural _Nzero), exist _ _Nzero h = Nzero.
  Proof.
    intro h.
    apply proof_irrelevance.
    simpl. reflexivity.
  Qed.



  Lemma destruct_min_le_n : forall n m, (Nle n m /\ Nmin n m = n) \/ (Nle m n /\ Nmin n m = m).
  Proof.
    intro n.
    pattern n;apply Ninduction;clear n.
    {
      intro m.
      rewrite Nmin_zero_l.
      left.
      split.
      { apply Nle_zero_l. }
      { reflexivity. }
    }
    {
      intros n' ih.
      intro m.
      destruct (Ndestruct m).
      {
        subst m. rewrite Nmin_zero_r. right. split.
        { apply Nle_zero_l. }
        { reflexivity. }
      }
      {
        destruct H. subst m. rename x into m'.
        rewrite Nmin_next.
        specialize (ih m').
        destruct ih as [ih|ih].
        {
          destruct ih as [hle heq]. left. split.
          { apply Nle_next_intro. exact hle. }
          { apply f_eq. exact heq. }
        }
        {
          destruct ih as [hle heq]. right. split.
          { apply Nle_next_intro. exact hle. }
          { apply f_eq. exact heq. }
        }
      }
    }
  Qed.


  Lemma min_nm_neq_n : forall n m, Nmin n m <> n -> Nmin n m = m.
  Proof.
    intro n.
    pattern n;apply Ninduction;clear n.
    { intro m. rewrite Nmin_zero_l. intro h. exfalso. apply h. reflexivity. }
    {
    intros n' ih m h.
    destruct (Ndestruct m).
    { subst m. rewrite Nmin_zero_r. reflexivity. }
    {
    destruct H. subst m. rename x into m'.
    rewrite Nmin_next.
    apply f_eq.
    specialize (ih m').
    apply ih.
    intro heq.
    apply h.
    rewrite Nmin_next.
    apply f_eq.
    exact heq.
    }
    }
Qed.



  Lemma Nrest_one : forall n:NN, n <> Nzero -> Nnext (Nrest n None) = n.
  Proof.
    intros n.
    induction n using Ninduction.
    { intro i. contradiction i. reflexivity. }
    { intros _. unfold None. rewrite Nrest_next. rewrite Nrest_zero_r. reflexivity. }
  Qed.

  Definition Ndestruct_dec n : sumbool (n=Nzero) (exists n', n = Nnext n').
  Proof.
    destruct (Neq_dec n Nzero) as [d|d].
    { left. exact d. }
    { right. exists (Nrest n None). rewrite Nrest_one. reflexivity. exact d. }
  Qed.



  Lemma Nneq_zero_lt : forall x:NN, x <> Nzero -> Nlt Nzero x.
  Proof.
    intros x h.
    unfold Nlt.
    destruct (Ndestruct x).
    { subst x. contradiction h. reflexivity. }
    { destruct H. subst x. apply Nle_next_intro. apply Nle_zero_l. }
  Qed.

  Lemma xxx : forall x y ,x <> y -> Nle x y -> Nlt x y.
intro x.
induction x using Ninduction.
{ intros. unfold Nlt. destruct (Ndestruct y).
{ subst y. contradiction H. reflexivity. }
{ destruct H1. subst y. apply Nle_next_intro. apply Nle_zero_l. }
}
{ intros. unfold Nlt in *.
destruct (Ndestruct y).
{ subst y. inversion H0. }
{ destruct H1. subst y. apply Nle_next_intro.
apply IHx.
intro. subst x0. apply H. reflexivity.
apply Nle_next_elim. assumption.
}
}
Qed.

  Definition Nlt_dec x y : sumbool (Nle x y) (Nlt y x).
    destruct (Neq_dec x y).
    { subst y. left. apply Nle_refl. }
    { destruct (Nle_dec x y).
      { left. assumption. }
      { right. apply xxx. intro. subst y. apply n. reflexivity. assumption. }
    }
  Defined.

Definition computational_eq {m n} (opaque_eq:m=n) : m = n :=
match Neq_dec m n with
| left transparent_eq => transparent_eq
| _ => opaque_eq
end.


Definition Npred (n:NN) (h:Nlt Nzero n) := Nrest n None.

Lemma Nnext_pred : forall n h, Nnext (Npred n h) = n.
Proof.
  intro n.
  induction n using Ninduction.
  { intros. inversion h. }
  {
    intros. unfold Npred.
    unfold None. rewrite Nrest_next. rewrite Nrest_zero_r.
    reflexivity.
  }
Qed.

Definition uu : forall x : NN, (forall y : NN, Nlt y x -> NN -> NN) -> NN -> NN.
intros. apply Nzero.
Defined.
Print uu.

Lemma vv x (r:Nzero <> x) : Nlt (Nrest x None) x.
Proof.
unfold Nlt.
unfold None.
assert (u:=Nnext_pred).
specialize (u x).
assert (v:Nlt Nzero x).
apply Nneq_zero_lt. intro heq. subst x. apply r. reflexivity.
specialize (u v).
pattern x at 1;rewrite <- u. rewrite Nrest_next. rewrite Nrest_zero_r.
rewrite u. apply Nle_refl.
Defined.

Definition _Nfact_main (x:NN) (f : forall y : NN, Nlt y x -> NN) : NN.
destruct (Neq_dec Nzero x).
{ apply None. }
{
  specialize (f (Nrest x None)).
  assert (Nlt (Nrest x None) x).
  { apply vv. exact n. }
  specialize (f H).
  apply (Nmult x f).
}
Defined.

Definition Nfact := Fix Nlt_wf _ _Nfact_main.

Lemma Nfact_zero : Nfact Nzero = None.
unfold Nfact. unfold Fix. simpl.
unfold _Nfact_main. simpl. reflexivity.
Qed.

Lemma Nfact_one: Nfact None = None.
Proof.
unfold Nfact.
assert (h:=Fix_eq).
specialize (h NN Nlt Nlt_wf).
specialize (h _ _Nfact_main).
rewrite h.
{
unfold _Nfact_main. rewrite Nmult_one_l. rewrite Nrest_cancel.
rewrite h.
{
unfold _Nfact_main. simpl. reflexivity. }
{
clear h.
intros.
unfold _Nfact_main.
destruct (Neq_dec _).
{ reflexivity. }
{ rewrite H. reflexivity. }
}
}
clear h.
intros.
unfold _Nfact_main.
destruct (Neq_dec _).
{ reflexivity. }
{ rewrite H. reflexivity. }
Qed.

Lemma Nfact_r : forall n, Nfact (Nnext n) = Nmult (Nnext n) (Nfact n).
Proof.
intro n.
induction n using Ninduction.
{
rewrite Nfact_zero. rewrite Nmult_one_r.
fold None. rewrite Nfact_one. reflexivity.
}
{
rename IHn into ih.
remember (Nfact n) as fn.
remember (Nfact (Nnext n)) as fnn.
remember (Nfact (Nnext (Nnext n))) as fnnn.
unfold Nfact in Heqfnnn.
rewrite Fix_eq in Heqfnnn.
{
unfold _Nfact_main in Heqfnnn.
destruct (Neq_dec _) in Heqfnnn.
{ inversion e. }
{
unfold Nfact in Heqfnn.
unfold _Nfact_main in Heqfnn.
unfold None at 3 in Heqfnnn.
rewrite Nrest_next in Heqfnnn.
rewrite Nrest_zero_r in Heqfnnn.
rewrite <- Heqfnn in Heqfnnn.
rewrite Heqfnnn.
reflexivity.
}
}
{
clear. intros.
unfold _Nfact_main.
destruct (Neq_dec _).
{ reflexivity. }
{ rewrite H. reflexivity. }
}
}
Qed.

  (* If allmatch is true for two lists, then it is true for their concatenation *)
  (*
  Theorem allmatch_append {A:Type} : forall (l m:LO A) (P:A->Prop),
    allmatch l P -> allmatch m P -> allmatch (append l m) P.
  Proof.
    (* We introduce both lists and the predicate *)
    intros l m P.
    (* And we will proceed by induction *)
    induction l as [|head tail ih].
    (* Base case *)
    {
      (* We don't need that *)
      intros _.
      (* This is the allmatch hypothesis for m *)
      intro hm.
      (* Simple evaluation *)
      simpl.
      (* And that's exactly our hypothesis *)
      exact hm.
    }
    (* Induction case *)
    {
      (* Hypotheses on n and m *)
      intros hn hm.
      (* Simple evaluation in goal and hypotheses *)
      simpl in *.
      (* The predicate applies to the head and to the tail *)
      destruct hn as [hhead htail].
      (* And we have to prove that the predicate applies to th ehead, the tail and m. *)
      split.
      (* We already know this *)
      { exact hhead. }
      (* Here we have to use the induction hypothesis *)
      {
        clear hhead.
        (* The predicate applies to the tail because htail *)
        specialize (ih htail). clear htail.
        (* And it applies to m because hm *)
        specialize (ih hm). clear hm.
        (* And therefore, we have our goal *)
        exact ih.
      }
    }
  Qed.
  *)

  (* In an empty list of lists, all elements are empty *)
  (*
  Lemma allnil_nil {A:Type} : allnil (nil (A:=LOLO A)).
  Proof.
    red.
    simpl.
    trivial.
  Qed.
  *)

  (* In a list of lists, if all elements are the empty list, then append commutes for these two lists *)
  (*
  Lemma allnil_append_comm {A:Type} : forall (l m : LOLO A), allnil l -> allnil m -> append l m = append m l.
  Proof.
    (* Induction on l *)
    intros l m.
    induction l as [|head tail ih].
    (* Base case *)
    {
      (* We don't care about the hypotheses for that case *)
      intros _ _.
      (* Left is simplified by definition of the fixpoint for append *)
      simpl.
      (* For the right side, we need our previous theorem *)
      rewrite append_nil.
      (* And we have equality *)
      reflexivity.
    }
    (* Induction case *)
    {
      (* First, we introduce and massage the hypotheses *)
      simpl in *.
      intros hx hy.
      red in hx, hy.
      simpl in *.
      destruct hx as [hnil hmatch].
      red in hnil.
      subst head.
      (* Then we prepare to use the induction hypothese *)
      unfold allnil in ih.
      specialize (ih hmatch). clear hmatch.
      specialize (ih hy).
      (* And we use it for rewrite *)
      rewrite ih. clear ih.
      (* Now we proceed by induction over m *)
      induction m as [|mhead mtail ih].
      (* Base case for m *)
      { simpl. reflexivity. }
      (* Induction case for m *)
      {
        (* Again we massage the hypotheses *)
        simpl.
        simpl in hy.
        destruct hy as [hnil hmatch'].
        red in hnil.
        subst mhead.
        (* Prepare the induction hypothese *)
        specialize (ih hmatch').
        (* Use it for rewrite *)
        rewrite ih. clear ih.
        (* And we have equality *)
        reflexivity.
      }
    }
  Qed.
  *)