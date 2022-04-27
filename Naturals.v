
  (************************************************************************************)
  (*                                                                                  *)
  (* In this file, we construct the natural integers (0, 1, 2, 3 ...) on lists of     *)
  (* empty lists of some arbitrary type which does not even need to be inhabited.     *)
  (* inhabited.                                                                       *)
  (*                                                                                  *)
  (* We prove the induction property over this construct, and then use it abundantly. *)
  (*                                                                                  *)
  (* We define the usual order relations Nle (<=) and Nlt (<) and prove that          *)
  (* Nlt is well-founded.                                                             *)
  (*                                                                                  *)
  (* Then we construct addition and multiplication using general recursion,           *)
  (* using 'Fix' to define them, and 'Fix_eq' to prove mathematicla properties.       *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (************************************************************************************)
  (*                                                                                  *)
  (* But first a bit of philosophy.                                                   *)
  (*                                                                                  *)
  (* If you look at the theorems in the standard library, you will notice that one    *)
  (* of the goals of the Coq team is to use as much automation as possible for        *)
  (* proving theorems.                                                                *)
  (*                                                                                  *)
  (* With such goals, every proof script tend to look like this:                      *)
  (*----------------------------------------------------------------------------------*)
  Comments.

  Goal True.
  Proof. auto. Qed.

  (*----------------------------------------------------------------------------------*)
  (* If you trust the system, this is all fine.                                       *)
  (* That's a theorem, there is a proof, therefore it is true.                        *)
  (* Even if you don't trust the system, you will be told that you can manually print *)
  (* the generated proof and convince yourself, but that something that very few      *)
  (* human being can do.                                                              *)
  (*                                                                                  *)
  (* For example, is what the proof of min_r for nat look like, which asserts that    *)
  (* min n m = m when m <= n.                                                         *)
  (*                                                                                  *)
  (* In case you ever had a doubt, I bet that doubt should be cleared now.            *)
  (*----------------------------------------------------------------------------------*)
  Comments.

  Print min_r.

  (*----------------------------------------------------------------------------------*)
  (* Machines are very happy with these kind of proofs, but not humans.               *)
  (*                                                                                  *)
  (* A proof is also an exercise in communication that seek to convince another       *)
  (* human that what is being claimed is true.                                        *)
  (*                                                                                  *)
  (* This leads to the next caveat. Human-conscious people put a lot of energy into   *)
  (* writing nice proof scripts.                                                      *)
  (*                                                                                  *)
  (* They then use coqdoc to package everything into a beautifully formatted document *)
  (* and then believe that this document contains all the necessary information to    *)
  (* convince someone that may be doubting the result.                                *)
  (*                                                                                  *)
  (* But alas, that's not true. A proof script in Coq is a sequence of operations     *)
  (* used to construct a proof term. It is really like a cooking recipe, but you also *)
  (* need to see the cake raise in the oven and taste it to belive that it is good.   *)
  (*                                                                                  *)
  (* That's why proof scripts should be run, and why you are probably watching this   *)
  (* video, it's to see the proofs in motion.                                         *)
  (************************************************************************************)
  Comments.

  (************************************************************************************)
  (*                                                                                  *)
  (* About the video.                                                                 *)
  (*                                                                                  *)
  (* This video does not contain any perception candy, such as exciting audio         *)
  (* stimutation or graphical special effects. It is actually silent and boring.      *)
  (*                                                                                  *)
  (* You will also probably get lost very quickly if you attempt to watch it at       *)
  (* normal speed. It's more like a slideshow made of a large number of still images, *)
  (* and it goes slow enough that you can reposition yourself at any particular       *)
  (* points of interests, but too fast to keep up with unfamiliar material.           *)
  (*                                                                                  *)
  (* I will provide timestamps to different section to make jumps easier. If I do not *)
  (* please remind me. You may also suggest your own timestamps and I'll add them to  *)
  (* the description.                                                                 *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Technical                                                                    *)
  (*                                                                                  *)
  (* We start with some technical lemmas and notations, to make a few things easier.  *)
  (*                                                                                  *)
  (* Note: Coq offers a 'Section' mechanism, but for some reason, notations defined   *)
  (* in a sections cannot escape them, so that's a bummer. You can use the '>>>'      *)
  (* to locate sections in the file.                                                  *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (* We will define some notations into the 'maths' scope *)
  Declare Scope maths.
  Open Scope maths.

  (* Technical lemma to introduce equality                                            *)
  (* We use this to substitute terms those equality must be proven using        r     *)
  (* proof irrelevance.                                                               *)
  Lemma eq_imp : forall {T:Type} (a b:T) (P:T->Prop), P a -> a = b -> P b.
  Proof.
    intros A a b P h heq.
    (* Since the equality is part of the hypothesis, it will have to be proven        *)
    (* when this lemma is used.                                                       *)
    subst b.
    exact h.
  Qed.

  (* This is the same lemma for any type. *)
  Lemma eq_impT : forall {T:Type} (a b:T) (P:T->Type), P a -> a = b -> P b.
  Proof.
    intros A a b P h heq.
    subst b. exact h.
  Qed.

  (* We use the 'sig' inductive type to construct a collection of elements which are  *)
  (* are guaranteed to satisfy a given property.                                      *)
  (* Then we can use the 'exist' constructor to create an instance of that type.      *)
  Print sig.

  (* Unfortunately, the notation is very verbose, so we define this notation to only  *)
  (* display what is relevant on screen, and keep this '§E' marker to informat that   *)
  (* there is more.                                                                   *)
  Notation "§E x" := (exist _ x _) (only printing, at level 60) : maths.

  (* 'sig' comes with two helper function 'proj1_sig', which retrieve what I call the *)
  (* payload, and 'proj2_sig', whic retrive the proof.                                *)
  (* In Coq, two proofs of the same thing are not equal, so we need to introduce      *)
  (* an axiom of proof irrelevance to focus only on equality of the payload.          *)
  Axiom proof_irrelevance : forall {A:Type} {P:A->Prop} (x y :sig P),
    proj1_sig x = proj1_sig y -> x = y.

  (* This lemma discard any function call when it appears on the both side of an      *)
  (* equality.                                                                        *)
  Lemma f_eq {A B:Type} : forall (f:A->B) (x y:A), x = y ->f x  = f y.
  Proof. intros f x y heq. subst y. reflexivity. Qed.

  (* And this lemma does the same thing for function of two arguments when the left   *)
  (* are equal.                                                                       *)
  (* It's not necessary to define feq_r, because f_eq can be used in this case,       *)
  (* because of currying.                                                             *)
  Lemma feq_l {A B C:Type} : forall (f:A->B->C) n m k, n = m -> f n k = f m k.
  Proof.
    intro f.
    intros n m k.
    intro heq. subst m.
    reflexivity.
  Qed.

  (************************************************************************************)
  (*                                                                                  *)
  (* >>> List                                                                         *)
  (*                                                                                  *)
  (* We don't need to know about about lists, we will only prove the lemmas we need,  *)
  (* but we may add more lemmas in the future, so this section may grow and end up in *)
  (* its own file.                                                                    *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (* This is the classic inductive definition of a list, as in the standard library *)
  Inductive List (A:Type) : Type :=
  | nil : List A
  | cons : A -> List A -> List A.
  Arguments nil {A}.
  Arguments cons {A}.

  (* But we define our own custom notations.                                        *)
  (* We show the empty list as '_' and the cons constructor as '∘l'                 *)
  Notation "'_'" := nil (only printing) : maths.
  Notation "x ∘l y" := (cons x y) (only printing, at level 60) : maths.
  Notation "[ x ]" := (cons x nil) (only printing) : maths.
  Notation "[ x ; y ; .. ; z ]" :=
    (cons x (cons y .. (cons z nil) ..)) (only printing) : maths.

  (************************************************************************************)
  (*                                                                                  *)
  (* Another 'philosophical' note: It is common to define notations both for printing *)
  (* and parsing. We only use notations for printing here.                            *)
  (*                                                                                  *)
  (* This allow changing notations more easily without having to hunt for them in all *)
  (* the source files.                                                                *)
  (*                                                                                  *)
  (* Additionally, displaying notations can be enabled and disabled at will, which    *)
  (* is useful when resolving some ambiguities, while it is not possible to do the    *)
  (* same for notations that appear in source files.                                  *)
  (*                                                                                  *)
  (* Also, we prefer more parentheses rather than operator priority and associativity *)
  (* because this limit the confusion when deciding whether a + b + c                 *)
  (* (a + b) + c or a + (b + c) to know what will happen when using commutativity,    *)
  (* for example.                                                                     *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (* Classic fixpoint definition of append, with use '⋄l' for the notation.           *)
  Fixpoint append {A:Type} (l l' : List A) : (List A) := match l, l' with
  | nil, _ => l'
  | cons head tail, _ => cons head (append tail l')
  end.
  Notation "x ⋄l y" := (append x y) (only printing, at level 60) : maths.

  (* Fixpoint definition to find if an element is in a list.                          *)
  Fixpoint inlist {A:Type} (l:List A) (a:A) := match l with
  | nil => False
  | cons head tail => a=head \/ inlist tail a
  end.

  (* Fixpoint definition of l being longer or equal than m.                           *)
  Fixpoint longerOrEqualThan {A:Type} (l m:List A) := match l, m with
  | nil , nil => True
  | nil , cons _ _ => False
  | cons _ _ , nil  => True
  | cons _ ltail, cons _ mtail => longerOrEqualThan ltail mtail
  end.


  (* A predicate that asserts whether a list is empty *)
  Definition isnil {A:Type} (l:List A) := l = nil.

  (* This predicate is true when the list is nil.                                     *)
  Lemma isnil_nil {A:Type} : isnil (@nil A).
  Proof.
    red.
    reflexivity.
  Qed.

  (* This predicate is true when all elements match a given predicate.                *)
  Fixpoint allmatch {A:Type} (l:List A) (P:A->Prop) := match l with
  | nil => True
  | cons x l' => P x /\ allmatch l' P
  end.



  (* This predicate is true when all the elements of a list of lists are              *)
  (* the nil list.                                                                    *)
  Definition allnil {A:Type} (l:List (List A)) := allmatch l isnil.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Construction                                                                 *)
  (*                                                                                  *)
  (* In this section, we define the naturals as lists of empty lists.                 *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.


  (* The actual type does not matter                                                  *)
  Parameter _NType : Type.

  (************************************************************************************)
  (*                                                                                  *)
  (* About naming conventions:                                                        *)
  (* We prefix 'private' definitions and lemmas with '_', and 'public' lemmas are     *)
  (* unprefixed.                                                                      *)
  (*                                                                                  *)
  (* Things about naturals start 'N', things about integers will start with 'Z'       *)
  (* and similarly for rationals 'Q', reals 'R', complex numbers 'C', matrices 'M'    *)
  (*                                                                                  *)
  (* Many theorems will have to be proven again for other types.                      *)
  (* It is well known that the theorems in the standard library follow different and  *)
  (* conflicting naming conventions, which make it more difficult to find them.       *)
  (*                                                                                  *)
  (* It is one goal of our goals to apply consistent naming conventions so that       *)
  (* names of theorems can be found 'by construction'.                                *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (* We define two levels of lists                                                    *)
  Definition _NLevel1 := List _NType.
  Definition _NLevel2 := List _NLevel1.

  (* A list of lists is 'natural' if all its elements are empty lists.                *)
  Definition isnatural (l:_NLevel2) := allnil l.

  (* We define the type for natural integers as the set of lists which are 'natural', *)
  (* that is to say, lists which are made of empty lists.                             *)
  (*                                                                                  *)
  (* This uses the 'sig' inductive type, which defines an 'exist' constructor         *)
  (* that takes pairs of elements and proofs, where the proof proves that the         *)
  (* the supplied element satisfies the required property.                            *)
  (*                                                                                  *)
  (* Note: We do use the standard notation for sig, because it looks quite natural.   *)
  Definition NN := { l | isnatural l }.

  (* sig comes with two projection functions which do not have very natural names     *)
  (* so we call the first one 'Nlist', which retrives the list,                       *)
  (* and the other one 'Nhyp', which retrieve the hypothesis.                         *)
  Definition Nlist (t:NN) := proj1_sig t.
  Definition Nhyp (t:NN) := proj2_sig t.

  (* We define zero in three steps.                                                   *)
  (* - first, we define the payload of zero, which is an empty list of empty lists.   *)
  (* - next, we prove that this list is 'natural'                                     *)
  (* - last, we use both these things to define the zero as a element of NN.          *)
  Definition _Nzero := @nil _NLevel1.

  (* _Nzero is 'natural' *)
  Theorem  _Nzero_natural : isnatural _Nzero.
  Proof.
    (* Unfold the definitions *)
    red. red. unfold _Nzero.
    (* allmatch on empty lists is always true *)
    simpl. trivial.
  Qed.

  (* This is the zero as type of NN, with a notation                                  *)
  Definition Nzero := exist _ _Nzero _Nzero_natural.
  Notation "0n" := Nzero (only printing) : maths.

  (************************************************************************************)
  (*                                                                                  *)
  (* Note: we will suffix all notations about NN with 'n'.                            *)
  (* This is a bit verbose, and may appear confusing at first, especially for         *)
  (* expressions with a lot of 'n' and 'm' variables.                                 *)
  (*                                                                                  *)
  (* But in the long run, we can immediately see which type we are dealing with,      *)
  (* and we don't have to open and close Coq 'scopes', so this inconvenience bring    *)
  (* some convenience.                                                                *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.


  (* The successor function, which we call 'next', adds an empty list                 *)
  (* to any list of lists.                                                            *)
  Definition _Nnext (n:_NLevel2) : _NLevel2 := cons nil n.

  (* Applying _Nnext on a 'natural' list yields another 'natural' list                *)
  Lemma _Nnext_natural : forall (l:_NLevel2),
    (isnatural l) -> isnatural (_Nnext l).
  Proof.
    (* We first unfold terms to a more convenient level *)
    unfold isnatural. unfold allnil.
    (* We only need to distinguish the empty list from any other lists *)
    intro l.
    destruct l as [|head tail].
    (* l is empty *)
    {
      intros _. simpl. split.
      { red. reflexivity. }
      { trivial. }
    }
    (* l is not empty *)
    {
      simpl. intros [hhead htail].
      unfold isnil in hhead. subst head.
      split.
      { red. reflexivity. }
      {
        split.
        { red. reflexivity. }
        { exact htail. }
      }
    }
  Qed.

  (* For Nnext, we have to construct a new natural using the proof _Nnext_natural.    *)
  Definition Nnext (n:NN) := exist _
    (_Nnext (Nlist n))
    (_Nnext_natural (Nlist n) (Nhyp n)).

  (* This is a rather unconventional notation for 'next', you may think of better       *)
  (* Note: the notation is '\', suffixed with 'n' for 'naturals', so don't think about  *)
  (* removing the 'n' if you suggest another notation.                                  *)
  Notation "\n x" := (Nnext x) (only printing, at level 60) : maths.

  (* Here are one and two *)
  Definition None := Nnext Nzero.
  Notation "1n" := None (only printing) : maths.

  Definition Ntwo := Nnext None.
  Notation "2n" := Ntwo (only printing) : maths.

  (************************************************************************************)
  (*                                                                                  *)
  (* I know, 'None' is a very poor name for 'one'. Same is 'Zone' for the integers,   *)
  (* and 'Cone' for the complex numbers.                                              *)
  (*                                                                                  *)
  (* Logical consistency in naming conventions yields sometimes suprising results,    *)
  (* but I'll stick with that because any other numbers works fine.                   *)
  (*                                                                                  *)
  (* Yes, yes, I know, the standard library uses 'None' for the 'option' type.        *)
  (* That's not a complicated inductive type, and I'll redefine it with 'Null' if I   *)
  (* if I need to.                                                                    *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (* n = m -> next n = next m *)
  (* This is actually subsumed by 'f_eq', but it looks more natural to have a         *)
  (* dedicated lemma for that.                                                        *)
  Lemma Nnext_intro : forall n m, n = m -> Nnext n = Nnext m.
  Proof.
    intros n m heq. subst n. reflexivity.
  Qed.

  (* next is injective *)
  (* next n = next m -> n = m  *)
  Lemma Nnext_elim : forall (n m:NN), Nnext n = Nnext m -> n = m.
  Proof.
    (* Destruct n and m *)
    intros [nl hn] [ml hm].
    (* Unfold, simplify, and use proof irrelevance and inversion *)
    (* to get to the actual lists.                               *)
    unfold Nnext. unfold _Nnext. simpl. intro heq.
    apply proof_irrelevance. simpl.
    (* inversion is quite powerful, and automatically identifies and discard *)
    (* the common 'nil'. The weird 'in heq' part prevents the tactic from    *)
    (* changing the goal                                                     *)
    inversion heq as [heql] in heq. clear heq. clear hn hm.
    (* And there we go *)
    subst ml. reflexivity.
  Qed.

  (************************************************************************************)
  (* One of the most useful thing is to prove an induction principle over NN.         *)
  (* For inductive types such as nat, the induction principles are created            *)
  (* automatically by Coq for types, propositions and sets:                           *)
  (*----------------------------------------------------------------------------------*)
  Print nat.
  Check nat_rect.
  Check nat_ind.
  Check nat_rec.
  (*----------------------------------------------------------------------------------*)
  (* But since NN is not an inductive type, we have to prove it ourselve              *)
  (************************************************************************************)

  (* Induction principle for NN over types *)
  Theorem NinductionT : forall (P: NN -> Type),
    (P Nzero) ->
    (forall n, P n -> P (Nnext n)) ->
    (forall n, P n).
  Proof.
    (* Here's the proposition that must be proven for all naturals *)
    intro P.
    (* We know it is true for zero *)
    intro hzero.
    (* And we now that whenever it holds for one number, it holds for its successor *)
    intro hnext.
    (* So we have to prove that it holds for that arbitrary number n *)
    intro n.
    (* We break n into its parts *)
    destruct n as [ln hn] eqn:heqn.
    (* We will proceed by induction on the list, and we put back n in the goal to have *)
    (* more flexible induction hypothesis that holds for any n.                        *)
    generalize dependent n.
    induction ln as [|head tail ih].
    (* ln = nil *)
    {
      clear hnext. intro n. intro heqn.
      (* We use our technical lemma to bind the goal with hzero *)
      eapply (eq_impT _ _ P).
      { exact hzero. }
      { apply proof_irrelevance. simpl. unfold _Nzero. reflexivity. }
    }
    (* Induction step *)
    {
      (* Goal is to link 'hnext' and 'ih' *)
      clear hzero.
      intro n. intro heqn.
      (* Massage the hypotheses *)
      unfold isnatural in hn. unfold allnil in hn. simpl in hn.
      destruct hn as [hnil hmatch].
      unfold isnil in hnil. subst head.
      (* Prepare the injection hypothesis *)
      unfold isnatural in ih. unfold allnil in ih.
      specialize (ih hmatch).
      (* Construct a natural number from the tail *)
      set (pred:=exist _ tail hmatch:NN).
      (* Feed pred to hnext and ih *)
      specialize (hnext pred).
      specialize (ih pred).
      (* Here we use our technical lemma twice, and let Coq fill most of the details *)
      (* Additionally, eapply will let us create the equalities on the fly           *)
      eapply (eq_impT _ _).
      (* I leave the other goals visible so that we can see them chaning as we go *)
      apply hnext.
      eapply (eq_impT _ _).
      apply ih.
      subst pred. apply proof_irrelevance. simpl. reflexivity.
      apply f_eq. subst pred. apply proof_irrelevance. simpl. reflexivity.
      apply f_eq. subst pred. apply proof_irrelevance. simpl. reflexivity.
    }
  Defined.

  (************************************************************************************)
  (* To prove Ninduction, we reuse NinductionT                                        *)
  (* That's a big weird, because 'Prop' is of type 'Type', but what holds for types   *)
  (*  also hold for props.                                                            *)
  (*----------------------------------------------------------------------------------*)
  Check Prop.
  Goal forall (P:Type->Prop), (forall (T:Type), P T) -> (forall (P':Prop), P P').
    (* P maps a Type to a Prop *)
    intro P.
    (* h says that P holds for all types *)
    intro h.
    (* P' is of type 'Prop' *)
    intro P'.
    (* And here, we can mysteriously apply h, which takes a thing of type 'Type', *)
    (* to 'P', which is of type 'Prop', which is of type 'Type'                   *)
    specialize (h P').
    (* And that works! *)
    exact h.
  Abort.

  (* So the proof if quite straightforward once you accept that fact *)
  Theorem Ninduction : forall (P: NN -> Prop),
    (P Nzero) ->
    (forall n, P n -> P (Nnext n)) ->
    (forall n, P n).
  Proof.
    intros P hzero hnext n.
    apply NinductionT.
    { exact hzero. }
    { intros n' h. apply hnext. exact h. }
  Defined.

  (* The same is true for Set *)
  Check Set.
  Goal forall (P:Type->Prop), (forall (T:Type), P T) -> (forall (S:Set), P S).
    intro P.
    intro h.
    intro S.
    (* Mysterious apply *)
    specialize (h S).
    (* And that works! *)
    exact h.
  Abort.

  (* Again, the proof of induction over sets is straightforward *)
  Theorem NinductionS : forall (P: NN -> Set),
    (P Nzero) ->
    (forall n, P n -> P (Nnext n)) ->
    (forall n, P n).
  Proof.
    intros P hzero hnext n.
    apply NinductionT.
    { exact hzero. }
    { intros n' h. apply hnext. exact h. }
  Defined.

  (************************************************************************************)
  (* To write functions over NN, it is sometimes necessary to prove                   *)
  (* that equality is decidable                                                       *)
  (* This means that given two naturals n and m, we have an actual program that can   *)
  (* inspect those numbers and decide equality.                                       *)
  (* This is specified with 'sumbool', which with an inductive type other Set         *)
  (*----------------------------------------------------------------------------------*)
  Print sumbool.

  (* Equality is decidable *)
  Definition Neq_dec (n m:NN) : sumbool (n = m) (n <> m).
  Proof.
    (* Break n and m into their parts *)
    destruct n as [nl hn];
    destruct m as [ml hm].
    (* Induction over nl with flexible ml *)
    generalize dependent ml.
    induction nl as [|headn tailn ihn].
    (* nl is nil *)
    {
      intros ml hm.
      destruct ml as [|headm tailm].
      (* ml is nil, so we have equality *)
      { left. apply proof_irrelevance. simpl. reflexivity. }
      (* ml is not nil, so we use inversion to prove inequality *)
      { right. unfold not. intro heq. inversion heq. }
    }
    (* Induction step *)
    {
      intros ml hm.
      (* Again, we destruct m *)
      destruct ml as [|headm tailm].
      (* m is nil, so we have inequality *)
      { right. unfold not. intro heq. inversion heq. }
      (* m is not nil *)
      {
        (* Massage the hypotheses *)
        unfold isnatural in hn, hm.
        unfold allnil in hn, hm.
        simpl in hn, hm.
        destruct hn as [hniln htailn];
        destruct hm as [hnilm htailm].
        red in hniln, hnilm.
        subst headn headm.
        (* Prepare the induction hypothesis with the tails *)
        specialize (ihn htailn).
        specialize (ihn tailm).
        specialize (ihn htailm).
        (* Examine each case in the induction hypothesis *)
        destruct ihn as [ihn|ihn].
        (* Equality case *)
        {
          inversion ihn as [heq] in ihn.
          subst tailm.
          left. apply proof_irrelevance. simpl. reflexivity.
        }
        (* Inequality case *)
        {
          right.
          unfold not. intro heq.
          inversion heq as [heql] in heq.
          subst tailm.
          unfold not in ihn.
          apply ihn.
          apply proof_irrelevance. simpl. reflexivity.
        }
      }
    }
  Defined.

  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Order                                                                        *)
  (*                                                                                  *)
  (* In this section, we define the order relation on naturals and prove some of its  *)
  (* properties.                                                                      *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  (************************************************************************************)
  (* We define ordering by inspecting the length of the associated list,              *)
  (* using 'longerOrEqualThan' that we previously defined for that purpose            *)
  (*----------------------------------------------------------------------------------*)
  Print longerOrEqualThan.

  (* Nle is '<=' *)
  Definition Nle (n m:NN) := longerOrEqualThan (Nlist m) (Nlist n).
  Notation "x <=n y" := (Nle x y) (only printing, at level 60) : maths.

  (* Nlt is '<' *)
  Definition Nlt (n m:NN) := Nle (Nnext n) m.
  Notation "x <n y" := (Nlt x y) (only printing, at level 60) : maths.

  (* Nle is decidable *)
  (* We'll use this to define min and max, and this will be used later for the        *)
  (* construction of the integers.                                                    *)
  Definition Nle_dec n m : sumbool (Nle n m) (Nle m n).
  Proof.
    (* Break n and m into their parts *)
    destruct n as [nl hn];
    destruct m as [ml hm].
    unfold Nle. simpl. clear hn.
    generalize dependent ml.
    induction nl as [|headn tailn ihn].
    (* nl is nil *)
    {
      intros m _.
      destruct m as [|headm tailm].
      { simpl. left. trivial. }
      { simpl. left. trivial. }
    }
    (* n is not nil *)
    {
      intros m hm.
      destruct m as [|headm tailm].
      { simpl. right. trivial. }
      {
        (* Massage the hypotheses *)
        simpl. unfold isnatural in *. unfold allnil in *. simpl in *.
        destruct hm as [hheadm htailm]. unfold isnil in hheadm. subst headm.
        (* Prepare the induction hypothese *)
        specialize (ihn tailm). specialize (ihn htailm).
        (* Look at each cases *)
        destruct ihn as [ihn|ihn].
        { left. exact ihn. }
        { right. exact ihn. }
      }
    }
  Defined.

  (* Nle is reflexive : forall n, n <= n *)
  Theorem Nle_refl : forall n:NN, Nle n n.
  Proof.
    intros (nl,hn).
    unfold Nle. simpl. clear hn.
    induction nl as [|head tail ih].
    { simpl. trivial. }
    { simpl. exact ih. }
  Qed.


  (* Nle is transitive : forall n m k, n <= m -> m <= k -> n <= k *)
  Lemma Nle_trans : forall n m k, Nle n m -> Nle m k -> Nle n k.
  Proof.
    (* This proof is more involved because there are many subcases *)
    intros (nl,hn) (ml,hm) (kl,hk).
    unfold Nle. simpl.
    clear hn hm hk.
    generalize dependent ml.
    generalize dependent nl.
    induction kl as [|headk tailk ih].
    (* kl is nil *)
    {
      simpl.
      (* Simpl is a bit too offensive here, but whenever a match is unfolded like this,
         it's a hint to use "destruct" *)
      intros nl ml h.
      destruct ml as [|headm tailm].
      (* ml is nil *)
      {
        destruct nl as [|headn tailn].
        (* nl is nil *)
        { intros _. trivial. }
        (* nl is not nil *)
        { simpl in h. inversion h. }
      }
      (* ml is not nil *)
      { intro f. inversion f. }
    }
    (* Induction step for kl *)
    {
      intros nl ml hmn hkm.
      simpl. simpl in hkm.
      destruct nl as [|headn tailn].
      (* nl is nil *)
      { trivial. }
      (* nl is not nil *)
      {
        destruct ml as [|headm tailm].
        (* ml is nil *)
        { simpl in *. inversion hmn. }
        (* nl, ml and kl are not nil *)
        {
          (* Here we use the induction hypothesis *)
          simpl in *.
          eapply ih.
          { apply hmn. }
          { apply hkm. }
        }
      }
    }
  Qed.

  (* Nle is antisymmetric: forall n m, n <= m -> m <= n -> n = m. *)
  Lemma Nle_antisym : forall n m, Nle n m -> Nle m n -> n = m.
  Proof.
    intros (nl,hn) (ml,hm).
    unfold Nle. simpl.
    generalize dependent ml.
    induction nl as [|headn tailn ih].
    (* n is nil *)
    {
      intros ml hm.
      destruct ml as [|headm tailm].
      (* ml is nil *)
      { simpl. intros _ _. apply proof_irrelevance. simpl. reflexivity. }
      (* ml is not nil, so we have a contradiction *)
      { simpl. intros _ f. inversion f. }
    }
    (* Induction step for nl *)
    {
      intros ml hm.
      destruct ml as [|headm tailm].
      (* ml is nil, so we have a contradiction *)
      { simpl. intro f. inversion f. }
      (* ml is not nil, so we use the induction hypothesis *)
      {
        simpl.
        (* Massage the hypotheses *)
        unfold isnatural in *.
        unfold allnil in *.
        simpl in *.
        destruct hn as [hheadn htailn].
        destruct hm as [hheadm htailm].
        unfold isnil in hheadn, hheadm.
        subst headn headm.
        intros hmn hnm.
        (* Prepare the induction *)
        specialize (ih htailn).
        specialize (ih tailm).
        specialize (ih htailm).
        specialize (ih hmn).
        specialize (ih hnm).
        (* Use inversion to extract tailn = tailm equality *)
        inversion ih.
        subst tailm.
        (* Use proof irrelevance to prove the equality, discarding the proofs *)
        apply proof_irrelevance. simpl. reflexivity.
      }
    }
  Qed.

  (* "<" is irreflexive : if n < n, then that's a contradiction *)
  Lemma Nlt_irrefl : forall n, Nlt n n -> False.
  Proof.
    intros (nl, hn).
    unfold Nlt. unfold Nle. simpl.
    induction nl as [|head tail ih].
    (* n is nil *)
    { unfold _Nnext. simpl. intro f. exact f. }
    (* Induction case *)
    {
      (* Massage the hypotheses *)
      intro h. simpl in *. unfold isnatural in *. unfold allnil in *. simpl in *.
      destruct hn as [hnil hmatch].
      red in hnil. subst head.
      (* Prepare the induction hypothese *)
      specialize (ih hmatch). clear hmatch.
      unfold _Nnext in ih.
      (* Use the induction hypothese *)
      apply ih. exact h.
    }
  Qed.

  (* next n <= next m => n <= m *)
  Lemma Nle_next_elim : forall n m, Nle (Nnext n) (Nnext m) -> Nle n m.
  Proof.
    intros (nl,hn) (ml,hm).
    unfold Nle. simpl. clear hn hm.
    intro h. exact h.
  Qed.

  (* If n <= m, then next n <= next m *)
  Lemma Nle_next_intro : forall n m, Nle n m -> Nle (Nnext n) (Nnext m).
  Proof.
    intros (nl,hn) (ml,hm).
    unfold Nle. simpl. clear hn hm.
    intro h. exact h.
  Qed.

  (* n <= next n *)
  Lemma Nle_next : forall n, Nle n (Nnext n).
  Proof.
    intro n.
    (* Here we're using our custom induction principle for the first time :) ! *)
    induction n as [|n ih] using Ninduction.
    { unfold Nle. simpl. trivial. }
    { apply Nle_next_intro. exact ih. }
  Qed.

  (* 0 <= n *)
  Lemma Nle_zero_l : forall n, Nle Nzero n.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    { apply Nle_refl. }
    {
      apply Nle_trans with n.
      { exact ih. }
      { apply Nle_next. }
    }
  Qed.

  (* n <= 0 -> n = 0 *)
  Lemma Nle_zero_r : forall n, Nle n Nzero -> n = Nzero.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    { intros _. reflexivity. }
    { intro h. inversion h. }
  Qed.



  (************************************************************************************)
  (* To define recursive function in Coq, we can use Fixpoint and recursion on        *)
  (* syntactic subterms of inductive types.                                           *)
  (* But NN is not an inductive type.                                                 *)
  (* One solution is to prove a well founded property of a relation,                  *)
  (* then use that well foundedness property to define recursive function using       *)
  (* Fix and Fix_eq.                                                                  *)
  (* So far, I cannot claim that's an easy thing to do.                               *)
  (************************************************************************************)

  (* The "<" relation is well_founded *)
  Lemma Nlt_wf: well_founded Nlt.
  Proof.
    (* I don't understand this proof very well *)
    red. intro a.
Print Acc.
    (* We have to prove this *)
    apply Acc_intro.
    (* So we know 'a', and we have to prove that for any 'y' that is strictly less *)
    (* than 'a', y is ... what?                                                    *)
    induction a as [|a ih] using Ninduction.
    (* a is zero *)
    {
      (* That vacuously true... ok *)
      intros y h. unfold Nlt in h. contradiction h.
    }
    {
      intros b hb.
      (* So we have a 'b', let's find a 'c' too, why not ? *)
      apply Acc_intro.
      intro c. intro hc.
      (* And we can apply ih by transitivity *)
      apply ih. clear ih.
      unfold Nlt in *.
      apply Nle_next_elim in hb.
      apply Nle_trans with b.
      exact hc. exact hb.
      (* So it's true... whatever it is, and Nlt is well founded. *)
    }
  Defined.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Rest                                                                         *)
  (*                                                                                  *)
  (* To use recursion, we will have to go down by one, but that's harder to do that   *)
  (* it looks, becaus not every number has a predecessor.                             *)
  (*                                                                                  *)
  (* So we define a 'rest' function, which given two numbers n and m,                 *)
  (* gives the number k such that n + k = m or n = k + m                              *)
  (*                                                                                  *)
  (* That's a bit unconventional, but probably better than defining pred 0 = 0        *)
  (* as they do in the standard library.                                              *)
  (************************************************************************************)
  Comments.

  (* I'm not joking, pred 0 = 0 *)
  Print Nat.pred.

  Fixpoint _Nrest {A:Type} (l m: List A) : (List A) := match l, m with
  | nil, nil => nil
  | nil, cons _ _ =>  m
  | cons _ _, nil =>  l
  | cons _ tailn, cons _ tailm =>  _Nrest tailn tailm
  end.

  Lemma _Nrest_natural : forall l m, isnatural l -> isnatural m ->
    isnatural (_Nrest l m).
  Proof.
    intro l.
    induction l as [|headl taill ih].
    (* l is nil *)
    {
      destruct m as [|headm tailm].
      (* m is nil *)
      { simpl. intros h _. exact h. }
      (* m is not nil *)
      { simpl. intros _ h. exact h. }
    }
    (* induction case *)
    {
      destruct m as [|headm tailm].
      (* m is nil *)
      { simpl. intros h _. exact h. }
      (* m is not nil, so we use the induction hypothesis *)
      {
        intros hl hm. simpl.
        apply ih.
        { apply hl. }
        { apply hm. }
      }
    }
  Qed.

  (* We can now define Nrest over NN *)
  Definition Nrest (n m:NN) :=
    let (nl, hn) := n in
    let (ml, hm) := m in
    exist _ (_Nrest nl ml) (_Nrest_natural nl ml hn hm).

  (* Fun fact: the 'rest' function is commutative *)
  Lemma Nrest_comm : forall n m, Nrest n m = Nrest m n.
  Proof.
    intros (nl,hn) (ml,hm).
    generalize dependent ml.
    unfold isnatural in *. unfold allnil in *.
    induction nl as [|headn tailn ih].
    (* nl is nil *)
    {
      intros ml hm.
      destruct ml as [|headm tailm].
      (* ml is nil *)
      { simpl. apply proof_irrelevance. simpl. reflexivity. }
      (* ml is not nil *)
      {
        simpl in hm. destruct hm as [hheadm htailm].
        unfold isnil in hheadm. subst headm.
        simpl. apply proof_irrelevance. simpl. reflexivity.
      }
    }
    (* Induction step *)
    {
      intros ml hm.
      destruct ml as [|headm tailm].
      (* ml is nil *)
      { simpl. apply proof_irrelevance. simpl. reflexivity. }
      (* ml is not nil, and we use the induction hypothesis *)
      {
        simpl. apply proof_irrelevance. simpl.
        simpl in hn, hm.
        destruct hn as [hheadn htailn].
        destruct hm as [hheadm htailm].
        unfold isnil in hheadn, hheadm.
        subst headn headm.
        specialize (ih htailn _ htailm).
        inversion ih as [heq]. clear ih.
        rewrite heq.
        reflexivity.
      }
    }
  Qed.

  (* rest 0 n = n *)
  Lemma Nrest_zero_l : forall n, Nrest Nzero n = n.
  Proof.
    intros (nl, hn). simpl.
    destruct nl as [|head tail].
    { apply proof_irrelevance. simpl. reflexivity. }
    { apply proof_irrelevance. simpl. reflexivity. }
  Qed.

  (* rest n 0 = n *)
  Lemma Nrest_zero_r : forall n, Nrest n Nzero  = n.
  Proof.
    intro n. rewrite Nrest_comm. apply Nrest_zero_l.
  Qed.

  (* rest n n = 0 *)
  (* I'm not sure if that kind of property has a special name *)
  Lemma Nrest_cancel : forall n, Nrest n n = Nzero.
  Proof.
    (* Go down to list again *)
    intros (nl, hn).
    simpl.
    generalize dependent hn.
    induction nl as [|head tail ih].
    (* nl is nil *)
    {
      simpl. intro hn.
      apply proof_irrelevance. simpl. unfold _Nzero. reflexivity.
    }
    (* Induction step *)
    {
      intro hn.
      (* Massage the hypotheses *)
      simpl in *.
      unfold isnatural in *.
      unfold allnil in *.
      simpl in *.
      destruct hn as [hhead htail].
      unfold isnil in hhead.
      subst head.
      (* Prepare the induction hypothesis *)
      specialize (ih htail).
      (* Use the technical lemma to bind the two equality together *)
      eapply eq_imp.
      2:{ apply ih. }
      { apply proof_irrelevance. simpl. reflexivity. }
    }
  Qed.

  (* rest (next n) (next m) = rest n m *)
  Lemma Nrest_next : forall n m, Nrest (Nnext n) (Nnext m) = Nrest n m.
  Proof.
    intros (nl, hn) (ml, hm).
    (* Coq will simplify calls to 'next' during evaluation  *)
    destruct nl as [|headn tailn].
    (* nl is nil *)
    {
      destruct ml as [|headm tailm].
      (* ml is nil *)
      { simpl. apply proof_irrelevance. simpl. reflexivity. }
      (* ml is not nil *)
      { simpl. apply proof_irrelevance. simpl. reflexivity. }
    }
    (* nl is not nil *)
    {
      destruct ml as [|headm tailm].
      (* ml is nil *)
      { simpl. apply proof_irrelevance. simpl. reflexivity. }
      (* ml is not nil *)
      { simpl. apply proof_irrelevance. simpl. reflexivity. }
    }
  Qed.

  (* n <> zero -> (rest n 1) < n *)
  (* Technical lemma to prove stuff when defining recursive functions *)
  Lemma Nrest_one_lt : forall n:NN, Nzero <> n -> Nlt (Nrest n None) n.
  Proof.
    intro n.
    induction n as [|n _] using Ninduction.
    (* n is zero *)
    { intro f. contradiction f. reflexivity. }
    {
      intros _.
      unfold None.
      rewrite Nrest_next.
      rewrite Nrest_zero_r.
      unfold Nlt.
      apply Nle_refl.
    }
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Min and max                                                                  *)
  (*                                                                                  *)
  (* Min and max are will be necessary when constructing the integers later.          *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

  Definition Nmin n m := match Nle_dec n m with
  | left _ => n
  | right _ => m
  end.

  (* min is commutative *)
  Lemma Nmin_comm : forall n m, Nmin n m = Nmin m n.
  Proof.
    intros n m. unfold Nmin.
    (* We simply examine all possibilities and use antisymmetry of Nle *)
    destruct (Nle_dec n m) as [dnm|dnm];
    destruct (Nle_dec m n) as [dmn|dmn].
    { apply Nle_antisym. exact dnm. exact dmn. }
    { reflexivity. }
    { reflexivity. }
    { apply Nle_antisym. exact dnm. exact dmn. }
  Qed.

  (* min 0 n = 0 *)
  Lemma Nmin_zero_l : forall n, Nmin Nzero n = Nzero.
  Proof.
    intro n. unfold Nmin.
    destruct (Nle_dec _) as [d|d].
    { reflexivity. }
    { apply Nle_zero_r in d. subst n. reflexivity. }
  Qed.

  (* min n 0 = 0 *)
  Lemma Nmin_zero_r : forall n, Nmin n Nzero = Nzero.
  Proof.
    intro n. rewrite Nmin_comm. rewrite Nmin_zero_l. reflexivity.
  Qed.

  (* min n n = n *)
  Lemma Nmin_cancel : forall n, Nmin n n  = n.
  Proof.
    intro n. unfold Nmin.
    destruct (Nle_dec _) as [d|d].
    reflexivity. reflexivity.
  Qed.

  (* min (next n) (next m) = min n m *)
  Lemma Nmin_next : forall n m, Nmin (Nnext n) (Nnext m)  = Nnext (Nmin n m).
  Proof.
    intros n m. unfold Nmin.
    destruct (Nle_dec _) as [d1|d1];
    destruct (Nle_dec _) as [d2|d2].
    { reflexivity. }
    { apply Nle_antisym. exact d1. apply Nle_next_intro. exact d2. }
    { apply Nle_antisym. exact d1. apply Nle_next_intro. exact d2. }
    { reflexivity. }
  Qed.

  (* min n m = n -> n <= m *)
  Lemma Nmin_le : forall n m, Nmin n m = n -> Nle n m.
  Proof.
    intros n m h. unfold Nmin in h.
    destruct (Nle_dec _) as [d|d].
    { exact d. }
    { subst m. exact d. }
  Qed.

  Definition Nmax n m := match Nle_dec n m with
  | left _ => m
  | right _ => n
  end.

  (* max is commutative *)
  Lemma Nmax_comm : forall n m, Nmax n m = Nmax m n.
  Proof.
    intros n m. unfold Nmax.
    destruct (Nle_dec n m) as [dnm|dnm];
    destruct (Nle_dec m n) as [dmn|dmn].
    { apply Nle_antisym. exact dmn. exact dnm. }
    { reflexivity. }
    { reflexivity. }
    { apply Nle_antisym. exact dmn. exact dnm. }
  Qed.

  (* max 0 n = n *)
  Lemma Nmax_zero_l : forall n, Nmax Nzero n = n.
  Proof.
    intro n. unfold Nmax.
    destruct (Nle_dec _) as [d|d].
    { reflexivity. }
    { apply Nle_zero_r in d. subst n. reflexivity. }
  Qed.

  (* max n 0 = n *)
  Lemma Nmax_zero_r : forall n, Nmax n Nzero = n.
  Proof.
    intro n. rewrite Nmax_comm. rewrite Nmax_zero_l. reflexivity.
  Qed.

  (* max n n = n *)
  Lemma Nmax_cancel : forall n, Nmax n n  = n.
  Proof.
    intro n. unfold Nmax.
    destruct (Nle_dec _) as [d|d].
    reflexivity. reflexivity.
  Qed.

  (* max (next n) (next m) = max n m *)
  Lemma Nmax_next : forall n m, Nmax (Nnext n) (Nnext m)  = Nnext (Nmax n m).
  Proof.
    intros n m. unfold Nmax.
    destruct (Nle_dec _) as [d1|d1];
    destruct (Nle_dec _) as [d2|d2].
    { reflexivity. }
    { apply Nle_antisym. apply Nle_next_intro. exact d2. exact d1. }
    { apply Nle_antisym. exact d2. apply Nle_next_intro. exact d1. }
    { reflexivity. }
  Qed.

  (* max n m = n -> m <= n *)
  Lemma Nmax_le : forall n m, Nmax n m = n -> Nle m n.
  Proof.
    intros n m h. unfold Nmax in h.
    destruct (Nle_dec _) as [d|d].
    { subst m. exact d. }
    { exact d. }
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Addition                                                                     *)
  (*                                                                                  *)
  (* We are about to define addition using Fix.                                       *)
  (* That's still quite confusing to me, and I had to go through a lot of trial       *)
  (* and error and copy/pasting from the Internet to arrive at this                   *)
  (*                                                                                  *)
  (* Here are some resources:                                                         *)
  (*                                                                                  *)
  (* - https://stackoverflow.com/questions/49846632                                   *)
  (* - http://adam.chlipala.net/cpdt/html/GeneralRec.html                             *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.


  (* In SO 49846632, he defines a custom thing like this, so I do the same *)
  Definition _NRecType (a : NN) := forall b : NN, NN.

  (* Then he used that type as such to define the recursive body of the function *)
  (* This function is constructed instead of being defined.                      *)
  Definition _Nplus_rec : forall x : NN,
    (forall y : NN,(Nlt y x) -> _NRecType y) -> _NRecType x.
    (* I thinks that's the input on the left side of 'plus' *)
    intro x.
    (* That's the recursive 'function' to do the iteration with *)
    intro rec.
    (* We can unfold that thing *)
    unfold _NRecType.
    (* And I believe that is the input on the right side of 'plus' *)
    intro y.
    (* If x is zero, we return y, otherwise, we do an iteration *)
    destruct (Neq_dec Nzero x) as [d|d].
    (* Case x = 0 *)
    { apply y. }
    (* Recursive case *)
    {
      (* We want to go down by one, and that's (rest x 1) *)
      (* So the first thing we give to 'rec' is the value for the next iteration *)
      specialize (rec (Nrest x None)).
      (* We need to prove that we are actually going down *)
      apply Nrest_one_lt in d. specialize (rec d). clear d.
      (* Now we unfold the thing again *)
      unfold _NRecType in rec.
      (* I think that's the right hand side for the next iteration *)
      specialize (rec y).
      (* And this is what we do with the result of the next iteration *)
      apply (Nnext rec).
    }
    (* Simple, isn't it ? *)
  Defined.

  (* This is the obligation that Fix_eq requires everytime we use it *)
  Lemma _Nplus_rec_ok: forall (x : NN)
    (f g : forall y : NN, Nlt y x -> _NRecType y),
    (forall (y : NN) (p : Nlt y x), f y p = g y p)
    -> _Nplus_rec x f = _Nplus_rec x g.
  Proof.
    intros x f g h.
    unfold _Nplus_rec.
    destruct (Neq_dec _) as [_|d].
    { reflexivity. }
    { rewrite h. reflexivity. }
  Qed.

  (* We just have to give the proof that Nlt is well founded and the recursive body *)
  (* to Fix, and voila !                                                            *)
  Definition Nplus := Fix Nlt_wf _ _Nplus_rec.
  Notation "x +n y" := (Nplus x y) (only printing, at level 50) : maths.

  (* In the remaining of this section, we prove the usual properties of addition *)

  (* 0 + n = n *)
  Lemma Nplus_zero_l : forall n, Nplus Nzero n = n.
  Proof.
    (* The strategy here is to unfold the fixpoint to go straight into the base case *)
    intro n.
    (* unfold these three things *)
    unfold Nplus.
    unfold _Nplus_rec.
    unfold Fix.
    (* This simplifies *)
    simpl.
    (* magic *)
    reflexivity.
  Qed.

  (* n + 0 = n *)
  Lemma Nplus_zero_r : forall n, Nplus n Nzero = n.
  Proof.
    (* For the other side, we don't know commutativity yet, so we have to proceed *)
    (* by induction                                                               *)
    intro n.
    induction n as [|n ih] using Ninduction.
    (* n = 0 *)
    { rewrite Nplus_zero_l. reflexivity. }
    (* Induction step *)
    {
      (* We can use Fix_eq to unfold one step *)
      unfold Nplus.
      rewrite Fix_eq.
      2:{ apply _Nplus_rec_ok. }
      {
        (* If you can read this, you're lucky, all I know is that I can unfold _Nplus_rec *)
        unfold _Nplus_rec.
        (* We can destroy the if pat *)
        destruct (Neq_dec _) as [d|_].
        { inversion d. }
        {
          (* The strategy is to rewrite, then refold *)
          unfold None at 2.
          rewrite Nrest_next.
          rewrite Nrest_zero_r.
          fold _Nplus_rec. fold Nplus.
          (* Remove 'next' on both sides *)
          (* Note: it's not obvious that it is (Nnext (Nplus n Nzero)) and not       *)
          (* Nplus (Nnext n) Nzero, we should improve the notation to add clarifying *)
          (* parentheses if you know how to do that.                                 *)
          apply Nnext_intro.
          (* And we're done! *)
          exact ih.
        }
      }
    }
  Qed.

  (* The strategy for proving other properties is similar: unfold, rewrite, refold *)
  (* (next n) + m = next (n+m) *)
  Lemma Nplus_next_l : forall n m, Nplus (Nnext n) m = Nnext (Nplus n m).
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    (* n = 0 *)
    {
      intro m.
      rewrite Nplus_zero_l.
      unfold Nplus.
      rewrite Fix_eq.
      2:{ apply _Nplus_rec_ok. }
      {
        unfold _Nplus_rec.
        destruct (Neq_dec _) as [d|d].
        { inversion d. }
        {
          unfold None at 2.
          rewrite Nrest_cancel.
          apply f_eq.
          unfold Fix.
          simpl.
          (* yeah ! *)
          reflexivity.
        }
      }
    }
    (* Induction case *)
    {
      intro m.
      rewrite ih. clear ih.
      unfold Nplus at 1.
      rewrite Fix_eq.
      2:{ apply _Nplus_rec_ok. }
      {
        unfold _Nplus_rec at 1.
        destruct (Neq_dec _) as [d|_].
        { inversion d. }
        {
          apply Nnext_intro.
          unfold None.
          rewrite Nrest_next.
          rewrite Nrest_zero_r.
          unfold Nplus.
          (* Too bad, we need to unfold again *)
          rewrite Fix_eq.
          2:{ apply _Nplus_rec_ok. }
          {
            unfold _Nplus_rec at 1.
            destruct (Neq_dec _) as [d|_].
            { inversion d. }
            {
              unfold None at 1.
              rewrite Nrest_next.
              rewrite Nrest_zero_r.
              fold Nplus.
              (* yipee ! *)
              reflexivity.
            }
          }
        }
      }
    }
  Qed.

  (* n + (next m) = next (n+m) *)
  Lemma Nplus_next_r : forall n m, Nplus n (Nnext m) = Nnext (Nplus n m).
  Proof.
    intros n.
    induction n as [|n ih] using Ninduction.
    (* n = 0 *)
    {
      intro m.
      rewrite Nplus_zero_l. rewrite Nplus_zero_l.
      reflexivity.
    }
    (* Induction case *)
    {
      intro m.
      rewrite Nplus_next_l.
      rewrite Nplus_next_l.
      rewrite ih.
      reflexivity.
    }
  Qed.

  (* Addition is commutative *)
  Lemma Nplus_comm : forall n m, Nplus n m = Nplus m n.
  Proof.
    (* Using the previous lemmas, this is easy *)
    intro n.
    induction n as [|n ih] using Ninduction.
    (* n = 0 *)
    { intro m. rewrite Nplus_zero_l. rewrite Nplus_zero_r. reflexivity. }
    (* Induction step *)
    { intro m. rewrite Nplus_next_l. rewrite Nplus_next_r. rewrite ih. reflexivity. }
  Qed.

  (* Addition is associative *)
  Lemma Nplus_assoc : forall n m k, Nplus n (Nplus m k) = Nplus (Nplus n m) k.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    (* n = 0 *)
    { intros m k. rewrite Nplus_zero_l. rewrite Nplus_zero_l. reflexivity. }
    {
      intros m k.
      rewrite Nplus_next_l. rewrite Nplus_next_l. rewrite Nplus_next_l.
      apply Nnext_intro. rewrite ih. reflexivity.
    }
  Qed.

  (* n = m -> n + k = m + k *)
  Lemma Nplus_intro_r : forall n m k, n = m -> Nplus n k = Nplus m k.
  Proof.
    intros n m k heq. subst m. reflexivity.
  Qed.

  (* n = m -> k + n = k + m *)
  Lemma Nplus_intro_l : forall n m k, n = m -> Nplus k n = Nplus k m.
  Proof.
    intros n m k heq. subst m. reflexivity.
  Qed.

  (* n + k = m + k -> n = m *)
  Lemma Nplus_elim_r : forall n m k, Nplus n k = Nplus m k -> n = m.
  Proof.
    intros n m k.
    generalize dependent m.
    generalize dependent n.
    induction k as [|k ih] using Ninduction.
    (* k = 0 *)
    {
      intros n m heq.
      rewrite Nplus_zero_r in heq.
      rewrite Nplus_zero_r in heq.
      exact heq.
    }
    (* Induction step *)
    {
      intros n m heq.
      rewrite Nplus_next_r in heq.
      rewrite Nplus_next_r in heq.
      apply Nnext_elim in heq.
      apply ih.
      exact heq.
    }
  Qed.

  (* k + n = k + m -> n = m *)
  Lemma Nplus_elim_l : forall n m k, Nplus k n = Nplus k m -> n = m.
  Proof.
    intros n m k heq.
    apply Nplus_elim_r with k.
    rewrite (Nplus_comm n).
    rewrite (Nplus_comm m).
    exact heq.
  Qed.

  (* n + m = n -> m = 0 *)
  Lemma Nplus_elim_zero_l : forall n m, Nplus n m = n -> m = Nzero.
  Proof.
    intros n m heq.
    apply Nplus_elim_l with n.
    rewrite Nplus_zero_r.
    exact heq.
  Qed.

  (* n + m = m -> n = 0 *)
  Lemma Nplus_elim_zero_r : forall n m, Nplus n m = m -> n = Nzero.
  Proof.
    intros n m heq.
    apply Nplus_elim_zero_l with m.
    rewrite Nplus_comm.
    exact heq.
  Qed.

  (* next n = n + 1 *)
  Lemma Nnext_eq : forall n, Nnext n = Nplus n None.
  Proof.
    intro n. unfold None. rewrite Nplus_next_r. rewrite Nplus_zero_r. reflexivity.
  Qed.

  (* If n + m = 0, then n = 0 and m = 0 *)
  Lemma Nplus_zero : forall (n m:NN), Nplus n m = Nzero -> n = Nzero /\ m = Nzero.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    (* n = 0 *)
    {
      (* If n is zero, then m is zero *)
      intros m heq.
      rewrite Nplus_zero_l in heq.
      subst m.
      split;reflexivity.
    }
    (* Induction case *)
    {
      (* Otherwise, we have a contradiction *)
      intros m heq.
      rewrite Nplus_next_l in heq.
      inversion heq.
    }
  Qed.

  (* If n + m = 1, then n = 1 or m = 1 *)
  Lemma Nplus_one : forall (n m:NN), Nplus n m = None -> n = None \/ m = None.
  Proof.
    intro n.
    induction n as [|n _] using Ninduction.
    (* n = 0 *)
    {
      (* then m = 1 *)
      intros m heq.
      rewrite Nplus_zero_l in heq.
      right. exact heq.
    }
    (* n is not zero *)
    {
      intros m heq.
      rewrite Nplus_next_l in heq.
      unfold None in heq.
      apply Nnext_elim in heq.
      (* Then n and m are zero *)
      apply Nplus_zero in heq.
      destruct heq as [heqn heqm].
      subst n m.
      (* which means the original n was one *)
      left.
      fold None.
      reflexivity.
    }
  Qed.

  (* n <= m -> k + n <= k + m *)
  Lemma Nle_plus_intro_l: forall n m k : NN, Nle n m -> Nle (Nplus k n) (Nplus k m).
  Proof.
    intros n m k.
    generalize dependent m.
    generalize dependent n.
    (* k = 0 *)
    induction k as [|k ih] using Ninduction.
    {
      intros n m h.
      rewrite Nplus_zero_l.
      rewrite Nplus_zero_l.
      exact h.
    }
    (* Induction step *)
    {
      intros n m h.
      rewrite Nplus_next_l.
      rewrite Nplus_next_l.
      apply Nle_next_intro.
      apply ih.
      exact h.
    }
  Qed.

  (* n <= m -> n + k <= m + k *)
  Lemma Nle_plus_intro_r: forall n m k : NN, Nle n m -> Nle (Nplus n k) (Nplus m k).
  Proof.
    intros n m k h.
    rewrite (Nplus_comm n).
    rewrite (Nplus_comm m).
    apply Nle_plus_intro_l.
    exact h.
  Qed.

  (* k + n <= k + m -> n <= m *)
  Lemma Nle_plus_elim_l: forall n m k : NN, Nle (Nplus k n) (Nplus k m) -> Nle n m.
  Proof.
    intros n m k.
    generalize dependent m.
    generalize dependent n.
    induction k as [|k ih] using Ninduction.
    (* k = 0 *)
    {
      intros n m h.
      rewrite Nplus_zero_l in h.
      rewrite Nplus_zero_l in h.
      exact h.
    }
    (* Induction step *)
    {
      intros n m h.
      rewrite Nplus_next_l in h.
      rewrite Nplus_next_l in h.
      apply Nle_next_elim in h.
      apply ih.
      exact h.
    }
  Qed.

  (* n + k <= m + k -> n <= m *)
  Lemma Nle_plus_elim_r: forall n m k : NN, Nle (Nplus n k) (Nplus m k) -> Nle n m.
  Proof.
    intros n m k h.
    apply Nle_plus_elim_l with k.
    rewrite (Nplus_comm k).
    rewrite (Nplus_comm k).
    exact h.
  Qed.

  (* n + m <= n -> m = 0 *)
  Lemma Nle_plus_elim_zero_r: forall n m : NN, Nle (Nplus n m) n -> m = Nzero.
  Proof.
    intros n m h.
    rewrite <- Nplus_zero_r in h.
    apply Nle_plus_elim_l in h.
    apply Nle_zero_r in h.
    exact h.
  Qed.

  (* n + m <= m -> n = 0 *)
  Lemma Nle_plus_elim_zero_l: forall n m : NN, Nle (Nplus n m) m -> n = Nzero.
  Proof.
    intros n m h.
    apply Nle_plus_elim_zero_r with m.
    rewrite Nplus_comm.
    exact h.
  Qed.

  (* Next come three lemmas that will be heavily used when constructing the integers *)

  (* n <= m -> there is k such that n + k = m *)
  Lemma Nle_nmk : forall n m, Nle n m -> exists k, Nplus n k = m.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    {
      intros m _.
      exists m.
      rewrite Nplus_zero_l.
      reflexivity.
    }
    {
      intro m.
      induction m as [|m _] using Ninduction.
      { intro h. inversion h. }
      {
        intro h.
        apply Nle_next_elim in h.
        specialize (ih _ h).
        destruct ih as [k ih].
        exists k.
        rewrite Nplus_next_l.
        apply Nnext_intro.
        exact ih.
      }
    }
  Qed.

  (* rest (n + m) m = n *)
  Lemma Nrest_plus_nmm : forall n m, Nrest (Nplus n m) m = n.
  Proof.
    intros n m.
    generalize dependent n.
    induction m as [|m ih] using Ninduction.
    { intro n. rewrite Nplus_zero_r. rewrite Nrest_zero_r. reflexivity. }
    {
      intro n.
      rewrite Nplus_next_r.
      rewrite Nrest_next.
      specialize (ih n).
      exact ih.
    }
  Qed.

  (* min n m <> n -> m <= n *)
  Lemma Nmin_neq_le : forall n m, Nmin n m <> n -> Nle m n.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    { intros m hneq. rewrite Nmin_zero_l in hneq. contradiction hneq. reflexivity. }
    {
      intros m hneq.
      induction m as [|m _] using Ninduction.
      { apply Nle_zero_l. }
      {
        rewrite Nmin_next in hneq.
        apply Nle_next_intro.
        apply ih.
        intro heq.
        apply hneq.
        apply Nnext_intro.
        exact heq.
      }
    }
  Qed.


  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Multiplication                                                               *)
  (*                                                                                  *)
  (* Once we know how to define addition, multiplication is not too difficult.        *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.


  Definition _Nmult_rec : forall x : NN,
    (forall y : NN,(Nlt y x) -> _NRecType y) -> _NRecType x.
  Proof.
    (* left input *)
    intro x.
    (* recursive body for next iteration *)
    intro rec.
    unfold _NRecType.
    (* right input *)
    intro y.
    destruct (Neq_dec Nzero x) as [_|d].
    (* 0 * y = 0 *)
    { apply Nzero. }
    {
      (* we go down by one *)
      specialize (rec (Nrest x None)).
      (* we can do it *)
      apply Nrest_one_lt in d. specialize (rec d). clear d.
      unfold _NRecType in rec.
      (* next iteration will use y too *)
      specialize (rec y).
      (* And we return y + the result of that *)
      apply (Nplus y rec).
    }
  Defined.

  (* This is the obligation that Fix_eq requires everytime we use it *)
  Lemma _Nmult_rec_ok: forall (x : NN)
    (f g : forall y : NN, Nlt y x -> _NRecType y),
    (forall (y : NN) (p : Nlt y x), f y p = g y p)
    -> _Nmult_rec x f = _Nmult_rec x g.
  Proof.
    intros x f g h.
    unfold _Nmult_rec.
    destruct (Neq_dec _) as [_|d].
    { reflexivity. }
    { rewrite h. reflexivity. }
  Qed.

  Definition Nmult := Fix Nlt_wf _ _Nmult_rec.
  Notation "x *n y" := (Nmult x y) (only printing, at level 50) : maths.

  (* And then some classical properties of multiplication *)

  (* 0 * n = 0 *)
  Lemma Nmult_zero_l : forall n, Nmult Nzero n = Nzero.
  Proof.
    intro n.
    unfold Nmult.
    unfold Fix.
    unfold _Nmult_rec.
    simpl.
    reflexivity.
  Qed.

  (* n * 0 = 0 *)
  Lemma Nmult_zero_r : forall n, Nmult n Nzero = Nzero.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    { rewrite Nmult_zero_l. reflexivity. }
    {
      unfold Nmult. rewrite Fix_eq.
      2:{ apply _Nmult_rec_ok. }
      unfold _Nmult_rec.
      destruct (Neq_dec _) as [d|_].
      { inversion d. }
      unfold None at 2. rewrite Nrest_next. rewrite Nrest_zero_r.
      rewrite Nplus_zero_l.
      fold _Nmult_rec. fold Nmult.
      exact ih.
    }
  Qed.

  (* 1 * n = n *)
  Lemma Nmult_one_l : forall n, Nmult None n = n.
  Proof.
    intro n.
    unfold Nmult.
    unfold _Nmult_rec.
    rewrite Fix_eq.
    2:{ apply _Nmult_rec_ok. }
    destruct (Neq_dec _) as [d|_].
    { inversion d. }
    rewrite Nrest_cancel.
    fold _Nmult_rec.
    fold Nmult.
    rewrite Nmult_zero_l.
    rewrite Nplus_zero_r.
    reflexivity.
  Qed.

  (* n * 1 = n *)
  Lemma Nmult_one_r : forall n, Nmult n None = n.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    { rewrite Nmult_zero_l. reflexivity. }
    {
      unfold Nmult. unfold _Nmult_rec.
      rewrite Fix_eq.
      2:{ apply _Nmult_rec_ok. }
      destruct (Neq_dec _) as [d|_].
      { inversion d. }
      unfold None at 3.
      rewrite Nrest_next. rewrite Nrest_zero_r.
      fold _Nmult_rec. fold Nmult.
      rewrite ih.
      rewrite Nplus_comm.
      rewrite <- Nnext_eq.
      reflexivity.
    }
  Qed.

  (* (next n) * m = m + (n * m) *)
  Lemma Nmult_next_l : forall n m, Nmult (Nnext n) m = Nplus m (Nmult n m).
  Proof.
    intros n m.
    generalize dependent n.
    induction m as [|m ih] using Ninduction.
    {
      intro n.
      rewrite Nmult_zero_r.
      rewrite Nmult_zero_r.
      rewrite Nplus_zero_r.
      reflexivity.
    }
    {
      intro n.
      unfold Nmult at 1.
      unfold _Nmult_rec.
      rewrite Fix_eq.
      2:{ apply _Nmult_rec_ok. }
      destruct (Neq_dec _) as [d|_].
      { inversion d. }
      unfold None at 2. rewrite Nrest_next. rewrite Nrest_zero_r.
      fold _Nmult_rec. fold Nmult.
      reflexivity.
    }
  Qed.

  (* n * (next m) = n + n * m *)
  Lemma Nmult_next_r : forall n m, Nmult n (Nnext m) = Nplus n (Nmult n m).
  Proof.
    intros n.
    induction n as [|n ih] using Ninduction.
    {
      intro m.
      rewrite Nmult_zero_l.
      rewrite Nmult_zero_l.
      rewrite Nplus_zero_l.
      reflexivity.
    }
    {
      intro m.
      rewrite Nmult_next_l.
      rewrite Nmult_next_l.
      rewrite Nplus_next_l.
      rewrite Nplus_next_l.
      apply Nnext_intro.
      rewrite ih.
      rewrite (Nplus_comm m).
      repeat rewrite <- Nplus_assoc.
      apply Nplus_intro_l.
      rewrite Nplus_comm.
      reflexivity.
    }
  Qed.

  (* n * m = m * n *)
  Lemma Nmult_comm : forall n m,  Nmult n m = Nmult m n.
  Proof.
    intros n m.
    generalize dependent m.
    induction n as [|n ih] using Ninduction.
    {
      intros.
      rewrite Nmult_zero_l.
      rewrite Nmult_zero_r.
      reflexivity.
    }
    {
      intro m.
      rewrite Nmult_next_l.
      rewrite Nmult_next_r.
      apply Nplus_intro_l.
      rewrite ih.
      reflexivity.
    }
  Qed.

 (* k * (n + m) = k * n + k * m *)
  Lemma Nplus_mult_distr_l : forall n m k, Nmult k (Nplus n m) = Nplus (Nmult k n) (Nmult k m).
  Proof.
    intros n m k.
    generalize dependent m.
    generalize dependent n.
    induction k as [|k ih] using Ninduction.
    {
      intros n m.
      rewrite Nmult_zero_l.
      rewrite Nmult_zero_l.
      rewrite Nmult_zero_l.
      rewrite Nplus_zero_l.
      reflexivity.
    }
    {
      intros n m.
      rewrite Nmult_next_l.
      rewrite Nmult_next_l.
      rewrite Nmult_next_l.
      repeat rewrite <- Nplus_assoc.
      apply Nplus_intro_l.
      symmetry.
      repeat rewrite Nplus_assoc.
      rewrite (Nplus_comm _ m).
      repeat rewrite <- Nplus_assoc.
      apply Nplus_intro_l.
      rewrite ih.
      reflexivity.
    }
  Qed.

  (* (n + m) * k = n * k + m * k *)
  Lemma Nplus_mult_distr_r : forall n m k,
    Nmult  (Nplus n m) k = Nplus (Nmult n k ) (Nmult m k ).
  Proof.
    intros n m k.
    rewrite (Nmult_comm _ k).
    rewrite Nplus_mult_distr_l.
    repeat rewrite (Nmult_comm k).
    reflexivity.
  Qed.

  (* n * (m * k) = (n * m) * k *)
  Lemma Nmult_assoc : forall n m k, Nmult n (Nmult m k) = Nmult (Nmult n m) k.
  Proof.
    intros n m k.
    generalize dependent k.
    generalize dependent m.
    induction n as [|n ih] using Ninduction.
    {
      intros m k.
      rewrite Nmult_zero_l. rewrite Nmult_zero_l. reflexivity.
    }
    {
      intros m k.
      rewrite Nmult_next_l.
      rewrite Nmult_next_l.
      rewrite Nplus_mult_distr_r.
      apply Nplus_intro_l.
      rewrite ih.
      reflexivity.
    }
  Qed.

  (* n * m = 0 -> n = 0 or m = 0 *)
  Lemma Nmult_zero : forall n m, Nmult n m = Nzero -> n = Nzero \/ m = Nzero.
  Proof.
    intro n.
    induction n as [|n _] using Ninduction.
    { intros m heq. left. reflexivity. }
    {
      intros m heq.
      rewrite Nmult_next_l in heq.
      apply Nplus_zero in heq.
      destruct heq as [hl hr].
      right.
      exact hl.
    }
  Qed.

  (* n = m -> n * k = m * k *)
  Lemma Nmult_intro_r: forall n m k, n = m -> Nmult n k = Nmult m k.
  Proof.
    intros n m k heq. subst m. reflexivity.
  Qed.

  (* n = m -> n * k = m * k *)
  Lemma Nmult_intro_l: forall n m k, n = m -> Nmult k n = Nmult k m.
  Proof.
    intros n m k heq. subst m. reflexivity.
  Qed.

  (* n * k = m * k -> n = m *)
  (* This one feels like a small maze. *)
  Lemma Nmult_elim_r: forall n m k : NN, k <> Nzero -> Nmult n k = Nmult m k -> n = m.
  Proof.
    intros n.
    induction n as [|n ih] using Ninduction.
    {
      intros m k hneq heq.
      rewrite Nmult_zero_l in heq.
      symmetry in heq.
      apply Nmult_zero in heq.
      destruct heq as [heq|heq].
      { subst m. reflexivity. }
      { subst k. contradiction hneq. reflexivity. }
    }
    {
      intros m k hneq heq.
      rewrite Nmult_next_l in heq.
      induction m as [|m _] using Ninduction.
      {
        rewrite Nmult_zero_l in heq.
        apply Nplus_zero in heq.
        destruct heq as [hl hr].
        subst k. contradiction hneq. reflexivity.
      }
      {
        apply Nnext_intro.
        apply ih with k.
        { exact hneq. }
        {
          rewrite Nmult_next_l in heq.
          apply Nplus_elim_l in heq.
          exact heq.
        }
      }
    }
  Qed.

  Lemma Nmult_elim_l: forall n m k : NN, k <> Nzero -> Nmult k n = Nmult k m -> n = m.
  Proof.
    intros n m k hneq heq.
    apply Nmult_elim_r with k.
    { exact hneq. }
    {
      rewrite (Nmult_comm n).
      rewrite (Nmult_comm m).
      exact heq.
    }
  Qed.

  (* n * m = 1 -> n = 1 and m = 1 *)
  Lemma Nmult_one: forall (n m : NN), Nmult n m = None -> n = None /\ m = None.
  Proof.
    (* I got lost on this one *)
    (* I start by discarding the case where n = 0 or m = 0 *)
    intros n m heq.
    (* The '_' here discards the induction hypothesis by the way, *)
    (* so it's the same as destruct                               *)
    induction n as [|n _] using Ninduction.
    { rewrite Nmult_zero_l in heq. inversion heq. }
    induction m as [|m _] using Ninduction.
    { rewrite Nmult_zero_r in heq. inversion heq. }
    (* Now we know that n and m are one or greater than one *)
    {
      (* We rewrite whatever we can *)
      rewrite Nmult_next_l in heq.
      rewrite Nmult_next_r in heq.
      (* Now we copy heq so that we can destruct the sum *)
      (* That's the trick: to keep the other equality around *)
      assert (heq':=heq).
      apply Nplus_one in heq'.
      (* And we check both branches *)
      destruct heq' as [heq'|heq'].
      {
        (* We can get a value for m *)
        unfold None in heq'. apply Nnext_elim in heq'. subst m.
        (* Now for a lot of rewriting *)
        rewrite Nmult_zero_r in heq.
        rewrite Nplus_zero_r in heq.
        rewrite Nplus_next_l in heq.
        rewrite Nplus_zero_l in heq.
        (* And we get n = 0 *)
        unfold None in heq. apply Nnext_elim in heq. subst n.
        (* So that's fine *)
        fold None. split. reflexivity. reflexivity.
      }
      {
        (* Another sum, another destruct, same strategy *)
        assert (heq'' := heq').
        apply Nplus_one in heq''.
        destruct heq'' as [heq''|heq''].
        {
          (* Here we show that something is wrong *)
          subst n.
          rewrite Nmult_one_l in heq'.
          apply Nplus_elim_zero_l in heq'.
          subst m.
          rewrite Nmult_zero_r in heq.
          rewrite Nplus_zero_r in heq.
          apply Nplus_elim_zero_l in heq.
          inversion heq.
        }
        {
          (* And here something is wrong too *)
          rewrite heq'' in heq'.
          apply Nplus_elim_zero_r in heq'.
          subst n.
          rewrite Nmult_zero_l in heq''.
          inversion heq''.
        }
      }
    }
  Qed.

  (* n <> 0 and n * m = n -> m = 1 *)
  Lemma Nmult_elim_zero_l: forall (n m : NN), n <> Nzero -> Nmult n m = n -> m = None.
  Proof.
    intros n m hneq heq.
    apply Nmult_elim_l with n.
    { exact hneq. }
    { rewrite Nmult_one_r. exact heq. }
  Qed.

  (* n <> 0 and n * m = n -> m = 1 *)
  Lemma Nmult_elim_zero_r: forall (n m : NN), m <> Nzero -> Nmult n m = m -> n = None.
  Proof.
    intros n m hneq heq.
    apply Nmult_elim_zero_l with m.
    { exact hneq. }
    { rewrite Nmult_comm. exact heq. }
  Qed.

  (* n <= m -> k * n <= k * m *)
  Lemma Nle_mult_intro_l: forall (n m k : NN), Nle n m -> Nle (Nmult k n) (Nmult k m).
  Proof.
    intros n m k.
    generalize dependent m.
    generalize dependent n.
    induction k as [|k ih] using Ninduction.
    {
      intros n m h.
      rewrite Nmult_zero_l.
      rewrite Nmult_zero_l.
      apply Nle_refl.
    }
    {
      intros n m h.
      rewrite Nmult_next_l.
      rewrite Nmult_next_l.
      specialize (ih n m h).
      remember (Nmult k n) as kn.
      remember (Nmult k m) as km.
      apply Nle_trans with (Nplus n km).
      { apply Nle_plus_intro_l. exact ih. }
      { apply Nle_plus_intro_r. exact h. }
    }
  Qed.

  (* n <= m -> n * k <= m * k *)
  Lemma Nle_mult_intro_r: forall (n m k : NN), Nle n m -> Nle (Nmult n k) (Nmult m k).
  Proof.
    intros n m k h.
    rewrite (Nmult_comm n).
    rewrite (Nmult_comm m).
    apply Nle_mult_intro_l.
    exact h.
  Qed.

  (* k <> 0 and k * n <= k * m -> n <= m *)
  Lemma Nle_mult_elim_l: forall (n m k : NN), k <> Nzero ->
    Nle (Nmult k n) (Nmult k m) -> Nle n m.
  Proof.
    intro n.
    induction n as [|n ih] using Ninduction.
    { intros m k hneq hle. apply Nle_zero_l. }
    {
      intros m k hneq hle.
      rewrite Nmult_next_r in hle.
      induction m as [|m _] using Ninduction.
      (* Handle the case m = 0 differently *)
      {
        rewrite Nmult_zero_r in hle.
        apply Nle_zero_r in hle.
        apply Nplus_zero in hle.
        destruct hle as [hl hr].
        subst k.
        contradiction hneq.
      }
      {
        apply Nle_next_intro.
        apply ih with k.
        { exact hneq. }
        {
          apply Nle_plus_elim_l with k.
          rewrite Nmult_next_r in hle.
          exact hle.
        }
      }
    }
  Qed.

  (* k <> 0 and n * k <= m * k -> n <= m *)
  Lemma Nle_mult_elim_r: forall (n m k : NN), k <> Nzero ->
    Nle (Nmult n k) (Nmult m k) -> Nle n m.
  Proof.
    intros n m k hneq hle.
    apply Nle_mult_elim_l with k.
    { exact hneq. }
    { rewrite (Nmult_comm k). rewrite (Nmult_comm k).  exact hle. }
  Qed.

  (************************************************************************************)
  (*                                                                                  *)
  (* >>> Conclusion                                                                   *)
  (*                                                                                  *)
  (* This was a lot, and yet it's a very small fraction of the lemmas and theorems    *)
  (* which can be proven over the natural integers.                                   *)
  (*                                                                                  *)
  (* But we have everything we need to construct the integers and define addition     *)
  (* and multiplication on them, and that will be our next stop.                      *)
  (*                                                                                  *)
  (* Then the plan is to construct the rational from the integers, then the           *)
  (* real numbers from the rationals using Dedekind cuts, then the complex numbers.   *)
  (*                                                                                  *)
  (* But this still has to materialize. As of this writing, only the integers are     *)
  (* almost ready. I fear that the rationals will be a bigger challenge because       *)
  (* multiplication seems more difficult to deal with, so we will see.                *)
  (*                                                                                  *)
  (************************************************************************************)
  Comments.

