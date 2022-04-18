
  (* Definition of commutativity for a binary operation over some type T *)
  Definition commutative {T:Type} (f:T->T->T) := forall x y, f x y = f y x.

  (* Definition of associativity for a binary operation over some type T *)
  Definition associative {T:Type} (f:T->T->T) := forall x y z, f (f x y) z = f x (f y z).

  (* Definition of a commutative monoid for a binary operation over some type T *)
  Definition commutative_monoid (T:Type) (op:T->T->T) :=
    associative op /\ commutative op /\
    (exists e, forall a, op e a = a /\ op a e = a).

  Definition reflexive {A:Type} (R:A->A->Prop) := forall x, R x x.
  Definition transitive {A:Type} (R:A->A->Prop) := forall x y z, R x y -> R y z -> R x z.
  Definition symmetric {A:Type} (R:A->A->Prop) := forall x y, R x y -> R y x.
  Definition equivalence {A:Type} (R:A->A->Prop) := reflexive R /\ symmetric R /\ transitive R.
