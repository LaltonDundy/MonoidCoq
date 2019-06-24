Inductive Nat : Set :=
| Z : Nat
| S : Nat -> Nat.

Fixpoint add ( n m : Nat ) : Nat :=
match n with
| Z    => m
| S n' => S ( add n' m )
end.

Theorem add_z_r : forall n : Nat, add n Z = n.
Proof.
    induction n.
    simpl.
    auto.
    simpl.
    rewrite IHn.
    auto.
Qed.

Theorem add_s_r : forall n m: Nat, add n (S m) = S (add n m).
Proof.
    induction n.
    simpl.
    auto.
    simpl.
    intros.
    simpl.
    rewrite IHn.
    auto.
Qed.

Inductive Assoc (A : Type) (f : A -> A -> A) :=
| Assoc_proof : ( forall a b c : A, f ( f a b ) c = f a ( f b c )) -> Assoc A f
.

Inductive ID_Elem (A : Type) (f : A -> A -> A) (id : A) :=
| ID_Elem_proof : (forall a : A, f id a = a) -> ID_Elem A f id
.

Inductive Commute (A : Type) (f : A -> A -> A) :=
| Commute_proof : (forall a b : A , f a b = f b a)  -> Commute A f
.

Inductive SemiGroup (A : Type) (f : A -> A -> A) :=
| SemiGroup_proof : Assoc A f -> Commute A f -> SemiGroup A f
.

Inductive Monoid (A : Type) (f : A -> A -> A) (id : A) :=
| Monoid_proof : SemiGroup A f -> ID_Elem A f id -> Monoid A f id
.

Theorem add_commut : forall n m : Nat, add n m = add m n.
Proof.
    induction n.
    simpl.
    intro m.
    replace (add m Z) with m.
    simpl.
    auto.
    rewrite add_z_r.
    auto.
    simpl.
    intros.
    rewrite add_s_r.
    auto.
    rewrite IHn.
    auto.
Qed.

Theorem add_assoc : forall a b c : Nat , add ( add a b ) c = add a ( add b c).
Proof.
    induction a.
    simpl.
    auto.
    simpl.
    intros.
    rewrite IHa.
    auto.
Qed.

Theorem add_id : forall n : Nat, add Z n = n.
Proof.
    intros.
    simpl.
    auto.
Qed.

Definition add_monoid := Monoid_proof Nat add Z
( SemiGroup_proof Nat add (Assoc_proof Nat add add_assoc) (Commute_proof Nat add add_commut ) )
( ID_Elem_proof Nat add Z add_id ) 
.

Inductive List (A : Type) :=
| Empty : List A  
| Cons  : A -> List A -> List A
.

Fixpoint fold (A : Type) (f : A -> A -> A) (empty : A) (p : Monoid A f empty) (ls : List A) := 
match ls with
| Empty  _        => empty
| Cons _ val rest => f val (fold A f empty p rest)
end .

