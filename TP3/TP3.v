Require Import List Arith Omega.


Fixpoint belast (n: nat) (l': list nat): list nat := 
    match l' with
    | nil => nil
    | cons y l => cons n (belast y l)
    end.

Lemma length_belast (x : nat) (s : list nat) : 
    length (belast x s) = length s.
Proof. 
    revert x.
    induction s; intro; try now simpl.
    simpl; now f_equal.
Qed.

Fixpoint skip  (l: list nat): list nat := 
    match l with
    | nil => nil
    | cons _ nil => nil
    | (cons _ (cons n l')) => cons n (skip l')
    end.


Lemma length_skip l : 2 * length (skip l) <= length l.
Proof.
    revert l.
    enough (forall (l l': list nat), length l' <= length l -> 2 * length (skip l') <= length l').
    intro; now apply (H l l).
    induction l; intros.
    -   assert (l' = nil).
        inversion H; now apply length_zero_iff_nil in H1. now subst l'.
    -   do 2 (destruct l'; simpl; auto).
        enough (2*length (skip l') <= length l'). omega.
        apply IHl; simpl in H; omega.
Qed.

Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m:nat, le n m -> le n (S m).

Print le_ind.

Lemma S_mon : forall (n m:nat), (le n m)->(le (S n) (S m)).
Proof.
    intros.
    induction H; now constructor.
Qed.

Goal forall (n:nat), (le O n).
Proof.
    intro. induction n; now constructor.
Qed.

Goal forall (n m p:nat), (le n m)->(le m p)->(le n p).
Proof.
    intros.
    induction H0; auto.
    now constructor.
Qed.


