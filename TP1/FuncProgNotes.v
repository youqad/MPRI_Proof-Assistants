Fixpoint factorial (n : nat) := 
    match n with
        | 0 => 1
        | S p => n * factorial p
    end.

Inductive nat:Type := 
    | 0: nat
    | S: nat -> nat.

Inductive even nat -> Prop :=
    | even_zero : even 0
    | enven_plus_2 : forall n, even n -> even (S (S n)).

Inductive term :=
    | Var: nat -> term
    | Lam: term -> term
    | App: term -> term -> term.